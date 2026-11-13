use vstd::prelude::*;

use vstd::{
    cell::{self, pcell_maybe_uninit},
    resource::ghost_var::{GhostVar, GhostVarAuth},
    simple_pptr::*,
};
use vstd_extra::{array_ptr, ownership::*};

use crate::specs::{
    arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS},
    mm::{
        frame::{
            mapping::{index_to_meta, max_meta_slots, meta_to_index},
            meta_owners::*,
            meta_region_owners::MetaRegionOwners,
        },
        page_table::owners::INC_LEVELS,
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel, Vaddr,
    frame::meta::{META_SLOT_SIZE, MetaSlot, mapping::meta_to_frame},
    kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
    paddr_to_vaddr,
    page_table::{PageTableGuard, *},
};

verus! {

// ─── Present-PTE counting ──────────────────────────────────────────────────────
// The intended meaning of `nr_children`: the number of *present* PTEs in the
// node's `children_perm` array. `metaregion_sound_node` ties `nr_children` to
// `count_present(children_perm.value())` (a settled-node invariant), which lets
// the `nr_children_*_slot_bound` boundary facts be proven rather than axiomatized.
/// Number of present PTEs among the first `n` entries of `s`.
pub open spec fn count_present_upto<E: PageTableEntryTrait>(s: Seq<E>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_present_upto(s, n - 1) + if s[n - 1].is_present() {
            1int
        } else {
            0int
        }
    }
}

/// Number of present PTEs in `s`.
pub open spec fn count_present<E: PageTableEntryTrait>(s: Seq<E>) -> int {
    count_present_upto(s, s.len() as int)
}

/// A sequence of absent PTEs has no present entries.
pub proof fn lemma_count_present_upto_all_absent<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> !(#[trigger] s[i]).is_present(),
    ensures
        count_present_upto(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_all_absent(s, n - 1);
    }
}

/// Whether a PTE of type `E`, given by its bytes, is present.
pub open spec fn raw_is_present<E: PageTableEntryTrait>(b: Seq<u8>) -> bool {
    ostd_pod::decode_pod::<E>(b).is_present()
}

/// The child page table node that a PTE of type `E` at `level`, given by its
/// bytes, points to: its physical address if it is present and not last.
pub open spec fn raw_child_of<E: PageTableEntryTrait>(b: Seq<u8>, level: PagingLevel) -> Option<
    Paddr,
> {
    let e = ostd_pod::decode_pod::<E>(b);
    if e.is_present() && !e.is_last(level) {
        Some(e.paddr())
    } else {
        None
    }
}

/// [`raw_child_of`] as a function value, as stored in the lock constant.
pub open spec fn raw_child_of_fn<E: PageTableEntryTrait>() -> spec_fn(Seq<u8>, PagingLevel) -> Option<Paddr> {
    |b: Seq<u8>, lv: PagingLevel| raw_child_of::<E>(b, lv)
}

/// The key of a node's lock is the physical address of the node's frame, the
/// one whose metadata slot is `slot_index`. Opaque to keep the address
/// arithmetic out of [`NodeOwner::metaregion_sound_node`] users' contexts.
#[verifier::opaque]
pub open spec fn lock_key_wf<C: PageTableConfig>(
    meta: PageTablePageMeta<C>,
    slot_index: int,
) -> bool {
    meta.lock.constant().key == meta_to_frame(index_to_meta(slot_index))
}

/// The byte representation of a sequence of PTEs, as recorded by the PTE model.
pub open spec fn pte_bytes<E: PageTableEntryTrait>(s: Seq<E>) -> PteBytes {
    s.map_values(|e: E| ostd_pod::pod_bytes(e))
}

/// Counting present PTEs through their byte representation gives the same
/// result as counting them directly.
pub proof fn lemma_count_where_pte_bytes<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        count_where_upto(|b: Seq<u8>| raw_is_present::<E>(b), pte_bytes(s), n)
            == count_present_upto(s, n),
    decreases n,
{
    if n > 0 {
        lemma_count_where_pte_bytes(s, n - 1);
        ostd_pod::lemma_decode_pod_inverse::<E>(s[n - 1]);
    }
}

/// `count_present_upto` is between `0` and `n`.
pub proof fn lemma_count_present_upto_bound<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        0 <= n,
    ensures
        0 <= count_present_upto(s, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_bound(s, n - 1);
    }
}

/// An absent slot below `n` makes the count strictly less than `n`.
pub proof fn lemma_count_present_upto_absent<E: PageTableEntryTrait>(s: Seq<E>, n: int, idx: int)
    requires
        0 <= idx < n,
        !s[idx].is_present(),
    ensures
        count_present_upto(s, n) < n,
    decreases n,
{
    lemma_count_present_upto_bound(s, n - 1);
    if idx < n - 1 {
        lemma_count_present_upto_absent(s, n - 1, idx);
    }
}

/// A present slot below `n` makes the count at least `1`.
pub proof fn lemma_count_present_upto_present<E: PageTableEntryTrait>(s: Seq<E>, n: int, idx: int)
    requires
        0 <= idx < n,
        s[idx].is_present(),
    ensures
        count_present_upto(s, n) >= 1,
    decreases n,
{
    lemma_count_present_upto_bound(s, n - 1);
    if idx < n - 1 {
        lemma_count_present_upto_present(s, n - 1, idx);
    }
}

/// Updating slot `idx` (with `idx < n`) shifts the count by the change in that
/// slot's present-indicator.
pub proof fn lemma_count_present_upto_update<E: PageTableEntryTrait>(
    s: Seq<E>,
    n: int,
    idx: int,
    pte: E,
)
    requires
        0 <= idx < n <= s.len(),
    ensures
        count_present_upto(s.update(idx, pte), n) == count_present_upto(s, n) - (
        if s[idx].is_present() {
            1int
        } else {
            0int
        }) + (if pte.is_present() {
            1int
        } else {
            0int
        }),
    decreases n,
{
    let s2 = s.update(idx, pte);
    if n - 1 == idx {
        // The first `idx` entries are unchanged.
        assert(count_present_upto(s2, n - 1) == count_present_upto(s, n - 1)) by {
            lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
        }
    } else {
        lemma_count_present_upto_update(s, n - 1, idx, pte);
    }
}

/// A zero present-count up to `n` means every slot below `n` is absent.
pub proof fn lemma_count_present_upto_zero_all_absent<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        count_present_upto(s, n) == 0,
        0 <= n,
    ensures
        forall|k: int| 0 <= k < n ==> !#[trigger] s[k].is_present(),
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_bound(s, n - 1);
        lemma_count_present_upto_zero_all_absent(s, n - 1);
    }
}

/// If two sequences agree on `[0, n)`, their counts up to `n` are equal.
pub proof fn lemma_count_present_upto_unchanged<E: PageTableEntryTrait>(
    s: Seq<E>,
    s2: Seq<E>,
    n: int,
    idx: int,
)
    requires
        0 <= n <= idx,
        forall|k: int| 0 <= k < n ==> s[k] == s2[k],
    ensures
        count_present_upto(s2, n) == count_present_upto(s, n),
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
    }
}

pub tracked struct PageMetaOwner {
    pub nr_children: pcell_maybe_uninit::PointsTo<u16>,
    pub stray: pcell_maybe_uninit::PointsTo<bool>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children.is_init()
        &&& 0 <= self.nr_children.value() <= NR_ENTRIES
        &&& self.stray.is_init()
    }
}

pub ghost struct PageMetaModel {
    pub nr_children: u16,
    pub stray: bool,
}

impl Inv for PageMetaModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(&self) -> <Self as View>::V {
        PageMetaModel { nr_children: self.nr_children.value(), stray: self.stray.value() }
    }
}

impl InvView for PageMetaOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children.id()
        &&& self.stray.id() == owner.stray.id()
        &&& 0 <= owner.nr_children.value() <= NR_ENTRIES
    }
}

/// # Verification Design
/// The owner type for a page table node. It contains:
/// - `meta_own`, a `PageMetaOwner`, which holds the permissions for node-specific
///   metadata fields, `nr_children` and `stray`. It is `Some` exactly when this
///   thread holds the node's lock; otherwise the permissions are stored in the lock
///   (see [`PtLockPayload`]).
/// - `pte_auth`, the authoritative half of the PTE model. Like `meta_own`, it
///   travels between the lock and the owner.
/// - `pte_view`, the other half of the PTE model, which always stays with the
///   owner. It records the bytes of the PTEs in `children_perm`; agreement with
///   `pte_auth` is what lets the lock state that `nr_children` counts the
///   present PTEs without depending on the `PageTableConfig`.
/// - `children_perm` is an array permission for the underlying frame in which the node
///   is allocated, interpreted as an array of `NR_ENTRIES` page table entries
/// - `slot_index` identifies the underlying frame's index in the metadata region
/// - Each node is a page table with a level between 1 and 4 (on x86); `level` tracks
///   the level of this node.
/// - `tree_level` is the level field of the `ghost_tree::TreeNode` that carries this object.
///   Carried here for convenience, though it can be computed from `level`.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: Option<PageMetaOwner>,
    pub pte_auth: Option<GhostVarAuth<PteBytes>>,
    pub pte_view: GhostVar<PteBytes>,
    pub children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
    pub ghost level: PagingLevel,
    pub ghost tree_level: int,
    pub ghost slot_index: int,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& (self.meta_own is Some <==> self.pte_auth is Some)
        &&& self.is_locked() ==> {
            &&& self.meta().inv()
            &&& self.pte_auth->Some_0.id() == self.pte_view.id()
            &&& self.pte_auth->Some_0@ == self.pte_view@
        }
        &&& self.pte_view@ == pte_bytes(self.children_perm.value())
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.children_perm.wf()
        &&& self.children_perm.is_init_all()
        &&& self.children_perm.addr() == paddr_to_vaddr(
            meta_to_frame(index_to_meta(self.slot_index)),
        )
        &&& self.tree_level == INC_LEVELS - self.level - 1
        &&& 0 <= self.slot_index < max_meta_slots()
        &&& FRAME_METADATA_RANGE.start <= index_to_meta(self.slot_index) < FRAME_METADATA_RANGE.end
        &&& index_to_meta(self.slot_index) % META_SLOT_SIZE == 0
        &&& meta_to_frame(index_to_meta(self.slot_index)) < VMALLOC_BASE_VADDR
            - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(index_to_meta(self.slot_index)) < MAX_PADDR
        &&& meta_to_frame(index_to_meta(self.slot_index)) == self.children_perm.addr()
        &&& self.slot_index == meta_to_index(index_to_meta(self.slot_index))
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// Whether this thread holds the node's lock, i.e., whether the lock's
    /// payload has been moved into this owner.
    pub open spec fn is_locked(self) -> bool {
        self.meta_own is Some
    }

    /// The metadata permissions. Only meaningful if [`Self::is_locked`].
    pub open spec fn meta(self) -> PageMetaOwner {
        self.meta_own->Some_0
    }

    /// Borrows the metadata permissions of a locked node.
    pub proof fn tracked_borrow_meta(tracked &self) -> (tracked res: &PageMetaOwner)
        requires
            self.is_locked(),
        ensures
            *res == self.meta(),
    {
        self.meta_own.tracked_borrow()
    }

    /// Moves the payload obtained by acquiring the node's lock into this owner.
    pub proof fn tracked_install_lock_payload(tracked &mut self, tracked payload: PtLockPayload)
        requires
            old(self).inv(),
            !old(self).is_locked(),
            payload.meta.inv(),
            payload.pte_auth.id() == old(self).pte_view.id(),
            payload.pte_auth@ == old(self).pte_view@,
        ensures
            final(self).inv(),
            final(self).is_locked(),
            final(self).meta() == payload.meta,
            final(self).pte_view == old(self).pte_view,
            final(self).children_perm == old(self).children_perm,
            final(self).level == old(self).level,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        let tracked PtLockPayload { meta, pte_auth, .. } = payload;
        self.meta_own = Some(meta);
        self.pte_auth = Some(pte_auth);
    }

    /// Updates the PTE model of a locked node to match its `children_perm`, after
    /// the latter has been written.
    pub proof fn tracked_sync_pte_model(tracked &mut self)
        requires
            old(self).is_locked(),
            old(self).pte_auth is Some,
            old(self).pte_auth->Some_0.id() == old(self).pte_view.id(),
        ensures
            final(self).pte_view@ == pte_bytes(old(self).children_perm.value()),
            final(self).pte_auth->Some_0@ == final(self).pte_view@,
            final(self).pte_auth->Some_0.id() == final(self).pte_view.id(),
            final(self).pte_view.id() == old(self).pte_view.id(),
            final(self).meta_own == old(self).meta_own,
            final(self).pte_auth is Some,
            final(self).children_perm == old(self).children_perm,
            final(self).level == old(self).level,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        let tracked mut auth = self.pte_auth.tracked_take();
        auth.update(&mut self.pte_view, pte_bytes(self.children_perm.value()));
        self.pte_auth = Some(auth);
    }

    /// The meta address of this node's slot, computed from `slot_index`.
    pub open spec fn meta_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<PageTablePageMeta<C>>(
            *regions.slots[self.slot_index],
            regions.slot_owners[self.slot_index].metadata_perm,
            (),
        )
    }

    pub open spec fn meta_value(self, regions: MetaRegionOwners) -> PageTablePageMeta<C> {
        typed_meta_value::<PageTablePageMeta<C>>(
            regions.slot_owners[self.slot_index].metadata_perm,
            (),
        )
    }

    /// Regions-tied invariants that used to live in `NodeOwner::inv()` via
    /// the now-removed `meta_perm` field. Establishes the bridge between
    /// the NodeOwner and the slot perm parked in regions.
    pub open spec fn metaregion_sound_node(self, regions: MetaRegionOwners) -> bool {
        let idx = self.slot_index;
        &&& regions.contains(idx)
        &&& self.meta_wf(regions)
        &&& self.meta_value(regions).lock_wf()
        &&& self.pte_view.id() == self.meta_value(regions).lock.constant().consts.pte_model_id
        &&& lock_key_wf(self.meta_value(regions), self.slot_index)
        &&& self.is_locked() ==> self.meta_value(regions).wf(self.meta())
        &&& self.level == self.meta_value(regions).level
        // A page-table node's slot is tracked with `PageTable` usage (set at
        // allocation via `get_node_from_unused_spec`). This discriminates node
        // slots from data-frame slots (`Frame`/MMIO) by `usage` alone, so a
        // freshly-allocated node (whose slot was `UNUSED`) can't collide with an
        // existing live node — giving `alloc_if_none`/`split` the parent≠child
        // slot distinctness without a PointsTo-linearity axiom.
        &&& regions.slot_owners[self.slot_index].usage is PageTable
        // `nr_children` counts the present PTEs in `children_perm`. A settled-node
        // invariant (it is momentarily broken mid-`replace`/`alloc_if_none`, between
        // the PTE write and the counter update, which is why it lives here rather
        // than in `inv()`). Lets `nr_children_*_slot_bound` be proven, not axiomatized.
        &&& self.count_consistent()
    }

    /// If the node is locked, `nr_children` equals the number of present PTEs in
    /// `children_perm`. Held by a settled node (see `metaregion_sound_node`'s use
    /// site). For an unlocked node the fact is kept by the lock instead.
    pub open spec fn count_consistent(self) -> bool {
        self.is_locked() ==> self.meta().nr_children.value() == count_present(
            self.children_perm.value(),
        )
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// If a slot in `children_perm` holds a non-present PTE, then
    /// `nr_children < NR_ENTRIES`. Proven (no longer axiomatized) from the
    /// `count_consistent` invariant: `nr_children` counts present PTEs, and an
    /// absent slot means not all `NR_ENTRIES` slots are present.
    pub proof fn nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.is_locked(),
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            !self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta().nr_children.value() < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }

    /// If a slot in `children_perm` holds a present PTE, then `nr_children > 0`.
    /// Dual of [`Self::nr_children_absent_slot_bound`]; proven from
    /// `count_consistent`.
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.is_locked(),
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta().nr_children.value() > 0,
    {
        lemma_count_present_upto_present(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {
    pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
        &&& guard.inner.inner@.ptr.addr() == self.meta_vaddr()
        &&& guard.inner.inner@.wf(self)
    }
}

pub ghost struct NodeModel<C: PageTableConfig> {
    pub level: PagingLevel,
    pub _phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> Inv for NodeModel<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> View for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(&self) -> <Self as View>::V {
        NodeModel { level: self.level, _phantom: core::marker::PhantomData }
    }
}

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_vaddr()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn invariants(self, owner: NodeOwner<C>) -> bool {
        &&& owner.inv()
        &&& self.wf(
            owner,
        )
        //        &&& owner.meta_perm.wf(owner.meta_perm.storage_perm())
        //        &&& owner.meta_perm.addr() == self.ptr.addr()
        //        &&& owner.meta_perm.addr() == self.ptr.addr()

    }
}

} // verus!
