use vstd::{
    cell::{self, pcell_maybe_uninit},
    prelude::*,
    resource::Loc,
    resource::ghost_var::{GhostVar, GhostVarAuth},
};
use vstd_extra::{array_ptr, ownership::*};

use crate::specs::{
    arch::*,
    mm::{
        frame::{mapping::*, meta_owners::*, meta_region_owners::MetaRegionOwners},
        page_table::owners::tree_level_for,
    },
};

use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel, Vaddr,
    frame::meta::{META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, mapping::meta_to_frame},
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

/// The PTE of type `E` whose raw value is `r`. Unique, by
/// [`PageTableEntryTrait::lemma_as_usize_injective`].
pub open spec fn raw_decode<E: PageTableEntryTrait>(r: usize) -> E {
    choose|e: E| e.as_usize_spec() == r
}

/// Decoding the raw value of a PTE gives the PTE back.
pub proof fn lemma_raw_decode<E: PageTableEntryTrait>(e: E)
    ensures
        raw_decode::<E>(e.as_usize_spec()) == e,
{
    let d = raw_decode::<E>(e.as_usize_spec());
    assert(d.as_usize_spec() == e.as_usize_spec());
    E::lemma_as_usize_injective(d, e);
}

/// Whether a PTE of type `E`, given by its raw value, is present.
pub open spec fn raw_is_present<E: PageTableEntryTrait>(r: usize) -> bool {
    raw_decode::<E>(r).is_present()
}

/// The child page table node that a PTE of type `E` at `level`, given by its
/// raw value, points to: its physical address if it is present and not last.
pub open spec fn raw_child_of<E: PageTableEntryTrait>(r: usize, level: PagingLevel) -> Option<
    Paddr,
> {
    let e = raw_decode::<E>(r);
    if e.is_present() && !e.is_last(level) {
        Some(e.paddr())
    } else {
        None
    }
}

/// [`raw_child_of`] as a function value, as stored in the lock constant.
pub open spec fn raw_child_of_fn<E: PageTableEntryTrait>() -> spec_fn(usize, PagingLevel) -> Option<
    Paddr,
> {
    |r: usize, lv: PagingLevel| raw_child_of::<E>(r, lv)
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

/// The raw representation of a sequence of PTEs, as recorded by the PTE model.
pub open spec fn pte_raws<E: PageTableEntryTrait>(s: Seq<E>) -> PteRaws {
    s.map_values(|e: E| e.as_usize_spec())
}

/// Counting present PTEs through their raw representation gives the same
/// result as counting them directly.
pub proof fn lemma_count_where_pte_raws<E: PageTableEntryTrait>(s: Seq<E>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        count_where_upto(|r: usize| raw_is_present::<E>(r), pte_raws(s), n) == count_present_upto(
            s,
            n,
        ),
    decreases n,
{
    if n > 0 {
        lemma_count_where_pte_raws(s, n - 1);
        lemma_raw_decode::<E>(s[n - 1]);
    }
}

/// Counting present PTEs among raw values gives the same result as counting
/// the decoded PTEs.
pub proof fn lemma_count_where_raw<E: PageTableEntryTrait>(raw: Seq<usize>, n: int)
    requires
        0 <= n <= raw.len(),
    ensures
        count_where_upto(|r: usize| raw_is_present::<E>(r), raw, n) == count_present_upto(
            raw.map_values(|r: usize| raw_decode::<E>(r)),
            n,
        ),
    decreases n,
{
    if n > 0 {
        lemma_count_where_raw::<E>(raw, n - 1);
    }
}

/// Decoding raw values written as `as_usize` of a PTE gives the PTE back, so
/// updating a raw value updates the decoded sequence.
pub proof fn lemma_decode_update<E: PageTableEntryTrait>(raw: Seq<usize>, i: int, e: E)
    requires
        0 <= i < raw.len(),
    ensures
        raw.update(i, e.as_usize_spec()).map_values(|r: usize| raw_decode::<E>(r))
            == raw.map_values(|r: usize| raw_decode::<E>(r)).update(i, e),
{
    lemma_raw_decode::<E>(e);
    assert(raw.update(i, e.as_usize_spec()).map_values(|r: usize| raw_decode::<E>(r))
        =~= raw.map_values(|r: usize| raw_decode::<E>(r)).update(i, e));
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
            lemma_count_present_upto_unchanged(s, s2, n - 1);
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
)
    requires
        0 <= n,
        forall|k: int| 0 <= k < n ==> s[k] == s2[k],
    ensures
        count_present_upto(s2, n) == count_present_upto(s, n),
    decreases n,
{
    if n > 0 {
        lemma_count_present_upto_unchanged(s, s2, n - 1);
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
/// - `pte_view`, one half of the node's PTE model: the raw values of its PTEs.
///   The authoritative half (`PtLockPayload::pte_auth`) is in the node's lock
///   cell, together with the permission for the PTE array itself and for the
///   node-specific metadata fields `nr_children` and `stray`. The owner never
///   holds the cell: it is in the node's lock, or held by whoever locked the
///   node (see [`Self::holds`]). The PTE model lets specs read the PTEs of a
///   node that is not locked, and lets the lock state that `nr_children`
///   counts the present PTEs without depending on the `PageTableConfig`.
/// - `slot_index` identifies the underlying frame's index in the metadata region
/// - `metadata` and `metadata_id` are identity snapshots, not permissions.
///   The owning Frame or incoming PTE holds this node's counted token.
/// - Each node is a page table with a level between 1 and 4 (on x86); `level` tracks
///   the level of this node.
/// - `tree_level` is the level field of the `ghost_tree::TreeNode` that carries this object.
///   Carried here for convenience, though it can be computed from `level`.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub pte_view: GhostVar<PteRaws>,
    /// Identity snapshots; the incoming PTE or owning Frame holds the token.
    pub ghost metadata: MetadataPerm,
    pub ghost metadata_id: Loc,
    pub ghost tree_level: int,
    pub ghost slot_index: int,
    /// The configuration, which determines how the raw PTEs are decoded.
    pub ghost _config: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.pte_view@.len() == NR_ENTRIES
        &&& 1 <= self.level() <= C::NR_LEVELS
        &&& self.tree_level == tree_level_for::<C>(self.level())
        &&& 0 <= self.slot_index < max_meta_slots()
        &&& FRAME_METADATA_RANGE.start <= index_to_meta(self.slot_index) < FRAME_METADATA_RANGE.end
        &&& index_to_meta(self.slot_index) % META_SLOT_SIZE == 0
        &&& meta_to_frame(index_to_meta(self.slot_index)) < VMALLOC_BASE_VADDR
            - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(index_to_meta(self.slot_index)) < MAX_PADDR
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// The node's PTEs, decoded from the PTE model. The model is always
    /// present, and agrees with the PTE array whenever the lock is held.
    pub open spec fn ptes(self) -> Seq<C::E> {
        self.pte_view@.map_values(|r: usize| raw_decode::<C::E>(r))
    }

    /// The physical address of the node's frame, which is its lock's key.
    pub open spec fn paddr(self) -> Paddr {
        meta_to_frame(index_to_meta(self.slot_index))
    }

    /// `perm` is the permission for this node's PTE array, and its contents
    /// agree with the node's PTE model.
    pub open spec fn is_pte_perm(self, perm: array_ptr::PointsTo<usize, NR_ENTRIES>) -> bool {
        &&& perm.wf()
        &&& perm.is_init_all()
        &&& perm.value() == self.pte_view@
        &&& perm.addr() == paddr_to_vaddr(self.paddr())
    }

    /// `cell` is this node's lock cell, and agrees with the owner: whoever
    /// holds it has locked the node. This is what holding the node's lock
    /// gives, except for `nr_children` counting the present PTEs
    /// ([`Self::count_consistent`]), which is momentarily broken while an
    /// entry is replaced.
    pub open spec fn holds(self, cell: PtLockCell) -> bool {
        &&& cell.lock_const() == self.meta_value().lock.constant()
        &&& cell.value().meta.inv()
        &&& self.meta_value().wf(cell.value().meta)
        &&& cell.value().pte_auth.id() == self.pte_view.id()
        &&& cell.value().pte_auth@ == self.pte_view@
        &&& self.is_pte_perm(cell.value().ptes)
    }

    /// `guards` records this node's lock cell as held: the cell of this
    /// node's lock is held by this thread.
    pub open spec fn held_in(self, guards: super::Guards) -> bool {
        guards.holds(self.slot_vaddr(), self.meta_value().lock.constant())
    }

    /// The node's lock cell, held by this thread and recorded in `guards`,
    /// is the one in `cells`.
    pub proof fn lemma_held_cell(self, guards: super::Guards, cells: Map<usize, PtLockCell>)
        requires
            self.held_in(guards),
            guards.cells_wf(cells),
        ensures
            cells.contains_key(self.slot_vaddr()),
            cells[self.slot_vaddr()].lock_const() == self.meta_value().lock.constant(),
            cells[self.slot_vaddr()].inv_cell(),
    {
        assert(guards.held.dom().contains(self.slot_vaddr()));
    }

    /// `nr_children` in the lock cell counts the present PTEs.
    pub open spec fn count_consistent(self, cell: PtLockCell) -> bool {
        cell.value().meta.nr_children.value() == count_present(self.ptes())
    }

    /// A cell that is ready to be unlocked, and belongs to this node's lock,
    /// agrees with the owner. This is how a holder of the cell (e.g. the
    /// cursor, which keeps cells apart from the page table tree) recovers
    /// [`Self::holds`].
    pub proof fn tracked_lemma_holds(tracked &self, tracked cell: &PtLockCell)
        requires
            self.inv(),
            self.meta_value().lock_wf(),
            self.pte_view.id() == self.meta_value().lock.constant().consts.pte_model_id,
            lock_key_wf(self.meta_value(), self.slot_index),
            cell.inv_cell(),
            cell.lock_const() == self.meta_value().lock.constant(),
        ensures
            self.holds(*cell),
            self.count_consistent(*cell),
    {
        reveal(crate::mm::page_table::PageTablePageMeta::lock_consts_wf);
        reveal(lock_key_wf);
        cell.tracked_borrow_value().pte_auth.agree(&self.pte_view);
        lemma_count_where_raw::<C::E>(self.pte_view@, self.pte_view@.len() as int);
    }

    /// The other direction of [`Self::tracked_lemma_holds`]: a cell that this
    /// node holds, and whose `nr_children` is consistent, is ready to be
    /// unlocked.
    pub proof fn lemma_holds_inv_cell(self, cell: PtLockCell)
        requires
            self.inv(),
            self.meta_value().lock_wf(),
            lock_key_wf(self.meta_value(), self.slot_index),
            self.holds(cell),
            self.count_consistent(cell),
        ensures
            cell.inv_cell(),
    {
        reveal(crate::mm::page_table::PageTablePageMeta::lock_consts_wf);
        reveal(lock_key_wf);
        lemma_count_where_raw::<C::E>(self.pte_view@, self.pte_view@.len() as int);
    }

    /// Updates the PTE model to match the PTE array in `cell`, after the
    /// latter has been written.
    pub proof fn tracked_sync_pte_model(tracked &mut self, tracked cell: &mut PtLockCell)
        requires
            old(cell).value().pte_auth.id() == old(self).pte_view.id(),
        ensures
            final(self).pte_view@ == old(cell).value().ptes.value(),
            final(cell).value().pte_auth@ == final(self).pte_view@,
            final(cell).value().pte_auth.id() == final(self).pte_view.id(),
            final(self).pte_view.id() == old(self).pte_view.id(),
            final(cell).loc() == old(cell).loc(),
            final(cell).level() == old(cell).level(),
            final(cell).value() == (PtLockPayload {
                pte_auth: final(cell).value().pte_auth,
                ..old(cell).value()
            }),
            final(self).metadata == old(self).metadata,
            final(self).metadata_id == old(self).metadata_id,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        let tracked payload = cell.tracked_borrow_mut_value();
        let ghost new_ptes = payload.ptes.value();
        payload.pte_auth.update(&mut self.pte_view, new_ptes);
    }

    /// Relates an actual counted token to this non-owning node identity.
    pub open spec fn matches_permission(self, permission: FracMetadataPerm) -> bool {
        &&& permission.frac() == 1
        &&& permission.id() == self.metadata_id
        &&& permission.resource() == self.metadata
    }

    /// The meta address of this node's slot, computed from `slot_index`.
    pub open spec fn slot_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<PageTablePageMeta<C>>(*regions.slots[self.slot_index], self.metadata)
    }

    pub open spec fn meta_value(self) -> PageTablePageMeta<C> {
        typed_meta_value::<PageTablePageMeta<C>>(self.metadata)
    }

    pub open spec fn level(self) -> PagingLevel {
        self.meta_value().level
    }

    /// Regions-tied invariants that used to live in `NodeOwner::inv()` via
    /// the now-removed `meta_perm` field. Establishes the bridge between
    /// the NodeOwner and the slot perm parked in regions.
    pub open spec fn metaregion_sound_node(self, regions: MetaRegionOwners) -> bool {
        let idx = self.slot_index;
        &&& regions.contains(idx)
        &&& 0 < regions.ref_count(idx) <= REF_COUNT_MAX
        &&& self.metadata_id == regions.slot_owners[idx].metadata_perm.id()
        &&& self.metadata == regions.slot_owners[idx].metadata_perm()
        &&& self.meta_wf(regions)
        &&& self.meta_value().lock_wf()
        &&& self.pte_view.id() == self.meta_value().lock.constant().consts.pte_model_id
        &&& lock_key_wf(
            self.meta_value(),
            self.slot_index,
        )
        // A page-table node's slot is tracked with `PageTable` usage (guaranteed
        // by `PageTableNode::alloc`). This discriminates node slots from
        // data-frame slots (`Frame`) by `usage` alone, so a
        // freshly-allocated node (whose slot was `UNUSED`) can't collide with an
        // existing live node — giving `alloc_if_none`/`split` the parent≠child
        // slot distinctness without a PointsTo-linearity axiom.
        &&& regions.slot_owners[self.slot_index].usage is PageTable
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// If a slot in `children_perm` holds a non-present PTE, then
    /// `nr_children < NR_ENTRIES`. Proven (no longer axiomatized) from the
    /// `count_consistent` invariant: `nr_children` counts present PTEs, and an
    /// absent slot means not all `NR_ENTRIES` slots are present.
    pub proof fn lemma_nr_children_absent_slot_bound(self, cell: PtLockCell, idx: usize)
        requires
            self.inv(),
            self.count_consistent(cell),
            self.ptes().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            !self.ptes()[idx as int].is_present(),
        ensures
            cell.value().meta.nr_children.value() < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.ptes(), NR_ENTRIES as int, idx as int);
    }

    /// If a slot in `children_perm` holds a present PTE, then `nr_children > 0`.
    /// Dual of [`Self::lemma_nr_children_absent_slot_bound`]; proven from
    /// `count_consistent`.
    pub proof fn nr_children_present_slot_bound(self, cell: PtLockCell, idx: usize)
        requires
            self.inv(),
            self.count_consistent(cell),
            self.ptes().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            self.ptes()[idx as int].is_present(),
        ensures
            cell.value().meta.nr_children.value() > 0,
    {
        lemma_count_present_upto_present(self.ptes(), NR_ENTRIES as int, idx as int);
    }
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {
    pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
        &&& guard.inner@.wf(self)
        &&& guard.inner.external_meta_wf(self.metadata)
        &&& guard.inner@.tracked_metadata_perm@ matches Some(permission) ==> {
            &&& guard.inner.inv()
            &&& self.matches_permission(permission)
        }
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.slot_vaddr() == owner.slot_vaddr()
        &&& self.ptr_inv()
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn invariants(self, owner: NodeOwner<C>) -> bool {
        &&& owner.inv()
        &&& self.wf(owner)
    }
}

} // verus!
