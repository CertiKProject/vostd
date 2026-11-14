use vstd::{
    cell::{self, pcell_maybe_uninit},
    prelude::*,
    resource::ghost_var::{GhostVar, GhostVarAuth},
    simple_pptr::*,
};
use vstd_extra::{array_ptr, ownership::*};

use crate::specs::{
    arch::*,
    mm::{
        frame::{mapping::*, meta_owners::*, meta_region_owners::MetaRegionOwners},
        page_table::owners::INC_LEVELS,
    },
};

use crate::arch::mm::PagingConsts;
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
pub open spec fn raw_child_of_fn<E: PageTableEntryTrait>() -> spec_fn(usize, PagingLevel) -> Option<Paddr> {
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
        count_where_upto(|r: usize| raw_is_present::<E>(r), pte_raws(s), n)
            == count_present_upto(s, n),
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
/// - `lock_cell`, the node's [`PtLockCell`]. It is `Some` exactly when this
///   thread holds the node's lock; otherwise the cell is stored in the lock. Its
///   [`PtLockPayload`] holds the permissions for the node-specific metadata
///   fields `nr_children` and `stray` (see [`Self::meta`]) and the
///   authoritative half of the PTE model (see [`Self::pte_auth`]).
/// - `pte_view`, the other half of the PTE model, which always stays with the
///   owner. It records the bytes of the PTEs in `children_perm`; agreement with
///   `pte_auth` is what lets the lock state that `nr_children` counts the
///   present PTEs without depending on the `PageTableConfig`.
/// - `children_perm` is an array permission for the underlying frame in which the node
///   is allocated, as `NR_ENTRIES` raw PTE values (`PageTableEntryTrait::as_usize`).
///   The raw type keeps it independent of the `PageTableConfig`, so that it can be
///   held by the node's lock. [`Self::ptes`] decodes it.
/// - `slot_index` identifies the underlying frame's index in the metadata region
/// - Each node is a page table with a level between 1 and 4 (on x86); `level` tracks
///   the level of this node.
/// - `tree_level` is the level field of the `ghost_tree::TreeNode` that carries this object.
///   Carried here for convenience, though it can be computed from `level`.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub lock_cell: Option<PtLockCell>,
    pub pte_view: GhostVar<PteRaws>,
    pub frame_permission: FracMetadataPerm,
    pub ghost tree_level: int,
    pub ghost slot_index: int,
    /// The configuration, which determines how the raw PTEs are decoded.
    pub ghost _config: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.is_locked() ==> {
            &&& self.meta().inv()
            &&& self.pte_auth().id() == self.pte_view.id()
            &&& self.pte_auth()@ == self.pte_view@
            &&& self.perm().wf()
            &&& self.perm().is_init_all()
            &&& self.perm().value() == self.pte_view@
            &&& self.perm().addr() == paddr_to_vaddr(meta_to_frame(index_to_meta(self.slot_index)))
        }
        &&& self.pte_view@.len() == NR_ENTRIES
        &&& self.frame_permission.frac() == 1
        &&& 1 <= self.level() <= NR_LEVELS
        &&& self.tree_level == INC_LEVELS - self.level() - 1
        &&& 0 <= self.slot_index < max_meta_slots()
        &&& FRAME_METADATA_RANGE.start <= index_to_meta(self.slot_index) < FRAME_METADATA_RANGE.end
        &&& index_to_meta(self.slot_index) % META_SLOT_SIZE == 0
        &&& meta_to_frame(index_to_meta(self.slot_index)) < VMALLOC_BASE_VADDR
            - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(index_to_meta(self.slot_index)) < MAX_PADDR
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// Whether this thread holds the node's lock, i.e., whether the lock's
    /// cell has been moved into this owner.
    pub open spec fn is_locked(self) -> bool {
        self.lock_cell is Some
    }

    /// The node's PTEs, decoded from the PTE model. The model is always
    /// present, and agrees with the PTE array whenever the lock is held.
    pub open spec fn ptes(self) -> Seq<C::E> {
        self.pte_view@.map_values(|r: usize| raw_decode::<C::E>(r))
    }

    /// The permission for the node's PTE array. Only meaningful if
    /// [`Self::is_locked`]: the permission travels with the lock cell.
    pub open spec fn perm(self) -> array_ptr::PointsTo<usize, NR_ENTRIES> {
        self.cell().value().ptes
    }

    /// `perm` is the permission for this node's PTE array, and its contents
    /// agree with the node's PTE model. The node's own lock cell holds one when
    /// [`Self::is_locked`]; a lock cell held elsewhere can provide one too.
    pub open spec fn is_pte_perm(self, perm: array_ptr::PointsTo<usize, NR_ENTRIES>) -> bool {
        &&& perm.wf()
        &&& perm.is_init_all()
        &&& perm.value() == self.pte_view@
        &&& perm.addr() == paddr_to_vaddr(meta_to_frame(index_to_meta(self.slot_index)))
    }

    /// Borrows the PTE array permission of a locked node.
    pub proof fn tracked_borrow_perm(tracked &self) -> (tracked res: &array_ptr::PointsTo<
        usize,
        NR_ENTRIES,
    >)
        requires
            self.is_locked(),
        ensures
            *res == self.perm(),
    {
        &self.lock_cell.tracked_borrow().tracked_borrow_value().ptes
    }

    /// Mutably borrows the PTE array permission inside a held lock cell, given
    /// only the owner's `lock_cell` field.
    pub proof fn tracked_cell_perm_mut(tracked cell: &mut Option<PtLockCell>) -> (tracked res:
        &mut array_ptr::PointsTo<usize, NR_ENTRIES>)
        requires
            (*old(cell)) is Some,
        ensures
            *res == (*old(cell))->Some_0.value().ptes,
            (*final(cell)) is Some,
            (*final(cell))->Some_0.loc() == (*old(cell))->Some_0.loc(),
            (*final(cell))->Some_0.level() == (*old(cell))->Some_0.level(),
            (*final(cell))->Some_0.value() == (PtLockPayload {
                ptes: *final(res),
                ..(*old(cell))->Some_0.value()
            }),
    {
        match cell {
            Some(c) => &mut c.tracked_borrow_mut_value().ptes,
            None => proof_from_false(),
        }
    }

    /// The lock cell. Only meaningful if [`Self::is_locked`].
    pub open spec fn cell(self) -> PtLockCell {
        self.lock_cell->Some_0
    }

    /// The metadata permissions. Only meaningful if [`Self::is_locked`].
    pub open spec fn meta(self) -> PageMetaOwner {
        self.cell().value().meta
    }

    /// The authoritative half of the PTE model. Only meaningful if
    /// [`Self::is_locked`].
    pub open spec fn pte_auth(self) -> GhostVarAuth<PteRaws> {
        self.cell().value().pte_auth
    }

    /// Borrows the metadata permissions of a locked node.
    pub proof fn tracked_borrow_meta(tracked &self) -> (tracked res: &PageMetaOwner)
        requires
            self.is_locked(),
        ensures
            *res == self.meta(),
    {
        &self.lock_cell.tracked_borrow().tracked_borrow_value().meta
    }

    /// Mutably borrows the metadata permissions of a locked node. Everything
    /// else in the owner, including the rest of the cell, is unchanged.
    pub proof fn tracked_borrow_mut_meta(tracked &mut self) -> (tracked res: &mut PageMetaOwner)
        requires
            old(self).is_locked(),
        ensures
            *res == old(self).meta(),
            final(self).is_locked(),
            final(self).meta() == *final(res),
            final(self).cell().loc() == old(self).cell().loc(),
            final(self).cell().level() == old(self).cell().level(),
            final(self).cell().value() == (PtLockPayload {
                meta: *final(res),
                ..old(self).cell().value()
            }),
            final(self).pte_view == old(self).pte_view,
            final(self).frame_permission == old(self).frame_permission,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        match self.lock_cell {
            Some(ref mut cell) => &mut cell.tracked_borrow_mut_value().meta,
            None => proof_from_false(),
        }
    }

    /// Mutably borrows the metadata permissions inside a held lock cell, given
    /// only the owner's `lock_cell` field, so that other fields of the owner
    /// (e.g. `frame_permission`) can stay borrowed meanwhile.
    pub proof fn tracked_cell_meta_mut(tracked cell: &mut Option<PtLockCell>) -> (tracked res:
        &mut PageMetaOwner)
        requires
            (*old(cell)) is Some,
        ensures
            *res == (*old(cell))->Some_0.value().meta,
            (*final(cell)) is Some,
            (*final(cell))->Some_0.loc() == (*old(cell))->Some_0.loc(),
            (*final(cell))->Some_0.level() == (*old(cell))->Some_0.level(),
            (*final(cell))->Some_0.value() == (PtLockPayload {
                meta: *final(res),
                ..(*old(cell))->Some_0.value()
            }),
    {
        match cell {
            Some(c) => &mut c.tracked_borrow_mut_value().meta,
            None => proof_from_false(),
        }
    }

    /// Moves the cell obtained by acquiring the node's lock into this owner.
    pub proof fn tracked_install_lock_cell(tracked &mut self, tracked cell: PtLockCell)
        requires
            old(self).inv(),
            !old(self).is_locked(),
            cell.inv_cell(),
            cell.key() == meta_to_frame(index_to_meta(old(self).slot_index)),
            cell.value().pte_auth.id() == old(self).pte_view.id(),
            cell.value().pte_auth@ == old(self).pte_view@,
        ensures
            final(self).inv(),
            final(self).is_locked(),
            final(self).cell() == cell,
            final(self).pte_view == old(self).pte_view,
            final(self).frame_permission == old(self).frame_permission,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        self.lock_cell = Some(cell);
    }

    /// Updates the PTE model of a locked node to match its `children_perm`, after
    /// the latter has been written.
    pub proof fn tracked_sync_pte_model(tracked &mut self)
        requires
            old(self).is_locked(),
            old(self).pte_auth().id() == old(self).pte_view.id(),
        ensures
            final(self).pte_view@ == old(self).perm().value(),
            final(self).pte_auth()@ == final(self).pte_view@,
            final(self).pte_auth().id() == final(self).pte_view.id(),
            final(self).pte_view.id() == old(self).pte_view.id(),
            final(self).is_locked(),
            final(self).meta() == old(self).meta(),
            final(self).cell().lock_const() == old(self).cell().lock_const(),
            final(self).cell().loc() == old(self).cell().loc(),
            final(self).cell().level() == old(self).cell().level(),
            final(self).cell().value() == (PtLockPayload {
                pte_auth: final(self).pte_auth(),
                ..old(self).cell().value()
            }),
            final(self).frame_permission == old(self).frame_permission,
            final(self).tree_level == old(self).tree_level,
            final(self).slot_index == old(self).slot_index,
    {
        let tracked mut cell = self.lock_cell.tracked_take();
        let tracked payload = cell.tracked_borrow_mut_value();
        let ghost new_ptes = payload.ptes.value();
        payload.pte_auth.update(&mut self.pte_view, new_ptes);
        self.lock_cell = Some(cell);
    }

    pub proof fn tracked_borrow_frame_metadata_perm(
        tracked permission: &FracMetadataPerm,
    ) -> (tracked res: &MetadataPerm)
        ensures
            *res == permission.resource(),
    {
        permission.tracked_borrow()
    }

    pub proof fn tracked_borrow_metadata_perm(tracked &self) -> tracked &MetadataPerm
        returns
            self.frame_permission.resource(),
    {
        self.frame_permission.tracked_borrow()
    }

    /// The meta address of this node's slot, computed from `slot_index`.
    pub open spec fn slot_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<PageTablePageMeta<C>>(
            *regions.slots[self.slot_index],
            self.frame_permission.resource(),
            (),
        )
    }

    pub open spec fn meta_value(self) -> PageTablePageMeta<C> {
        typed_meta_value::<PageTablePageMeta<C>>(self.frame_permission.resource(), ())
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
        &&& self.frame_permission.id() == regions.slot_owners[idx].metadata_perm.id()
        &&& self.meta_wf(regions)
        &&& self.meta_value().lock_wf()
        &&& self.pte_view.id() == self.meta_value().lock.constant().consts.pte_model_id
        &&& lock_key_wf(self.meta_value(), self.slot_index)
        &&& self.is_locked() ==> self.meta_value().wf(self.meta())
        &&& self.is_locked() ==> self.cell().lock_const() == self.meta_value().lock.constant()
        // A page-table node's slot is tracked with `PageTable` usage (guaranteed
        // by `PageTableNode::alloc`). This discriminates node slots from
        // data-frame slots (`Frame`) by `usage` alone, so a
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
            self.ptes(),
        )
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// If a slot in `children_perm` holds a non-present PTE, then
    /// `nr_children < NR_ENTRIES`. Proven (no longer axiomatized) from the
    /// `count_consistent` invariant: `nr_children` counts present PTEs, and an
    /// absent slot means not all `NR_ENTRIES` slots are present.
    pub proof fn lemma_nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.is_locked(),
            self.count_consistent(),
            self.ptes().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            !self.ptes()[idx as int].is_present(),
        ensures
            self.meta().nr_children.value() < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.ptes(), NR_ENTRIES as int, idx as int);
    }

    /// If a slot in `children_perm` holds a present PTE, then `nr_children > 0`.
    /// Dual of [`Self::lemma_nr_children_absent_slot_bound`]; proven from
    /// `count_consistent`.
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.is_locked(),
            self.count_consistent(),
            self.ptes().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            self.ptes()[idx as int].is_present(),
        ensures
            self.meta().nr_children.value() > 0,
    {
        lemma_count_present_upto_present(self.ptes(), NR_ENTRIES as int, idx as int);
    }
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {
    pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
        &&& guard.inner.inner@.wf(self)
        &&& guard.inner.inner@.external_meta_wf(self.frame_permission.resource(), ())
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.slot_vaddr()
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
