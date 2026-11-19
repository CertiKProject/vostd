use vstd::{
    cell::{self, pcell_maybe_uninit},
    prelude::*,
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
// slots the node owns (`NodeOwner::owned_range`). `metaregion_sound_node` ties
// `nr_children` to that count (`NodeOwner::count_consistent`, a settled-node
// invariant), which lets the `nr_children_*_slot_bound` boundary facts be
// proven rather than axiomatized.
/// Number of present PTEs among entries `lo..n` of `s`.
pub open spec fn count_present_between<E: PageTableEntryTrait>(s: Seq<E>, lo: int, n: int) -> int
    decreases n - lo,
{
    if n <= lo {
        0
    } else {
        count_present_between(s, lo, n - 1) + if s[n - 1].is_present() {
            1int
        } else {
            0int
        }
    }
}

/// `count_present_between` is between `0` and `n - lo`.
pub proof fn lemma_count_present_between_bound<E: PageTableEntryTrait>(s: Seq<E>, lo: int, n: int)
    requires
        lo <= n,
    ensures
        0 <= count_present_between(s, lo, n) <= n - lo,
    decreases n - lo,
{
    if n > lo {
        lemma_count_present_between_bound(s, lo, n - 1);
    }
}

/// An absent slot in `lo..n` makes the count strictly less than `n - lo`.
pub proof fn lemma_count_present_between_absent<E: PageTableEntryTrait>(
    s: Seq<E>,
    lo: int,
    n: int,
    idx: int,
)
    requires
        lo <= idx < n,
        !s[idx].is_present(),
    ensures
        count_present_between(s, lo, n) < n - lo,
    decreases n - lo,
{
    lemma_count_present_between_bound(s, lo, n - 1);
    if idx < n - 1 {
        lemma_count_present_between_absent(s, lo, n - 1, idx);
    }
}

/// A present slot in `lo..n` makes the count at least `1`.
pub proof fn lemma_count_present_between_present<E: PageTableEntryTrait>(
    s: Seq<E>,
    lo: int,
    n: int,
    idx: int,
)
    requires
        lo <= idx < n,
        s[idx].is_present(),
    ensures
        count_present_between(s, lo, n) >= 1,
    decreases n - lo,
{
    lemma_count_present_between_bound(s, lo, n - 1);
    if idx < n - 1 {
        lemma_count_present_between_present(s, lo, n - 1, idx);
    }
}

/// If two sequences agree on `lo..n`, their counts there are equal.
pub proof fn lemma_count_present_between_unchanged<E: PageTableEntryTrait>(
    s: Seq<E>,
    s2: Seq<E>,
    lo: int,
    n: int,
)
    requires
        forall|k: int| lo <= k < n ==> s[k] == s2[k],
    ensures
        count_present_between(s2, lo, n) == count_present_between(s, lo, n),
    decreases n - lo,
{
    if n > lo {
        lemma_count_present_between_unchanged(s, s2, lo, n - 1);
    }
}

/// Updating slot `idx` shifts the count over `lo..n` by the change in that
/// slot's present-indicator if `idx` is in `lo..n`, and leaves it unchanged
/// otherwise.
pub proof fn lemma_count_present_between_update<E: PageTableEntryTrait>(
    s: Seq<E>,
    lo: int,
    n: int,
    idx: int,
    pte: E,
)
    requires
        0 <= lo,
        n <= s.len(),
        0 <= idx < s.len(),
    ensures
        count_present_between(s.update(idx, pte), lo, n) == count_present_between(s, lo, n) + if lo
            <= idx < n {
            (if pte.is_present() {
                1int
            } else {
                0int
            }) - (if s[idx].is_present() {
                1int
            } else {
                0int
            })
        } else {
            0int
        },
    decreases n - lo,
{
    let s2 = s.update(idx, pte);
    if n > lo {
        if n - 1 == idx {
            lemma_count_present_between_unchanged(s, s2, lo, n - 1);
        } else {
            lemma_count_present_between_update(s, lo, n - 1, idx, pte);
        }
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
/// - `meta_own`, a `PageMetaOwner`, which holds the permissions for node-specific
///   metadata fields, `nr_children` and `stray`
/// - `children_perm` is an array permission for the underlying frame in which the node
///   is allocated, interpreted as an array of `NR_ENTRIES` page table entries
/// - `slot_index` identifies the underlying frame's index in the metadata region
/// - Each node is a page table with a level between 1 and 4 (on x86); `level` tracks
///   the level of this node.
/// - `tree_level` is the level field of the `ghost_tree::TreeNode` that carries this object.
///   Carried here for convenience, though it can be computed from `level`.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub frame_permission: FracMetadataPerm,
    pub children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
    pub ghost tree_level: int,
    pub ghost slot_index: int,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_own.inv()
        &&& self.frame_permission.frac() == 1
        &&& 1 <= self.level() <= NR_LEVELS
        &&& self.children_perm.wf()
        &&& self.children_perm.is_init_all()
        &&& self.children_perm.addr() == paddr_to_vaddr(
            meta_to_frame(index_to_meta(self.slot_index)),
        )
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
        &&& self.meta_value().wf(
            self.meta_own,
        )
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

    /// `nr_children` equals the number of present PTEs in `children_perm`.
    /// Held by a settled node (see `metaregion_sound_node`'s use site).
    pub open spec fn count_consistent(self) -> bool {
        self.meta_own.nr_children.value() == self.count_owned()
    }

    /// The slots whose children this node owns, `lo..hi`. A top-level node owns
    /// only the configuration's [`PageTableConfig::TOP_LEVEL_INDEX_RANGE`]: a user
    /// page table borrows the kernel's half, which it does not count or drop
    /// (upstream's `PageTablePageMeta::on_drop` walks only this range). Every
    /// other node owns all its slots.
    pub open spec fn owned_range(self) -> (int, int) {
        if self.level() == C::NR_LEVELS() {
            (
                C::TOP_LEVEL_INDEX_RANGE_spec().start as int,
                C::TOP_LEVEL_INDEX_RANGE_spec().end as int,
            )
        } else {
            (0, NR_ENTRIES as int)
        }
    }

    /// The node owns the child in slot `i`.
    pub open spec fn owns_slot(self, i: int) -> bool {
        self.owned_range().0 <= i < self.owned_range().1
    }

    /// The number of present PTEs in the slots the node owns: what `nr_children`
    /// counts.
    pub open spec fn count_owned(self) -> int {
        count_present_between(
            self.children_perm.value(),
            self.owned_range().0,
            self.owned_range().1,
        )
    }

    /// The owned range is within the node's slots.
    pub proof fn lemma_owned_range_bounds(self)
        ensures
            0 <= self.owned_range().0 <= self.owned_range().1 <= NR_ENTRIES,
            self.owned_range().1 - self.owned_range().0 < NR_ENTRIES ==> self.level()
                == C::NR_LEVELS(),
    {
        C::lemma_page_table_config_constant_properties();
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
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
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            !self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() < NR_ENTRIES,
    {
        let (lo, hi) = self.owned_range();
        self.lemma_owned_range_bounds();
        lemma_count_present_between_bound(self.children_perm.value(), lo, hi);
        if lo <= idx < hi {
            lemma_count_present_between_absent(self.children_perm.value(), lo, hi, idx as int);
        }
    }

    /// If a slot in `children_perm` holds a present PTE, then `nr_children > 0`.
    /// Dual of [`Self::lemma_nr_children_absent_slot_bound`]; proven from
    /// `count_consistent`.
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.count_consistent(),
            self.children_perm.value().len() == NR_ENTRIES,
            idx < NR_ENTRIES,
            self.owns_slot(idx as int),
            self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() > 0,
    {
        let (lo, hi) = self.owned_range();
        lemma_count_present_between_present(self.children_perm.value(), lo, hi, idx as int);
    }

    /// Writing slot `idx` changes the owned count by the change in that slot's
    /// present-indicator, if the node owns the slot, and not at all otherwise.
    pub proof fn lemma_count_owned_update(self, other: Self, idx: int, pte: C::E)
        requires
            self.children_perm.value().len() == NR_ENTRIES,
            0 <= idx < NR_ENTRIES,
            other.children_perm.value() == self.children_perm.value().update(idx, pte),
            other.frame_permission == self.frame_permission,
        ensures
            other.count_owned() == self.count_owned() + if self.owns_slot(idx) {
                (if pte.is_present() {
                    1int
                } else {
                    0int
                }) - (if self.children_perm.value()[idx].is_present() {
                    1int
                } else {
                    0int
                })
            } else {
                0int
            },
    {
        let (lo, hi) = self.owned_range();
        self.lemma_owned_range_bounds();
        lemma_count_present_between_update(self.children_perm.value(), lo, hi, idx, pte);
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
