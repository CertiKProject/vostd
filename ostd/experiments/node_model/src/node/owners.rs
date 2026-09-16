//! Ghost ownership of a page table node.
//!
//! Model of `ostd::specs::mm::page_table::node::owners`.
//!
//! The central object is [`NodeOwner`], which holds **everything** there is to
//! own about one page table node:
//!
//! * `meta_perm` — the slot's storage. In the central-region design this was
//!   parked in `MetaRegionOwners` and a `meta_bridge` predicate had to tie it
//!   back to the node; now it simply lives here, and the tie is part of
//!   `inv()`.
//! * `meta_own` — the `PCell` permissions for the mutable metadata fields
//!   (`nr_children`, `stray`).
//! * `children_perm` — the node's page, an array of `NR_ENTRIES` PTEs mapped
//!   at `paddr_to_vaddr(paddr)`.
//!
//! A `NodeOwner` is never passed around directly by the node API. It is stored
//! inside a [`NodeAuth`](crate::node::NodeAuth) and lent out as
//! [`NodeFrac`](crate::node::NodeFrac) fractions; only a `PageTableGuard`,
//! which has gathered every fraction, holds one outright.
use core::marker::PhantomData;

use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

use vstd_extra::array_ptr;
use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::Frame;
use crate::frame::mapping::*;
use crate::node::PageTablePageMeta;
use crate::pte::Pte;

verus! {

// ─── Present-PTE counting ──────────────────────────────────────────────────
//
// The intended meaning of `nr_children` is "the number of present PTEs in this
// node". `NodeOwner::settled` pins it to `count_present(children_perm)`, which
// is what lets `replace` prove its `nr_children +/- 1` bookkeeping never
// underflows or overflows, instead of assuming it.
/// Number of present PTEs among the first `n` entries of `s`.
pub open spec fn count_present_upto(s: Seq<Pte>, n: int) -> int
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
pub open spec fn count_present(s: Seq<Pte>) -> int {
    count_present_upto(s, s.len() as int)
}

/// `count_present_upto` is between `0` and `n`.
pub proof fn lemma_count_present_upto_bound(s: Seq<Pte>, n: int)
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
pub proof fn lemma_count_present_upto_absent(s: Seq<Pte>, n: int, idx: int)
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
pub proof fn lemma_count_present_upto_present(s: Seq<Pte>, n: int, idx: int)
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

/// If two sequences agree on `[0, n)`, their counts up to `n` are equal.
pub proof fn lemma_count_present_upto_unchanged(s: Seq<Pte>, s2: Seq<Pte>, n: int, idx: int)
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

/// Updating slot `idx` shifts the count by the change in that slot's
/// present-indicator. This is the lemma `replace` needs.
pub proof fn lemma_count_present_upto_update(s: Seq<Pte>, n: int, idx: int, pte: Pte)
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
        assert(count_present_upto(s2, n - 1) == count_present_upto(s, n - 1)) by {
            lemma_count_present_upto_unchanged(s, s2, n - 1, idx);
        }
    } else {
        lemma_count_present_upto_update(s, n - 1, idx, pte);
    }
}

// ─── The node's metadata ───────────────────────────────────────────────────
/// Permissions for the two mutable metadata fields of a page table node.
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

impl OwnerOf for PageTablePageMeta {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children.id()
        &&& self.stray.id() == owner.stray.id()
        &&& 0 <= owner.nr_children.value() <= NR_ENTRIES
    }
}

// ─── The node ──────────────────────────────────────────────────────────────
/// Everything there is to own about one page table node.
///
/// The real type also carries `tree_level`, the level of the `ghost_tree` node
/// that holds this owner. The model has no ghost tree, so it is dropped.
pub tracked struct NodeOwner {
    /// The node's metadata slot storage. Previously parked in
    /// `MetaRegionOwners`; holding it here is what lets the node certify
    /// itself.
    pub meta_perm: PointsTo<PageTablePageMeta>,
    pub meta_own: PageMetaOwner,
    pub children_perm: array_ptr::PointsTo<Pte, NR_ENTRIES>,
    pub ghost level: PagingLevel,
    pub ghost slot_index: int,
}

impl Inv for NodeOwner {
    open spec fn inv(self) -> bool {
        &&& self.meta_own.inv()
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.children_perm.wf()
        &&& self.children_perm.is_init_all()
        &&& self.children_perm.value().len() == NR_ENTRIES
        &&& 0 <= self.slot_index
            < max_meta_slots()
        // The node's PTE array lives at the linear-mapping address of the
        // node's own frame. This is what makes two distinct nodes hold
        // disjoint `children_perm`s.
        &&& self.children_perm.addr() == paddr_to_vaddr_spec(
            index_to_frame(self.slot_index),
        )
        // The former `meta_bridge`: the slot permission this owner holds is
        // the right slot, is initialised, and agrees with the `PCell`
        // permissions in `meta_own`. In the central-region design these four
        // clauses had to be re-established against the region after every
        // change; now they are simply part of being a `NodeOwner`.
        &&& self.meta_perm.addr() == index_to_meta(self.slot_index)
        &&& self.meta_perm.is_init()
        &&& self.meta_perm.value().wf(self.meta_own)
        &&& self.level == self.meta_perm.value().level
    }
}

impl NodeOwner {
    /// The address of this node's metadata slot. A `Frame` handle to the node
    /// stores exactly this address.
    pub open spec fn meta_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    /// The physical address of this node's frame. A PTE pointing at this node
    /// stores exactly this address.
    pub open spec fn paddr(self) -> Paddr {
        index_to_frame(self.slot_index)
    }

    /// The metadata value this owner's slot permission holds.
    pub open spec fn meta_value(self) -> PageTablePageMeta {
        self.meta_perm.value()
    }

    /// A *settled* node additionally has `nr_children` equal to the number of
    /// present PTEs.
    ///
    /// This is deliberately not part of `inv()`: it is momentarily false
    /// inside `replace`, between the counter update and the PTE write. Since
    /// `inv()` is what a [`NodeFrac`](crate::node::NodeFrac) carries, keeping
    /// it out means a fraction never promises something a mid-flight node
    /// cannot deliver.
    pub open spec fn settled(self) -> bool {
        self.count_consistent()
    }

    /// `nr_children` equals the number of present PTEs in `children_perm`.
    pub open spec fn count_consistent(self) -> bool {
        self.meta_own.nr_children.value() == count_present(self.children_perm.value())
    }

    /// An absent slot means the node is not full, so `nr_children` can be
    /// incremented. Proven from `count_consistent`, not assumed.
    pub proof fn nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.count_consistent(),
            idx < NR_ENTRIES,
            !self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }

    /// A present slot means `nr_children` is non-zero, so it can be
    /// decremented. Dual of [`Self::nr_children_absent_slot_bound`].
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            self.count_consistent(),
            idx < NR_ENTRIES,
            self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() > 0,
    {
        lemma_count_present_upto_present(self.children_perm.value(), NR_ENTRIES as int, idx as int);
    }
}

pub ghost struct NodeModel {
    pub level: PagingLevel,
}

impl Inv for NodeModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for NodeOwner {
    type V = NodeModel;

    open spec fn view(&self) -> <Self as View>::V {
        NodeModel { level: self.level }
    }
}

impl InvView for NodeOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl OwnerOf for Frame<PageTablePageMeta> {
    type Owner = NodeOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        self.ptr.addr() == owner.meta_vaddr()
    }
}

impl Frame<PageTablePageMeta> {
    pub open spec fn invariants(self, owner: NodeOwner) -> bool {
        &&& owner.inv()
        &&& self.wf(owner)
    }
}

} // verus!
