//! Ghost ownership of a page table node.
//!
//! Model of `ostd::specs::mm::page_table::node::owners`.
//!
//! A node's ownership is split three ways, by *how each part changes*:
//!
//! * [`NodeIdentity`] — what never changes once the node exists: the slot's
//!   storage permission `meta_perm`, the level, the slot index, and the
//!   [`AtomicInvariant`] that guards the PTE array. This is what every
//!   reader agrees on, so it is the resource inside a
//!   [`NodeFrac`](crate::node::NodeFrac). Because it is immutable, nothing a
//!   writer does ever has to be propagated to the readers.
//! * [`PteArray`], stored *inside* that invariant — the PTE array permission
//!   itself. Readers and the writer alike open the invariant around a single
//!   atomic `load_pte` / `store_pte`; what a reader learns is only the
//!   invariant's weak predicate [`pte_wf`], which is exactly the guarantee an
//!   unlocked reader in the real code has.
//! * [`NodeWriter`] — the unique write token: the `PCell` permissions for the
//!   lock-protected metadata (`nr_children`, `stray`), and the authoritative
//!   half of a ghost variable that pins the *exact* PTE array. A
//!   `PageTableGuard` holds it, which is why a guard knows precisely what the
//!   node contains while a reader does not.
//!
//! [`NodeOwner`] remains as the *unpacked* form of all of this — what the frame
//! allocator hands back for a fresh node, before
//! [`NodeAuth::alloc`](crate::node::NodeAuth::alloc) packs it.
use core::marker::PhantomData;

use vstd::cell::pcell_maybe_uninit;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
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

// ─── The node, unpacked ────────────────────────────────────────────────────
/// Everything there is to own about one page table node, in one bundle.
///
/// This is the form in which [`PageTableNode::alloc`](crate::node::PageTableNode::alloc)
/// returns a fresh node. It is immediately packed by
/// [`NodeAuth::alloc`](crate::node::NodeAuth::alloc) into a [`NodeIdentity`]
/// (shared by readers), a [`PteArray`] (inside an atomic invariant) and a
/// [`NodeWriter`] (held by whoever holds the lock).
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
        // node's own frame.
        &&& self.children_perm.addr() == paddr_to_vaddr_spec(
            index_to_frame(self.slot_index),
        )
        // The former `meta_bridge`: the slot permission this owner holds is
        // the right slot, is initialised, and agrees with the `PCell`
        // permissions in `meta_own`.
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

    /// `nr_children` equals the number of present PTEs.
    pub open spec fn settled(self) -> bool {
        self.meta_own.nr_children.value() == count_present(self.children_perm.value())
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

// ─── What a reader may assume about a PTE ──────────────────────────────────
/// The weak, level-local well-formedness of one PTE in a node at `level`.
///
/// This is the predicate of the PTE array's atomic invariant, and therefore
/// *everything* a reader without the lock learns from `read_pte`. It is the
/// part of [`EntryOwner::match_pte`](crate::node::EntryOwner::match_pte) that
/// can be stated without knowing what the entry owns:
///
/// * every PTE carries a valid frame address;
/// * an absent PTE above level 1 does not claim to terminate the walk;
/// * a terminating PTE is not at the top level (no 512 GiB pages).
pub open spec fn pte_wf(pte: Pte, level: PagingLevel) -> bool {
    &&& valid_frame_paddr(pte.paddr())
    &&& !pte.is_present() && level > 1 ==> !pte.is_last(level)
    &&& pte.is_present() && pte.is_last(level) ==> level < NR_LEVELS
}

/// Every PTE in `ptes` is well formed at `level`.
pub open spec fn ptes_wf(ptes: Seq<Pte>, level: PagingLevel) -> bool {
    &&& ptes.len() == NR_ENTRIES
    &&& forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] pte_wf(ptes[i], level)
}

/// The absent PTE is well formed at any level.
pub proof fn lemma_absent_pte_wf(level: PagingLevel)
    ensures
        pte_wf(Pte::new_absent_spec(), level),
{
    assert(valid_frame_paddr(0)) by (compute_only);
}

// ─── The PTE array and its invariant ───────────────────────────────────────
/// What lives inside a node's atomic invariant: the PTE array permission, and
/// the invariant's half of the ghost variable mirroring the array's contents.
pub tracked struct PteArray {
    pub perm: array_ptr::PointsTo<Pte, NR_ENTRIES>,
    /// Always equal to `perm.value()`. The writer holds the authoritative
    /// half, which is how it knows the exact contents between invariant
    /// openings.
    pub contents: GhostVar<Seq<Pte>>,
}

/// The constants a node's PTE invariant is configured with.
pub ghost struct PteArrayParams {
    /// The virtual address of the node's PTE array.
    pub addr: usize,
    /// The node's level; [`pte_wf`] depends on it.
    pub level: PagingLevel,
    /// The ghost variable the writer's [`NodeWriter::contents`] must match.
    pub contents_id: Loc,
}

pub struct PteArrayPred;

impl InvariantPredicate<PteArrayParams, PteArray> for PteArrayPred {
    open spec fn inv(k: PteArrayParams, v: PteArray) -> bool {
        &&& v.perm.wf()
        &&& v.perm.addr() == k.addr
        &&& v.perm.is_init_all()
        &&& v.contents.id() == k.contents_id
        &&& v.contents@ == v.perm.value()
        &&& ptes_wf(v.perm.value(), k.level)
    }
}

/// The namespace of every node's PTE invariant. No code path opens two of
/// them at once, so they can share one.
pub open spec fn pte_array_ns() -> int {
    0
}

// ─── The identity: what readers share ──────────────────────────────────────
/// The immutable part of a node, shared by every reader.
///
/// Nothing in here changes for the lifetime of the node, which is what makes
/// it safe to replicate across [`NodeFrac`](crate::node::NodeFrac)s: the
/// agreement that `Count` enforces never has to be re-established after a
/// write.
pub tracked struct NodeIdentity {
    /// The node's metadata slot. Read-only: the mutable metadata fields are
    /// `PCell`s whose permissions live in the [`NodeWriter`].
    pub meta_perm: PointsTo<PageTablePageMeta>,
    /// Guards the PTE array.
    pub ptes: AtomicInvariant<PteArrayParams, PteArray, PteArrayPred>,
    pub ghost level: PagingLevel,
    pub ghost slot_index: int,
}

impl Inv for NodeIdentity {
    open spec fn inv(self) -> bool {
        &&& 1 <= self.level <= NR_LEVELS
        &&& 0 <= self.slot_index < max_meta_slots()
        &&& self.meta_perm.addr() == index_to_meta(self.slot_index)
        &&& self.meta_perm.is_init()
        &&& self.level == self.meta_perm.value().level
        &&& self.ptes.constant().addr == paddr_to_vaddr_spec(index_to_frame(self.slot_index))
        &&& self.ptes.constant().level == self.level
        &&& self.ptes.namespace() == pte_array_ns()
    }
}

impl NodeIdentity {
    pub open spec fn meta_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn paddr(self) -> Paddr {
        index_to_frame(self.slot_index)
    }
}

// ─── The writer ────────────────────────────────────────────────────────────
/// The unique permission to write a node: what a `PageTableGuard` holds.
///
/// Mutual exclusion between writers is simply the uniqueness of this token —
/// readers may coexist with it.
pub tracked struct NodeWriter {
    /// The `PCell` permissions for `nr_children` and `stray`.
    pub meta_own: PageMetaOwner,
    /// The authoritative half of the ghost variable mirroring the PTE array:
    /// the exact contents, as of the writer's last write.
    pub contents: GhostVarAuth<Seq<Pte>>,
}

impl NodeWriter {
    /// This is a writer for the node `id`.
    pub open spec fn wf_for(self, id: NodeIdentity) -> bool {
        &&& self.meta_own.inv()
        &&& id.meta_perm.value().wf(self.meta_own)
        &&& self.contents.id() == id.ptes.constant().contents_id
        &&& self.contents@.len() == NR_ENTRIES
    }

    /// `nr_children` equals the number of present PTEs.
    ///
    /// Deliberately not part of [`Self::wf_for`]: it is momentarily false
    /// inside `replace`, between the counter update and the PTE write.
    pub open spec fn settled(self) -> bool {
        self.meta_own.nr_children.value() == count_present(self.contents@)
    }
}

// ─── The writer's view ─────────────────────────────────────────────────────
/// Everything a writer knows about its node, as plain values.
///
/// The view of a `PageTableGuard`. Ghost, so specifications can compare a
/// guard before and after an operation without touching tracked state.
pub ghost struct NodeView {
    pub level: PagingLevel,
    pub slot_index: int,
    /// The exact PTE array.
    pub ptes: Seq<Pte>,
    pub nr_children: u16,
    pub stray: bool,
}

impl NodeView {
    pub open spec fn meta_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index)
    }

    pub open spec fn paddr(self) -> Paddr {
        index_to_frame(self.slot_index)
    }

    /// A *settled* node has `nr_children` equal to the number of present PTEs.
    pub open spec fn settled(self) -> bool {
        self.nr_children == count_present(self.ptes)
    }

    /// An absent slot means the node is not full, so `nr_children` can be
    /// incremented. Proven from `settled`, not assumed.
    pub proof fn nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.ptes.len() == NR_ENTRIES,
            self.settled(),
            idx < NR_ENTRIES,
            !self.ptes[idx as int].is_present(),
        ensures
            self.nr_children < NR_ENTRIES,
    {
        lemma_count_present_upto_absent(self.ptes, NR_ENTRIES as int, idx as int);
    }

    /// A present slot means `nr_children` is non-zero, so it can be
    /// decremented. Dual of [`Self::nr_children_absent_slot_bound`].
    pub proof fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.ptes.len() == NR_ENTRIES,
            self.settled(),
            idx < NR_ENTRIES,
            self.ptes[idx as int].is_present(),
        ensures
            self.nr_children > 0,
    {
        lemma_count_present_upto_present(self.ptes, NR_ENTRIES as int, idx as int);
    }
}

} // verus!
