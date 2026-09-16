//! Fractional ownership of a page table node.
//!
//! This module is the ownership *currency* of the model. It replaces the
//! central `MetaRegionOwners` and the `Guards` ghost lock-set with two tokens
//! built on `vstd_extra::resource::ghost_resource::count_auth`:
//!
//! * [`NodeFrac`] — a **fraction** of one node's ownership. Enough to *read*
//!   the node (its level, its PTEs, its `nr_children`), and nothing more. A
//!   [`PageTableNodeRef`](crate::node::PageTableNodeRef) carries one.
//! * [`NodeAuth`] — the **authority**: the node's [`NodeOwner`] itself,
//!   together with whatever fractions have not been lent out. Only when every
//!   fraction has come home can the authority hand back exclusive ownership,
//!   which is what a [`PageTableGuard`](crate::node::PageTableGuard) holds and
//!   what permits *writing* a PTE.
//!
//! The same construction is used in production by `ostd/src/sync/rwlock.rs`
//! (`CountResource<ReadPerm<T>, MAX_READER>`).
//!
//! # Invariants travel with the token
//!
//! [`NodeFrac`] declares a `#[verifier::type_invariant]` asserting
//! `NodeOwner::inv()` of the node it names. So [`NodeFrac::borrow`] hands back
//! a `&NodeOwner` *already known to be well formed*, with no precondition and
//! no region to consult. That is the substance of the change: a node's
//! invariant is carried by the thing that refers to the node, rather than
//! re-established from a global map at every call.
use vstd::prelude::*;
use vstd_extra::ownership::Inv;
use vstd_extra::resource::ghost_resource::count_auth::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::node::owners::NodeOwner;

verus! {

/// The static ceiling on simultaneous references to one node.
///
/// This is a *bound*, not a fixed arity: the authority holds every fraction it
/// has not lent out, so the number of live references is dynamic. `rwlock.rs`
/// uses the same `1 << 60` for `MAX_READER`.
pub const MAX_REFS: usize = 1 << 60;

/// The literal value of [`MAX_REFS`].
///
/// `Count::bounded()` states `frac() <= TOTAL` against the *const-generic*
/// parameter, and Verus does not on its own connect that symbol to the named
/// constant. Folding it once here saves repeating the `compute_only` nudge.
pub broadcast proof fn lemma_max_refs_value()
    ensures
        #[trigger] MAX_REFS == 1152921504606846976usize,
{
    assert(MAX_REFS == 1152921504606846976usize) by (compute_only);
}

// ─── The fraction ──────────────────────────────────────────────────────────
/// A fraction of one node's ownership: enough to read, never enough to write.
pub tracked struct NodeFrac {
    tracked inner: Count<NodeOwner, MAX_REFS>,
}

impl NodeFrac {
    /// The node's invariant travels *with* the fraction.
    ///
    /// A type invariant is the right tool here because a `NodeFrac` is only
    /// ever borrowed or consumed, never mutated in place. (Contrast
    /// [`NodeAuth::wf`], which must be an explicit predicate for exactly that
    /// reason.)
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.inner.resource().inv()
    }

    /// Identifies *which* node this is a fraction of.
    pub closed spec fn id(self) -> vstd::resource::Loc {
        self.inner.id()
    }

    pub closed spec fn frac(self) -> int {
        self.inner.frac()
    }

    /// What the node currently is. All fractions of a node agree on this; see
    /// [`Self::agree`].
    pub closed spec fn view(self) -> NodeOwner {
        self.inner.resource()
    }

    /// Recover the carried invariant. No `requires` clause — that is the point.
    pub proof fn validate(tracked &self)
        ensures
            self@.inv(),
            0 < self.frac() <= MAX_REFS,
    {
        broadcast use lemma_max_refs_value;

        use_type_invariant(self);
        self.inner.bounded();
    }

    /// Read access, with the node's invariant for free.
    pub proof fn borrow(tracked &self) -> (tracked res: &NodeOwner)
        ensures
            *res == self@,
            res.inv(),
    {
        use_type_invariant(self);
        self.inner.tracked_borrow()
    }

    /// Two fractions of the same node see the same node.
    pub proof fn agree(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        self.inner.agree(&other.inner)
    }

    /// Subdivide a fraction, e.g. to hand a second reference to the same node.
    pub proof fn split(tracked &mut self) -> (tracked res: Self)
        requires
            old(self).frac() > 1,
        ensures
            res.id() == old(self).id(),
            final(self).id() == old(self).id(),
            res@ == old(self)@,
            final(self)@ == old(self)@,
            res.frac() == 1,
            final(self).frac() == old(self).frac() - 1,
    {
        use_type_invariant(&*self);
        let tracked f = self.inner.split(1);
        Self { inner: f }
    }

    /// Merge two fractions of the same node.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self).frac() == old(self).frac() + other.frac(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self.inner.agree(&other.inner);
        let tracked Self { inner } = other;
        self.inner.combine(inner);
    }
}

// ─── The authority ─────────────────────────────────────────────────────────
/// A node's ownership, plus every fraction not currently lent out.
///
/// The parent's [`EntryOwner`](crate::node::EntryOwner) holds the authority
/// for its child node; this is what decentralises the ownership story — the
/// tree structure carries it, instead of a flat global map.
pub tracked struct NodeAuth {
    tracked inner: CountResource<NodeOwner, MAX_REFS>,
    /// Which node this is the authority for.
    ///
    /// Held separately from the resource so that the node stays *identifiable*
    /// while it is lent out to a guard. Without this, a locked child would
    /// make its parent's `match_pte` meaningless, because a vacant
    /// `CountResource` has no resource to ask.
    pub ghost slot: int,
    /// The node's paging level, kept for the same reason.
    pub ghost lvl: PagingLevel,
}

impl NodeAuth {
    /// An *explicit* well-formedness predicate, deliberately not a
    /// `#[verifier::type_invariant]`.
    ///
    /// The authority is mutated in place (`lend`, `reclaim`,
    /// `into_exclusive`), and a type invariant on a struct whose field is
    /// mutated through `&mut self.inner` is re-checked the instant the inner
    /// call returns — before the post-state facts needed to re-establish it
    /// are available.
    pub closed spec fn wf(self) -> bool {
        &&& self.inner.wf()
        &&& 0 <= self.slot < max_meta_slots()
        &&& 1 <= self.lvl <= NR_LEVELS
        &&& !self.inner.is_resource_vacant() ==> {
            &&& self.inner.resource().inv()
            &&& self.inner.resource().slot_index == self.slot
            &&& self.inner.resource().level == self.lvl
        }
    }

    /// The node's metadata-slot index. Meaningful even while lent out.
    pub closed spec fn slot_index(self) -> int {
        self.slot
    }

    /// The node's paging level. Meaningful even while lent out.
    pub closed spec fn level(self) -> PagingLevel {
        self.lvl
    }

    /// The physical address of the node's frame — what a PTE pointing at this
    /// node stores.
    pub open spec fn paddr(self) -> Paddr {
        index_to_frame(self.slot_index())
    }

    /// The address of the node's metadata slot.
    pub open spec fn meta_vaddr(self) -> Vaddr {
        index_to_meta(self.slot_index())
    }

    pub closed spec fn id(self) -> vstd::resource::Loc {
        self.inner.id()
    }

    pub closed spec fn frac(self) -> int {
        self.inner.frac()
    }

    /// Every fraction is home, so exclusive ownership can be taken.
    pub closed spec fn is_full(self) -> bool {
        self.inner.is_full()
    }

    /// A guard currently holds the node's `NodeOwner`.
    pub closed spec fn is_lent_out(self) -> bool {
        self.inner.is_resource_vacant()
    }

    pub closed spec fn view(self) -> NodeOwner {
        self.inner.resource()
    }

    /// The node's invariant, straight from the authority — available whenever
    /// the node is not currently lent out to a guard.
    pub proof fn lemma_inv(self)
        requires
            self.wf(),
            !self.is_lent_out(),
        ensures
            self@.inv(),
            self@.slot_index == self.slot_index(),
            self@.level == self.level(),
            self@.paddr() == self.paddr(),
            self@.meta_vaddr() == self.meta_vaddr(),
    {
    }

    /// Identity facts that hold unconditionally, lent out or not.
    pub proof fn lemma_identity(self)
        requires
            self.wf(),
        ensures
            0 <= self.slot_index() < max_meta_slots(),
            1 <= self.level() <= NR_LEVELS,
    {
    }

    /// A full authority holds exactly `MAX_REFS` fractions.
    pub proof fn lemma_full_frac(self)
        requires
            self.wf(),
            self.is_full(),
        ensures
            self.frac() == MAX_REFS as int,
            self.frac() > 1,
    {
        broadcast use lemma_max_refs_value;

    }

    /// Every fraction is home. Folding the `MAX_REFS` literal is needed because
    /// `is_full()` is stated against the const-generic `TOTAL`.
    pub proof fn lemma_full_from_frac(self)
        requires
            self.wf(),
            self.frac() == MAX_REFS as int,
        ensures
            self.is_full(),
    {
        broadcast use lemma_max_refs_value;

    }

    /// A non-zero fraction means the node is actually present here, so the
    /// carried invariant applies.
    pub proof fn lemma_present(tracked &self)
        requires
            self.wf(),
            self.frac() > 0,
        ensures
            !self.is_lent_out(),
            self@.inv(),
    {
        if self.inner.is_resource_vacant() {
            self.inner.lemma_resource_vacant_implies_empty();
        }
    }

    /// Take ownership of a freshly created node.
    pub proof fn alloc(tracked owner: NodeOwner) -> (tracked res: Self)
        requires
            owner.inv(),
        ensures
            res.wf(),
            res.is_full(),
            res@ == owner,
            res.slot_index() == owner.slot_index,
            res.level() == owner.level,
    {
        broadcast use lemma_max_refs_value;

        let ghost slot = owner.slot_index;
        let ghost lvl = owner.level;
        let tracked inner = CountResource::alloc(owner);
        Self { inner, slot, lvl }
    }

    /// Lend a fraction to a new reference.
    pub proof fn lend(tracked &mut self) -> (tracked res: NodeFrac)
        requires
            old(self).wf(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            res.id() == final(self).id(),
            final(self).id() == old(self).id(),
            res@ == old(self)@,
            final(self)@ == old(self)@,
            res.frac() == 1,
            final(self).frac() == old(self).frac() - 1,
            final(self).slot_index() == old(self).slot_index(),
            final(self).level() == old(self).level(),
            res@.slot_index == old(self).slot_index(),
            res@.level == old(self).level(),
    {
        self.lemma_present();
        let tracked f = self.inner.split_one();
        NodeFrac { inner: f }
    }

    /// Take a fraction back from a reference that is going away.
    pub proof fn reclaim(tracked &mut self, tracked frac: NodeFrac)
        requires
            old(self).wf(),
            old(self).id() == frac.id(),
            old(self).frac() > 0,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() + frac.frac(),
            final(self)@ == old(self)@,
            final(self).slot_index() == old(self).slot_index(),
            final(self).level() == old(self).level(),
    {
        self.lemma_present();
        use_type_invariant(&frac);
        self.inner.validate_with_frac(&frac.inner);
        let tracked NodeFrac { inner } = frac;
        self.inner.combine(inner);
    }

    /// Every fraction is home: hand over exclusive ownership.
    ///
    /// This is the only route to a [`PageTableGuard`](crate::node::PageTableGuard),
    /// and therefore the only route to writing a PTE.
    pub proof fn into_exclusive(tracked &mut self) -> (tracked res: NodeOwner)
        requires
            old(self).wf(),
            old(self).is_full(),
        ensures
            final(self).wf(),
            final(self).is_lent_out(),
            res == old(self)@,
            res.inv(),
            res.slot_index == old(self).slot_index(),
            res.level == old(self).level(),
            final(self).id() == old(self).id(),
            final(self).slot_index() == old(self).slot_index(),
            final(self).level() == old(self).level(),
    {
        broadcast use lemma_max_refs_value;

        self.lemma_present();
        self.inner.take_resource()
    }

    /// Give exclusive ownership back when the guard is released.
    pub proof fn restore(tracked &mut self, tracked owner: NodeOwner)
        requires
            old(self).wf(),
            old(self).is_lent_out(),
            owner.inv(),
            owner.slot_index == old(self).slot_index(),
            owner.level == old(self).level(),
        ensures
            final(self).wf(),
            final(self).is_full(),
            final(self)@ == owner,
            final(self).id() == old(self).id(),
            final(self).slot_index() == old(self).slot_index(),
            final(self).level() == old(self).level(),
    {
        self.inner.put_resource(owner);
    }
}

} // verus!
