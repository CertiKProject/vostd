//! Fractional ownership of a page table node.
//!
//! This module is the ownership *currency* of the model, built on
//! `vstd_extra::resource::ghost_resource::count_auth`:
//!
//! * [`NodeFrac`] — a **reader**: one fraction of a node's [`NodeIdentity`].
//!   Enough to name the node, read its level, and read PTEs through the
//!   node's atomic invariant. A [`PageTableNodeRef`](crate::node::PageTableNodeRef)
//!   carries one, and so does a [`PageTableGuard`](crate::node::PageTableGuard).
//! * [`NodeWriter`] — the **writer**: the unique token licensing PTE writes
//!   and metadata updates. It coexists with readers.
//! * [`NodeAuth`] — the **core**: the node's identity resource, every
//!   fraction not currently lent out, and the writer while nobody holds it.
//!
//! The fractions count *readers*, not anything about the node's contents. The
//! resource they agree on is the immutable [`NodeIdentity`], so a write never
//! has to touch them.
//!
//! The same construction is used in production by `ostd/src/sync/rwlock.rs`
//! (`CountResource<ReadPerm<T>, MAX_READER>`).
//!
//! # Lifetimes
//!
//! A reader must not outlive its node. That is enforced by the count, not by a
//! Rust lifetime: freeing the node would need the full fraction back in the
//! core. The model is non-RCU — readers return their fractions explicitly —
//! see the README's "Open issue: RCU reclamation".
use vstd::invariant::AtomicInvariant;
use vstd::prelude::*;
use vstd::resource::ghost_var::GhostVarAuth;
use vstd_extra::ownership::Inv;
use vstd_extra::resource::ghost_resource::count_auth::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::node::owners::*;
use crate::pte::Pte;

verus! {

/// The static ceiling on simultaneous readers of one node.
///
/// This is a *bound*, not a fixed arity: the core holds every fraction it has
/// not lent out, so the number of live readers is dynamic. `rwlock.rs` uses
/// the same `1 << 60` for `MAX_READER`.
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

// ─── The reader ────────────────────────────────────────────────────────────
/// A fraction of one node's identity: a reader.
pub tracked struct NodeFrac {
    tracked inner: Count<NodeIdentity, MAX_REFS>,
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

    /// The node's identity. All fractions of a node agree on it; see
    /// [`Self::agree`].
    pub closed spec fn view(self) -> NodeIdentity {
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

    /// Read access to the identity, with its invariant for free.
    pub proof fn borrow(tracked &self) -> (tracked res: &NodeIdentity)
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

// ─── The core ──────────────────────────────────────────────────────────────
/// A node's identity, every reader fraction not currently lent out, and the
/// writer whenever no guard holds it.
///
/// The parent's [`EntryOwner`](crate::node::EntryOwner) holds the core for its
/// child node; this is what decentralises the ownership story — the tree
/// structure carries it, instead of a flat global map.
pub tracked struct NodeAuth {
    tracked inner: CountResource<NodeIdentity, MAX_REFS>,
    /// The writer, parked here while no guard holds the node.
    tracked writer: Option<NodeWriter>,
}

impl NodeAuth {
    /// An *explicit* well-formedness predicate, deliberately not a
    /// `#[verifier::type_invariant]`.
    ///
    /// The core is mutated in place (`lend`, `reclaim`, `take_writer`), and a
    /// type invariant on a struct whose field is mutated through
    /// `&mut self.inner` is re-checked the instant the inner call returns —
    /// before the post-state facts needed to re-establish it are available.
    ///
    /// A parked writer is always *settled*: a node is only ever released with
    /// its `nr_children` bookkeeping in order.
    pub closed spec fn wf(self) -> bool {
        &&& self.inner.wf()
        &&& !self.inner.is_resource_vacant()
        &&& self.inner.resource().inv()
        &&& self.writer matches Some(w) ==> {
            &&& w.wf_for(self.inner.resource())
            &&& w.settled()
        }
    }

    /// The node's identity.
    pub closed spec fn view(self) -> NodeIdentity {
        self.inner.resource()
    }

    /// The node's metadata-slot index.
    pub open spec fn slot_index(self) -> int {
        self@.slot_index
    }

    /// The node's paging level.
    pub open spec fn level(self) -> PagingLevel {
        self@.level
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

    /// The number of reader fractions still at home.
    pub closed spec fn frac(self) -> int {
        self.inner.frac()
    }

    /// Every reader fraction is home.
    pub closed spec fn is_full(self) -> bool {
        self.inner.is_full()
    }

    /// A guard currently holds the node's writer.
    pub closed spec fn is_lent_out(self) -> bool {
        self.writer is None
    }

    /// Identity facts.
    pub proof fn lemma_identity(self)
        requires
            self.wf(),
        ensures
            self@.inv(),
            0 <= self.slot_index() < max_meta_slots(),
            1 <= self.level() <= NR_LEVELS,
    {
    }

    /// A lent-out fraction names the same identity as its core.
    pub proof fn agree(tracked &self, tracked frac: &NodeFrac)
        requires
            self.wf(),
            self.id() == frac.id(),
        ensures
            self@ == frac@,
    {
        self.inner.validate_with_frac(&frac.inner);
    }

    /// A full core holds exactly `MAX_REFS` fractions.
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

    /// Pack a freshly allocated node: build its PTE invariant and its core,
    /// and hand back the writer, so the new node starts out locked.
    ///
    /// Every reader fraction stays in the core.
    pub proof fn alloc(tracked owner: NodeOwner) -> (tracked res: (Self, NodeWriter))
        requires
            owner.inv(),
            ptes_wf(owner.children_perm.value(), owner.level),
        ensures
            res.0.wf(),
            res.0.is_full(),
            res.0.is_lent_out(),
            res.0.slot_index() == owner.slot_index,
            res.0.level() == owner.level,
            res.0@.meta_perm == owner.meta_perm,
            res.1.wf_for(res.0@),
            res.1.meta_own == owner.meta_own,
            res.1.contents@ == owner.children_perm.value(),
    {
        broadcast use lemma_max_refs_value;

        let tracked NodeOwner { meta_perm, meta_own, children_perm, level, slot_index } = owner;
        let tracked (auth, var) = GhostVarAuth::<Seq<Pte>>::new(children_perm.value());
        let ghost k = PteArrayParams { addr: children_perm.addr(), level, contents_id: auth.id() };
        let tracked arr = PteArray { perm: children_perm, contents: var };
        let tracked ptes = AtomicInvariant::<_, _, PteArrayPred>::new(k, arr, pte_array_ns());
        let tracked ident = NodeIdentity { meta_perm, ptes, level, slot_index };
        let tracked writer = NodeWriter { meta_own, contents: auth };
        (Self { inner: CountResource::alloc(ident), writer: None }, writer)
    }

    /// Lend a reader fraction.
    pub proof fn lend(tracked &mut self) -> (tracked res: NodeFrac)
        requires
            old(self).wf(),
            old(self).frac() > 0,
        ensures
            final(self).wf(),
            res.id() == final(self).id(),
            final(self).id() == old(self).id(),
            res@ == old(self)@,
            final(self)@ == old(self)@,
            res.frac() == 1,
            final(self).frac() == old(self).frac() - 1,
            final(self).is_lent_out() == old(self).is_lent_out(),
    {
        let tracked f = self.inner.split_one();
        NodeFrac { inner: f }
    }

    /// Take a reader fraction back.
    pub proof fn reclaim(tracked &mut self, tracked frac: NodeFrac)
        requires
            old(self).wf(),
            old(self).id() == frac.id(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() + frac.frac(),
            final(self)@ == old(self)@,
            final(self).is_lent_out() == old(self).is_lent_out(),
    {
        use_type_invariant(&frac);
        self.inner.validate_with_frac(&frac.inner);
        let tracked NodeFrac { inner } = frac;
        self.inner.combine(inner);
    }

    /// Hand the writer to a guard.
    ///
    /// Note what is *not* required: the readers need not come home. Readers
    /// coexist with the writer; only another writer is excluded, and that by
    /// the writer's uniqueness.
    pub proof fn take_writer(tracked &mut self) -> (tracked res: NodeWriter)
        requires
            old(self).wf(),
            !old(self).is_lent_out(),
        ensures
            final(self).wf(),
            final(self).is_lent_out(),
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self).frac() == old(self).frac(),
            res.wf_for(old(self)@),
            res.settled(),
    {
        self.writer.tracked_take()
    }

    /// Take the writer back from a guard being released.
    pub proof fn put_writer(tracked &mut self, tracked writer: NodeWriter)
        requires
            old(self).wf(),
            old(self).is_lent_out(),
            writer.wf_for(old(self)@),
            writer.settled(),
        ensures
            final(self).wf(),
            !final(self).is_lent_out(),
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self).frac() == old(self).frac(),
    {
        self.writer = Some(writer);
    }
}

} // verus!
