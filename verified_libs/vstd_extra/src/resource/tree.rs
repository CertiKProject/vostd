//! Shared ghost trees whose subtrees are checked out one writer at a time.
//!
//! # Why not [`crate::ghost_tree`]
//!
//! [`crate::ghost_tree::Tree`] is a linear tracked value. Reaching a node
//! means borrowing the root, so exactly one party can hold the tree, and a
//! cursor that walks down must physically take each subtree out and remember
//! how to put it back. That models a single-threaded walk well and a shared
//! page table not at all: two threads cannot hold overlapping prefixes of the
//! same tree, and nothing in the type expresses "this subtree is locked".
//!
//! This module keeps `ghost_tree`'s shape — [`TreePath`], arity `N`, depth
//! bound `L`, and the [`TreeNodeValue`] invariants — and replaces the linear
//! spine with one ownership cell per node.
//!
//! # Scope: writers only
//!
//! This module governs **write/write exclusion** between subtree holders.
//! Read sharing is not modelled here and is expected to be governed by RCU,
//! so a node has exactly two states rather than three. Concretely that means
//! a holder may look anywhere inside its own subtree
//! ([`NodeResource::tracked_borrow_descendant`]) but there is no token a
//! concurrent reader can hold, and nothing here constrains a reader.
//!
//! That is sound because the physical permissions never leave the node value
//! `T`: converting or mutating a subtree here moves ghost ownership of cells
//! and never touches a `PointsTo`. Whatever makes a concurrent read safe — a
//! grace period, or the frame reference count that
//! `Count<MetadataPerm, REF_COUNT_MAX>` already tracks a layer below — is
//! established against the permissions inside `T`, not against this tree.
//! This module makes no claim about readers, in either direction.
//!
//! # Structure
//!
//! A node's contents live inside the Leaf-style storage protocol of a
//! one-slot [`CountResource`], and what that cell protects is a
//! [`NodeResource`]: the node's own value together with the *cells of its
//! children*. Cells nest the way nodes do:
//!
//! ```text
//!   SubtreeLock (cell)
//!     └── NodeResource { value: T, children: [SubtreeLock, ...] }
//!                                              └── NodeResource { ... }
//! ```
//!
//! A cell is either occupied or checked out:
//!
//! | state        | predicate                    | meaning                        |
//! |--------------|------------------------------|--------------------------------|
//! | occupied     | `!`[`SubtreeLock::is_vacant`] | available to be checked out    |
//! | checked out  | [`SubtreeLock::is_vacant`]   | one writer holds the node      |
//!
//! Checking a node out yields a [`SubtreeWriter`]; handing it back refills the
//! cell. That is an ordinary mutex at one node. The tree structure is what
//! makes it a *subtree* lock:
//!
//! - **A writer descends by withdrawal.** A writer reaches a child only
//!   through the parent's [`NodeResource`], and holding that means the
//!   parent's cell is checked out. So a writer anywhere inside a subtree has
//!   passed through the subtree's root cell, and holding that root excludes
//!   every other writer beneath it.
//! - **Disjoint subtrees never interfere.** Two children's cells are separate
//!   [`Loc`]s — [`SubtreeLock::lemma_distinct`] — so locking one says nothing
//!   about the other.
//!
//! Acquiring a subtree lock is therefore a single operation on a single token,
//! not a walk that collects one token per node.
//!
//! # Frozen identity vs. protected contents
//!
//! A parent's invariant must survive a child being checked out, otherwise
//! locking a child would invalidate its ancestors — and a child guard
//! deliberately *does* outlive the parent guard that minted it, since that is
//! how a subtree is handed to another thread. So a node value is split:
//! [`SharedTreeValue::stable`] projects out the part fixed for the node's
//! lifetime (for a page table: its level and physical address), and
//! [`SharedTreeValue::rel_stable`] is the edge relation over that part alone.
//! [`SubtreeLock`] records its node's frozen identity *outside* the cell, so
//! [`NodeResource::inv_children`] holds in either cell state.
//!
//! The rest — the agreement between a parent's value and a child's full value,
//! [`NodeResource::coherent`] — is exactly what a [`SubtreeWriter`] holder may
//! break. It is not part of [`NodeResource::inv`], and
//! [`SubtreeLock::tracked_write_release`] is what forces identity and level to
//! be restored.
//!
//! # Leaving the resource world
//!
//! A subtree with nothing checked out below it can be dissolved back into a
//! plain [`crate::ghost_tree`] value with [`SubtreeWriter::tracked_into_tree`],
//! [`SubtreeLock::tracked_into_tree`], or [`NodeResource::tracked_into_tree`].
//! The result is a tracked [`TreeNode`] equal to
//! [`NodeResource::view_tree`], so every linear tree operation applies to it
//! afterwards.
//!
//! The precondition is [`NodeResource::fully_locked`], and it does *not*
//! follow from holding the root guard: a child guard outlives the parent guard
//! that minted it, so a descendant can still be checked out by someone else.
//! Dissolving the subtree consumes those nodes, so every descendant guard must
//! have come home first.
//!
//! [`NodeResource::coherent`] is not needed to perform the conversion, only to
//! conclude that the result satisfies [`TreeNode::inv`]; a writer midway
//! through restoring a parent/child relation can still dissolve its subtree,
//! it just gets no invariant with it.
//!
//! [`SubtreeLock::tracked_from_tree`] goes the other way, wrapping a plain
//! [`TreeNode`] and every node beneath it in fresh cells. The round trip is
//! exact on the tree — `tracked_from_tree(l.tracked_into_tree())` denotes what
//! `l` denoted — but *not* on identity: every cell is newly allocated, so no
//! [`Loc`] survives a trip out of and back into the resource world. Ghost
//! state elsewhere that records a node's cell identity must be rebuilt.
//!
//! # Reusing the existing specifications
//!
//! [`NodeResource::view_tree`] maps a subtree to the pure [`TreeNode`] it
//! currently denotes, with checked-out children appearing absent, and
//! [`NodeResource::lemma_view_tree_inv`] shows a coherent subtree's view
//! satisfies [`TreeNode::inv`]. Every path lemma in [`crate::ghost_tree`] —
//! `recursive_visit`, `recursive_seek`, `trace`, `on_subtree`, `path_between` —
//! therefore applies unchanged to this tree's view.
//!
//! # Wiring to a real lock
//!
//! The cell is ghost state; a client ties it to a physical lock word through
//! [`crate::resource_invariant::ResourceInvariant`], whose `inv` relates the
//! lock word to [`SubtreeLock::is_vacant`]. Because there is no reader count
//! to track, that word is a plain mutex rather than the three-valued
//! reference count the frame layer keeps.
//!
//! # Not covered here
//!
//! Reads, as above. If a read-side token over *this* algebra is ever wanted —
//! a counted lease that pins a node's contents without checking it out — the
//! cell generalises to the counting [`CountResource`] it is already built on:
//! the full count is this module's checked-out state, and a partial count is a
//! shared lease. That was the original shape of this module and was removed
//! because it duplicated the frame reference count.
use crate::ghost_tree::{TreeNode, TreePath};
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::ghost_resource::count_auth::CountResource;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// A [`TreeNodeValue`] that separates a node's frozen identity from its
/// lock-protected contents.
pub trait SharedTreeValue<const L: usize>: TreeNodeValue<L> {
    /// The part of a node's value that is fixed for the node's lifetime.
    type Stable;

    /// Projects the frozen identity out of a node value.
    spec fn stable(self) -> Self::Stable;

    /// Edge relation between a parent value and the frozen identity of its
    /// child at `index`.
    spec fn rel_stable(self, index: int, child: Option<Self::Stable>) -> bool;

    /// `rel_children` refines `rel_stable`.
    proof fn lemma_rel_children_refines_rel_stable(self, index: int, child: Option<Self>)
        ensures
            self.rel_children(index, child) ==> self.rel_stable(
                index,
                match child {
                    Some(c) => Some(c.stable()),
                    None => None,
                },
            ),
    ;
}

/// The contents of one tree node, protected by that node's [`SubtreeLock`].
pub tracked struct NodeResource<T: SharedTreeValue<L>, const N: usize, const L: usize> {
    tracked value: T,
    ghost level: nat,
    // Boxed in `Tracked` for the same reason as `ghost_tree::TreeNode`;
    // see https://github.com/verus-lang/verus/issues/2627.
    tracked children: Tracked<Seq<Option<SubtreeLock<T, N, L>>>>,
}

/// The counting authority for the subtree rooted at one node.
pub tracked struct SubtreeLock<T: SharedTreeValue<L>, const N: usize, const L: usize> {
    ghost stable: T::Stable,
    tracked pool: CountResource<NodeResource<T, N, L>, 1>,
}

/// Exclusive access to the subtree rooted at one node.
pub tracked struct SubtreeWriter<T: SharedTreeValue<L>, const N: usize, const L: usize> {
    ghost id: Loc,
    ghost stable: T::Stable,
    ghost level: nat,
    tracked node: NodeResource<T, N, L>,
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// The lock-protected value stored in this node.
    pub closed spec fn value(self) -> T {
        self.value
    }

    /// The depth of this node below the root.
    pub closed spec fn level(self) -> nat {
        self.level
    }

    /// The locks of this node's children, `None` at absent slots.
    pub closed spec fn children(self) -> Seq<Option<SubtreeLock<T, N, L>>> {
        self.children@
    }

    /// Whether the `i`-th child exists.
    pub open spec fn has_child(self, i: int) -> bool {
        self.children()[i] is Some
    }

    /// The lock of the `i`-th child. Only meaningful when it exists.
    pub open spec fn child(self, i: int) -> SubtreeLock<T, N, L> {
        self.children()[i]->0
    }

    /// This node has no children at all.
    pub open spec fn is_childless(self) -> bool {
        forall|i: int| 0 <= i < N ==> (#[trigger] self.children()[i]) is None
    }

    /// Node-local invariant, excluding anything about the children.
    pub open spec fn inv_node(self) -> bool {
        &&& self.value().inv()
        &&& self.value().la_inv(self.level())
        &&& self.level() < L
        &&& self.children().len() == N
    }

    /// Edge invariant for every child slot. This holds whatever lock state the
    /// children are in, because it only mentions their frozen identities.
    pub open spec fn inv_children(self) -> bool {
        if self.level() == L - 1 {
            forall|i: int| 0 <= i < N ==> (#[trigger] self.children()[i]) is None
        } else {
            forall|i: int|
                0 <= i < N ==> match #[trigger] self.children()[i] {
                    Some(lock) => lock.inv_edge(self.value(), i, self.level()),
                    None => self.value().rel_stable(i, None),
                }
        }
    }

    /// Whole-subtree invariant. Descends only into children that are not
    /// currently withdrawn by a writer: a withdrawn child's invariant is the
    /// obligation of the [`SubtreeWriter`] that holds it.
    pub open spec fn inv(self) -> bool
        decreases L - self.level(),
    {
        &&& L > 0
        &&& N > 0
        &&& self.inv_node()
        &&& self.inv_children()
        &&& if L - self.level() == 1 {
            true
        } else {
            forall|i: int|
                0 <= i < N ==> match #[trigger] self.children()[i] {
                    Some(lock) => lock.is_vacant() || lock.node().inv(),
                    None => true,
                }
        }
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeLock<T, N, L> {
    /// The resource location identifying this lock.
    pub closed spec fn id(self) -> Loc {
        self.pool.id()
    }

    /// The frozen identity of the locked node.
    pub closed spec fn stable(self) -> T::Stable {
        self.stable
    }

    /// Whether the node is currently withdrawn by a [`SubtreeWriter`].
    pub closed spec fn is_vacant(self) -> bool {
        self.pool.is_resource_vacant()
    }

    /// The locked node. Only meaningful when the node is not withdrawn.
    pub closed spec fn node(self) -> NodeResource<T, N, L> {
        self.pool.resource()
    }

    /// The cell is well formed and never partially issued, and an occupied
    /// cell carries the frozen identity this lock advertises to its parent.
    ///
    /// "Never partially issued" is what makes this a two-state ownership
    /// cell rather than the counting pool it is built on: no operation here
    /// ever splits a fraction out, so the cell is whole whenever occupied.
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.pool.wf()
        &&& self.pool.is_resource_vacant() || self.pool.is_full()
        &&& !self.pool.is_resource_vacant() ==> self.pool.resource().value().stable() == self.stable
    }

    /// An occupied cell's node carries the identity this lock advertises.
    ///
    /// Needed by any client rebuilding [`NodeResource::inv_edge`] for a lock
    /// it did not just construct — one taken out with
    /// [`NodeResource::tracked_remove_child`], say.
    pub proof fn lemma_stable_agrees(tracked &self)
        requires
            !self.is_vacant(),
        ensures
            self.node().value().stable() == self.stable(),
    {
        use_type_invariant(self);
    }

    /// What a parent may rely on about a child slot in any lock state.
    pub open spec fn inv_edge(self, parent: T, i: int, parent_level: nat) -> bool {
        &&& parent.rel_stable(i, Some(self.stable()))
        &&& !self.is_vacant() ==> {
            &&& self.node().level() == parent_level + 1
            &&& self.node().value().stable() == self.stable()
        }
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// Builds a node from its tracked parts.
    pub proof fn tracked_new(
        tracked value: T,
        level: nat,
        tracked children: Seq<Option<SubtreeLock<T, N, L>>>,
    ) -> (tracked res: Self)
        ensures
            res.value() == value,
            res.level() == level,
            res.children() == children,
    {
        NodeResource { value, level, children: Tracked(children) }
    }

    /// Builds a fresh childless node.
    pub proof fn tracked_new_leaf(tracked value: T, level: nat) -> (tracked res: Self)
        requires
            L > 0,
            N > 0,
            level < L,
            value.inv(),
            value.la_inv(level),
            forall|i: int| 0 <= i < N ==> #[trigger] value.rel_stable(i, None),
        ensures
            res.inv(),
            res.value() == value,
            res.level() == level,
            res.children() == Seq::new(N as nat, |i| None),
            res.is_childless(),
    {
        proof fn tracked_none_seq<A>(n: nat) -> (tracked res: Seq<Option<A>>)
            ensures
                res == Seq::new(n, |i| None),
            decreases n,
        {
            if n == 0 {
                Seq::tracked_empty()
            } else {
                let tracked mut res = tracked_none_seq((n - 1) as nat);
                res.tracked_push(None);
                res
            }
        }
        let tracked children = tracked_none_seq(N as nat);
        Self::tracked_new(value, level, children)
    }

    /// Consumes this node and returns its tracked parts.
    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (
        T,
        Seq<Option<SubtreeLock<T, N, L>>>,
    ))
        ensures
            res.0 == self.value(),
            res.1 == self.children(),
    {
        let tracked Tracked(children) = self.children;
        (self.value, children)
    }

    /// Borrows this node's value.
    pub proof fn tracked_borrow_value(tracked &self) -> (tracked res: &T)
        returns
            self.value(),
    {
        &self.value
    }

    /// Mutably borrows this node's value, leaving the children untouched.
    pub proof fn tracked_borrow_mut_value(tracked &mut self) -> (tracked res: &mut T)
        ensures
            *res == old(self).value(),
            final(self).value() == *final(res),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children(),
    {
        &mut self.value
    }

    /// Borrows the lock of the `i`-th child.
    pub proof fn tracked_borrow_child(tracked &self, i: int) -> (tracked res: &SubtreeLock<T, N, L>)
        requires
            0 <= i < self.children().len(),
            self.has_child(i),
        returns
            self.child(i),
    {
        self.children.tracked_borrow(i).tracked_borrow()
    }

    /// Mutably borrows the lock of the `i`-th child. This is how a writer
    /// descends: the child's slot stays `Some`, so the parent's
    /// [`Self::inv_children`] survives the child being write-locked.
    pub proof fn tracked_borrow_mut_child(tracked &mut self, i: int) -> (tracked res:
        &mut SubtreeLock<T, N, L>)
        requires
            0 <= i < old(self).children().len(),
            old(self).has_child(i),
        ensures
            *res == old(self).child(i),
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children().update(i, Some(*final(res))),
    {
        match self.children.tracked_borrow_mut(i) {
            Some(ref mut lock) => lock,
            None => vstd::pervasive::proof_from_false(),
        }
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeLock<T, N, L> {
    /// Creates an unlocked subtree lock holding `node`.
    pub proof fn tracked_new(tracked node: NodeResource<T, N, L>) -> (tracked res: Self)
        ensures
            !res.is_vacant(),
            res.node() == node,
            res.stable() == node.value().stable(),
            !res.is_vacant(),
    {
        let ghost stable = node.value().stable();
        let tracked pool = CountResource::alloc(node);
        Self { stable, pool }
    }

    /// Borrows the locked node for reading.
    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeResource<T, N, L>)
        requires
            !self.is_vacant(),
        returns
            self.node(),
    {
        self.pool.tracked_borrow()
    }

    /// Acquires exclusive access to this subtree, withdrawing the node.
    ///
    /// Only possible when the node is not already checked out by another
    /// writer.
    pub proof fn tracked_write_acquire(tracked &mut self) -> (tracked res: SubtreeWriter<T, N, L>)
        requires
            !old(self).is_vacant(),
        ensures
            final(self).id() == old(self).id(),
            final(self).stable() == old(self).stable(),
            final(self).is_vacant(),
            res.id() == old(self).id(),
            res.stable() == old(self).stable(),
            res.level() == old(self).node().level(),
            res.node() == old(self).node(),
    {
        use_type_invariant(&*self);
        let ghost stable = self.stable;
        let ghost level = self.pool.resource().level();
        let tracked node = self.pool.take_resource();
        SubtreeWriter { id: self.pool.id(), stable, level, node }
    }

    /// Releases exclusive access, depositing the node back into the lock.
    ///
    /// The guard must restore the node's frozen identity and level, which is
    /// what lets a parent's [`NodeResource::inv_children`] hold throughout.
    pub proof fn tracked_write_release(tracked &mut self, tracked guard: SubtreeWriter<T, N, L>)
        requires
            old(self).is_vacant(),
            old(self).id() == guard.id(),
            old(self).stable() == guard.stable(),
            guard.node().value().stable() == guard.stable(),
            guard.node().level() == guard.level(),
        ensures
            final(self).id() == old(self).id(),
            final(self).stable() == old(self).stable(),
            !final(self).is_vacant(),
            !final(self).is_vacant(),
            final(self).node() == guard.node(),
            final(self).node().level() == guard.level(),
            final(self).node().value().stable() == old(self).stable(),
    {
        use_type_invariant(&*self);
        let tracked SubtreeWriter { id: _, stable: _, level: _, node } = guard;
        self.pool.put_resource(node);
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeWriter<T, N, L> {
    /// The lock this guard was acquired from.
    pub closed spec fn id(self) -> Loc {
        self.id
    }

    /// The frozen identity this guard must restore.
    pub closed spec fn stable(self) -> T::Stable {
        self.stable
    }

    /// The level this guard must restore.
    pub closed spec fn level(self) -> nat {
        self.level
    }

    /// The exclusively held node.
    pub closed spec fn node(self) -> NodeResource<T, N, L> {
        self.node
    }

    /// Borrows the held node.
    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeResource<T, N, L>)
        returns
            self.node(),
    {
        &self.node
    }

    /// Mutably borrows the held node. Identity and level must be restored
    /// before [`SubtreeLock::tracked_write_release`] accepts the guard back.
    pub proof fn tracked_borrow_mut_node(tracked &mut self) -> (tracked res: &mut NodeResource<
        T,
        N,
        L,
    >)
        ensures
            *res == old(self).node(),
            final(self).node() == *final(res),
            final(self).id() == old(self).id(),
            final(self).stable() == old(self).stable(),
            final(self).level() == old(self).level(),
    {
        &mut self.node
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// The node reached by following `path`, provided every lock along the way
    /// still holds its node (no writer has withdrawn it).
    pub open spec fn seek(self, path: TreePath<N>) -> Option<NodeResource<T, N, L>>
        decreases path.len(),
    {
        if path.is_empty() {
            Some(self)
        } else {
            let (hd, tl) = path.pop_head();
            if 0 <= hd < N && self.has_child(hd) && !self.child(hd).is_vacant() {
                self.child(hd).node().seek(tl)
            } else {
                None
            }
        }
    }

    /// Whether `path` resolves to a node reachable from here.
    pub open spec fn reachable(self, path: TreePath<N>) -> bool {
        self.seek(path) is Some
    }

    /// The empty path resolves to this node.
    pub proof fn lemma_seek_empty(self, path: TreePath<N>)
        requires
            path.is_empty(),
        ensures
            self.seek(path) == Some(self),
    {
    }

    /// One step of [`Self::seek`], so callers need no fuel reasoning.
    pub proof fn lemma_seek_step(self, path: TreePath<N>)
        requires
            !path.is_empty(),
            0 <= path.pop_head().0 < N,
            self.has_child(path.pop_head().0),
            !self.child(path.pop_head().0).is_vacant(),
        ensures
            self.seek(path) == self.child(path.pop_head().0).node().seek(path.pop_head().1),
    {
    }

    /// [`Self::seek`] fails at a missing or withdrawn child.
    pub proof fn lemma_seek_blocked(self, path: TreePath<N>)
        requires
            !path.is_empty(),
            !(0 <= path.pop_head().0 < N) || !self.has_child(path.pop_head().0) || self.child(
                path.pop_head().0,
            ).is_vacant(),
        ensures
            self.seek(path) is None,
    {
    }

    /// Borrows a descendant through shared borrows only.
    ///
    /// Every step down is a shared borrow, so a holder can look anywhere in
    /// its own subtree without checking anything out.
    pub proof fn tracked_borrow_descendant<'a>(tracked &'a self, path: TreePath<N>) -> (tracked res:
        &'a NodeResource<T, N, L>)
        requires
            self.inv(),
            path.inv(),
            self.reachable(path),
        ensures
            *res == self.seek(path)->0,
        decreases path.len(),
    {
        if path.is_empty() {
            self
        } else {
            let (hd, tl) = path.pop_head();
            let tracked lock = self.tracked_borrow_child(hd);
            let tracked child = lock.tracked_borrow_node();
            child.tracked_borrow_descendant(tl)
        }
    }

    /// Installs a lock in an empty child slot.
    pub proof fn tracked_insert_child(tracked &mut self, i: int, tracked lock: SubtreeLock<T, N, L>)
        requires
            0 <= i < old(self).children().len(),
            !old(self).has_child(i),
        ensures
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children().update(i, Some(lock)),
    {
        let tracked _ = self.children.borrow_mut().tracked_remove(i);
        self.children.borrow_mut().tracked_insert(i, Some(lock));
        assert(self.children() =~= old(self).children().update(i, Some(lock)));
    }

    /// Detaches the lock of an existing child, emptying its slot.
    ///
    /// The caller owes the parent's [`Self::inv_children`] for slot `i` until
    /// the slot is refilled or the parent's value is updated to record the
    /// child's absence.
    pub proof fn tracked_remove_child(tracked &mut self, i: int) -> (tracked res: SubtreeLock<
        T,
        N,
        L,
    >)
        requires
            0 <= i < old(self).children().len(),
            old(self).has_child(i),
        ensures
            res == old(self).child(i),
            final(self).value() == old(self).value(),
            final(self).level() == old(self).level(),
            final(self).children() == old(self).children().update(i, None),
    {
        let tracked lock = self.children.borrow_mut().tracked_remove(i).tracked_unwrap();
        self.children.borrow_mut().tracked_insert(i, None);
        assert(self.children() =~= old(self).children().update(i, None));
        lock
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeLock<T, N, L> {
    /// Two subtree locks are different cells.
    ///
    /// This is the formal content of "disjoint subtrees never interfere":
    /// nothing a holder of one lock does is visible through the other.
    pub proof fn lemma_distinct(tracked &mut self, tracked other: &Self)
        ensures
            *final(self) == *old(self),
            final(self).id() != other.id(),
    {
        use_type_invariant(&*self);
        self.pool.lemma_distinct_authority(&other.pool);
    }

    /// Dissolves an available lock and recovers its node.
    ///
    /// This consumes the cell, so it is admissible only while the cell is
    /// occupied: a node that is checked out belongs to its guard holder.
    pub proof fn tracked_into_node(tracked self) -> (tracked res: NodeResource<T, N, L>)
        requires
            !self.is_vacant(),
        ensures
            res == self.node(),
            res.value().stable() == self.stable(),
    {
        use_type_invariant(&self);
        let tracked mut pool = self.pool;
        pool.take_resource()
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// The pure [`TreeNode`] this subtree denotes, cut off at `depth`.
    ///
    /// `depth` is a manifest fuel counter so that termination does not depend
    /// on tree structure, matching the `pt_inv_at_depth` idiom already used by
    /// the page-table proofs.
    pub open spec fn view_tree_at(self, depth: nat) -> TreeNode<T, N, L>
        decreases depth,
    {
        TreeNode::new(
            self.value(),
            self.level(),
            Seq::new(
                N as nat,
                |i: int|
                    if depth > 0 && 0 <= i < N && self.has_child(i) && !self.child(i).is_vacant() {
                        Some(self.child(i).node().view_tree_at((depth - 1) as nat))
                    } else {
                        None
                    },
            ),
        )
    }

    /// The pure [`TreeNode`] this subtree currently denotes.
    ///
    /// Withdrawn children appear as absent, so the view is the part of the
    /// subtree observable without acquiring any further lock. This is the
    /// bridge that lets a client reuse the path lemmas of
    /// [`crate::ghost_tree`] against a shared tree.
    pub open spec fn view_tree(self) -> TreeNode<T, N, L> {
        self.view_tree_at((L - self.level()) as nat)
    }

    /// Every present child's full value, not just its frozen identity, agrees
    /// with this node's value.
    ///
    /// [`Self::inv`] deliberately does not require this: it is exactly the
    /// part of the tree invariant that a [`SubtreeWriter`] holder is allowed to
    /// break and must restore. A subtree with no writer inside it is coherent,
    /// and only then does its view satisfy [`TreeNode::inv`].
    pub open spec fn coherent_at(self, depth: nat) -> bool
        decreases depth,
    {
        (depth > 0 && self.level() < L - 1) ==> forall|i: int|
            0 <= i < N ==> match #[trigger] self.children()[i] {
                Some(lock) => if lock.is_vacant() {
                    self.value().rel_children(i, None)
                } else {
                    &&& self.value().rel_children(i, Some(lock.node().value()))
                    &&& lock.node().coherent_at((depth - 1) as nat)
                },
                None => self.value().rel_children(i, None),
            }
    }

    /// Whether the whole subtree below this node is coherent.
    pub open spec fn coherent(self) -> bool {
        self.coherent_at((L - self.level()) as nat)
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// A coherent shared subtree denotes a well-formed [`TreeNode`].
    pub proof fn lemma_view_tree_at_inv(self, depth: nat)
        requires
            self.inv(),
            self.coherent_at(depth),
            depth == L - self.level(),
        ensures
            self.view_tree_at(depth).inv(),
        decreases depth,
    {
        let view = self.view_tree_at(depth);
        assert(view.value() == self.value());
        assert(view.level() == self.level());
        assert(view.children().len() == N);
        assert forall|i: int| 0 <= i < N implies #[trigger] view.children()[i] == if depth > 0
            && self.has_child(i) && !self.child(i).is_vacant() {
            Some(self.child(i).node().view_tree_at((depth - 1) as nat))
        } else {
            None
        } by {}
        if self.level() == L - 1 {
            assert forall|i: int| 0 <= i < N implies (#[trigger] view.children()[i]) is None by {
                assert(self.children()[i] is None);
            }
        } else {
            assert forall|i: int| 0 <= i < N implies match #[trigger] view.children()[i] {
                Some(child) => {
                    &&& child.level() == view.level() + 1
                    &&& view.value().rel_children(i, Some(child.value()))
                    &&& child.inv()
                },
                None => view.value().rel_children(i, None),
            } by {
                assert(self.children()[i] is Some ==> self.child(i).inv_edge(
                    self.value(),
                    i,
                    self.level(),
                ));
                if self.has_child(i) && !self.child(i).is_vacant() {
                    let node = self.child(i).node();
                    assert(node.level() == self.level() + 1);
                    assert(node.inv());
                    assert(node.coherent_at((depth - 1) as nat));
                    node.lemma_view_tree_at_inv((depth - 1) as nat);
                }
            }
        }
    }

    /// A coherent shared subtree denotes a well-formed [`TreeNode`].
    pub proof fn lemma_view_tree_inv(self)
        requires
            self.inv(),
            self.coherent(),
        ensures
            self.view_tree().inv(),
    {
        self.lemma_view_tree_at_inv((L - self.level()) as nat);
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// No descendant is checked out by another writer, down to `depth`.
    ///
    /// This is the formal content of "fully locked", and it does not follow
    /// from holding a [`SubtreeWriter`] on the subtree's root. Taking that
    /// guard stops any *new* descendant from being checked out, but a child
    /// guard minted earlier is an owned token that outlives its parent's
    /// guard — which is how a subtree is handed to another thread. Only when
    /// every such guard has come home is the subtree entirely in one
    /// holder's hands.
    pub open spec fn fully_locked_at(self, depth: nat) -> bool
        decreases depth,
    {
        depth > 0 ==> forall|i: int|
            0 <= i < N ==> match #[trigger] self.children()[i] {
                Some(lock) => !lock.is_vacant() && lock.node().fully_locked_at((depth - 1) as nat),
                None => true,
            }
    }

    /// No descendant is checked out by another writer.
    pub open spec fn fully_locked(self) -> bool {
        self.fully_locked_at((L - self.level()) as nat)
    }

    /// One step of [`Self::fully_locked_at`], so callers need no fuel reasoning.
    pub proof fn lemma_fully_locked_at_unfold(self, depth: nat)
        requires
            depth > 0,
        ensures
            self.fully_locked_at(depth) <==> forall|i: int|
                0 <= i < N ==> match #[trigger] self.children()[i] {
                    Some(lock) => !lock.is_vacant() && lock.node().fully_locked_at(
                        (depth - 1) as nat,
                    ),
                    None => true,
                },
    {
    }

    /// A childless node is fully locked at every depth.
    pub proof fn lemma_fully_locked_at_leaf(self, depth: nat)
        requires
            self.is_childless(),
        ensures
            self.fully_locked_at(depth),
    {
    }

    /// One step of [`Self::coherent_at`], so callers need no fuel reasoning.
    pub proof fn lemma_coherent_at_unfold(self, depth: nat)
        requires
            depth > 0,
            self.level() < L - 1,
        ensures
            self.coherent_at(depth) <==> forall|i: int|
                0 <= i < N ==> match #[trigger] self.children()[i] {
                    Some(lock) => if lock.is_vacant() {
                        self.value().rel_children(i, None)
                    } else {
                        &&& self.value().rel_children(i, Some(lock.node().value()))
                        &&& lock.node().coherent_at((depth - 1) as nat)
                    },
                    None => self.value().rel_children(i, None),
                },
    {
    }

    /// A node at the deepest level is coherent for free: [`TreeNode::inv`]
    /// relates no values there, because such a node can have no children.
    pub proof fn lemma_coherent_at_bottom(self, depth: nat)
        requires
            self.level() == L - 1,
        ensures
            self.coherent_at(depth),
    {
    }

    /// A childless node is coherent at every depth once its value records that
    /// every slot is absent.
    pub proof fn lemma_coherent_at_leaf(self, depth: nat)
        requires
            self.is_childless(),
            forall|i: int| 0 <= i < N ==> #[trigger] self.value().rel_children(i, None),
        ensures
            self.coherent_at(depth),
    {
    }

    /// The node-local fields of a subtree view.
    pub proof fn lemma_view_tree_at_fields(self, depth: nat)
        ensures
            self.view_tree_at(depth).value() == self.value(),
            self.view_tree_at(depth).level() == self.level(),
            self.view_tree_at(depth).children().len() == N,
    {
    }

    /// One child slot of a subtree view.
    pub proof fn lemma_view_tree_at_child(self, depth: nat, i: int)
        requires
            0 <= i < N,
        ensures
            self.view_tree_at(depth).has_child(i) <==> (depth > 0 && self.has_child(i)
                && !self.child(i).is_vacant()),
            (depth > 0 && self.has_child(i) && !self.child(i).is_vacant()) ==> self.view_tree_at(
                depth,
            ).child(i) == self.child(i).node().view_tree_at((depth - 1) as nat),
    {
    }

    /// Dissolves a fully locked subtree, down to `depth`, into a plain
    /// [`TreeNode`].
    pub proof fn tracked_into_tree_at(tracked self, depth: nat) -> (tracked res: TreeNode<T, N, L>)
        requires
            depth == L - self.level(),
            self.inv(),
            self.fully_locked_at(depth),
        ensures
            res == self.view_tree_at(depth),
        decreases depth, N as int + 1,
    {
        let ghost me = self;
        let ghost level = self.level();
        let tracked (value, children) = self.tracked_into_parts();
        let tracked child_trees = Self::tracked_convert_children(children, depth);
        assert(child_trees =~= me.view_tree_at(depth).children());
        TreeNode::tracked_new(value, level, child_trees)
    }

    /// Dissolves every lock in a child sequence into plain [`TreeNode`]s.
    ///
    /// `depth` is the *parent's* depth, so the children sit at `depth - 1`.
    /// Together with [`Self::tracked_into_tree_at`] this forms one lexicographic
    /// recursion: descending a level shrinks `depth`, and consuming a child
    /// shrinks the sequence.
    proof fn tracked_convert_children(
        tracked locks: Seq<Option<SubtreeLock<T, N, L>>>,
        depth: nat,
    ) -> (tracked res: Seq<Option<TreeNode<T, N, L>>>)
        requires
            depth > 0,
            forall|i: int|
                0 <= i < locks.len() ==> match #[trigger] locks[i] {
                    Some(lock) => {
                        &&& !lock.is_vacant()
                        &&& lock.node().inv()
                        &&& lock.node().level() == L - depth + 1
                        &&& lock.node().fully_locked_at((depth - 1) as nat)
                    },
                    None => true,
                },
        ensures
            res.len() == locks.len(),
            forall|i: int|
                0 <= i < locks.len() ==> #[trigger] res[i] == match locks[i] {
                    Some(lock) => Some(lock.node().view_tree_at((depth - 1) as nat)),
                    None => None,
                },
        decreases depth, locks.len(),
    {
        if locks.len() == 0 {
            Seq::tracked_empty()
        } else {
            let ghost old_locks = locks;
            let tracked mut locks = locks;
            let tracked head = locks.tracked_pop_front();
            let tracked mut rest = Self::tracked_convert_children(locks, depth);
            let tracked converted = match head {
                Some(lock) => {
                    let tracked node = lock.tracked_into_node();
                    Some(node.tracked_into_tree_at((depth - 1) as nat))
                },
                None => None,
            };
            rest.tracked_push_front(converted);
            assert forall|i: int| 0 <= i < old_locks.len() implies #[trigger] rest[i]
                == match old_locks[i] {
                Some(lock) => Some(lock.node().view_tree_at((depth - 1) as nat)),
                None => None,
            } by {
                if i > 0 {
                    assert(old_locks.drop_first()[i - 1] == old_locks[i]);
                }
            }
            rest
        }
    }

    /// Dissolves a fully locked subtree into a plain [`TreeNode`].
    ///
    /// The result is the subtree's [`Self::view_tree`], now owned as an
    /// ordinary [`crate::ghost_tree`] value, so every linear tree operation
    /// applies to it. [`Self::coherent`] is not needed to perform the
    /// conversion, only to conclude that the result satisfies
    /// [`TreeNode::inv`].
    pub proof fn tracked_into_tree(tracked self) -> (tracked res: TreeNode<T, N, L>)
        requires
            self.inv(),
            self.fully_locked(),
        ensures
            res == self.view_tree(),
            self.coherent() ==> res.inv(),
    {
        let ghost me = self;
        let tracked res = self.tracked_into_tree_at((L - me.level()) as nat);
        if me.coherent() {
            me.lemma_view_tree_inv();
        }
        res
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeLock<T, N, L> {
    /// Dissolves a fully locked subtree, lock and all, into a plain
    /// [`TreeNode`].
    pub proof fn tracked_into_tree(tracked self) -> (tracked res: TreeNode<T, N, L>)
        requires
            !self.is_vacant(),
            self.node().inv(),
            self.node().fully_locked(),
        ensures
            res == self.node().view_tree(),
            self.node().coherent() ==> res.inv(),
    {
        let tracked node = self.tracked_into_node();
        node.tracked_into_tree()
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeWriter<T, N, L> {
    /// Dissolves the exclusively held subtree into a plain [`TreeNode`].
    ///
    /// This consumes the guard without releasing it, so the [`SubtreeLock`] it
    /// came from stays vacant for good: the shared tree is being taken apart,
    /// not handed back. Drop that lock, or use
    /// [`SubtreeLock::tracked_into_tree`] to consume it in the same step.
    pub proof fn tracked_into_tree(tracked self) -> (tracked res: TreeNode<T, N, L>)
        requires
            self.node().inv(),
            self.node().fully_locked(),
        ensures
            res == self.node().view_tree(),
            self.node().coherent() ==> res.inv(),
    {
        let tracked SubtreeWriter { id: _, stable: _, level: _, node } = self;
        node.tracked_into_tree()
    }
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> NodeResource<T, N, L> {
    /// Rebuilds a subtree in the resource world from a plain [`TreeNode`],
    /// down to `depth`.
    pub proof fn tracked_from_tree_at(tracked tree: TreeNode<T, N, L>, depth: nat) -> (tracked res:
        Self)
        requires
            depth == L - tree.level(),
            tree.inv(),
        ensures
            res.value() == tree.value(),
            res.level() == tree.level(),
            res.inv(),
            res.fully_locked_at(depth),
            res.coherent_at(depth),
            res.view_tree_at(depth) == tree,
        decreases depth, N as int + 1,
    {
        let ghost original = tree;
        let ghost level = tree.level();
        let tracked (value, children) = tree.tracked_into_parts();
        let tracked cells = Self::tracked_cells_from_children(children, depth);
        let tracked res = Self::tracked_new(value, level, cells);
        if level == L - 1 {
            // `TreeNode::inv` already forces a bottom-level node childless, so
            // the rebuilt node is childless too and relates no values.
            assert forall|i: int| 0 <= i < N implies (#[trigger] res.children()[i]) is None by {
                assert(original.children()[i] is None);
            }
            res.lemma_coherent_at_bottom(depth);
        } else {
            assert forall|i: int| 0 <= i < N implies match #[trigger] res.children()[i] {
                Some(lock) => lock.inv_edge(res.value(), i, res.level()),
                None => res.value().rel_stable(i, None),
            } by {
                original.value().lemma_rel_children_refines_rel_stable(
                    i,
                    match original.children()[i] {
                        Some(c) => Some(c.value()),
                        None => None,
                    },
                );
            }
        }
        assert(res.inv_children());

        // The recursive conjuncts of `inv`, `fully_locked_at` and
        // `coherent_at` all come straight from the children the helper built.
        assert forall|i: int| 0 <= i < N implies match #[trigger] res.children()[i] {
            Some(lock) => {
                &&& !lock.is_vacant()
                &&& lock.node().inv()
                &&& lock.node().fully_locked_at((depth - 1) as nat)
                &&& lock.node().coherent_at((depth - 1) as nat)
                &&& lock.node().value() == original.child(i).value()
            },
            None => true,
        } by {
            if res.children()[i] is Some {
                assert(original.children()[i] is Some);
            }
        }
        assert(res.inv());
        assert(res.fully_locked_at(depth));
        if level < L - 1 {
            assert forall|i: int| 0 <= i < N implies match #[trigger] res.children()[i] {
                Some(lock) => {
                    &&& !lock.is_vacant()
                    &&& res.value().rel_children(i, Some(lock.node().value()))
                    &&& lock.node().coherent_at((depth - 1) as nat)
                },
                None => res.value().rel_children(i, None),
            } by {
                assert(original.inv_children());
                if res.children()[i] is Some {
                    assert(original.children()[i] is Some);
                    assert(res.child(i).node().value() == original.child(i).value());
                    assert(original.value().rel_children(i, Some(original.child(i).value())));
                } else {
                    assert(original.children()[i] is None);
                }
            }
            assert(res.coherent_at(depth));
        }
        assert(res.view_tree_at(depth).children() =~= original.children());
        res
    }

    /// Wraps each child of a plain [`TreeNode`] in a fresh cell.
    ///
    /// `depth` is the *parent's* depth, mirroring
    /// [`Self::tracked_convert_children`] in the opposite direction.
    proof fn tracked_cells_from_children(
        tracked children: Seq<Option<TreeNode<T, N, L>>>,
        depth: nat,
    ) -> (tracked res: Seq<Option<SubtreeLock<T, N, L>>>)
        requires
            depth > 0,
            forall|i: int|
                0 <= i < children.len() ==> match #[trigger] children[i] {
                    Some(child) => child.inv() && child.level() == L - depth + 1,
                    None => true,
                },
        ensures
            res.len() == children.len(),
            forall|i: int|
                0 <= i < children.len() ==> match #[trigger] children[i] {
                    Some(child) => {
                        &&& res[i] matches Some(lock)
                        &&& res[i]->0.stable() == child.value().stable()
                        &&& !res[i]->0.is_vacant()
                        &&& res[i]->0.node().value() == child.value()
                        &&& res[i]->0.node().level() == child.level()
                        &&& res[i]->0.node().inv()
                        &&& res[i]->0.node().fully_locked_at((depth - 1) as nat)
                        &&& res[i]->0.node().coherent_at((depth - 1) as nat)
                        &&& res[i]->0.node().view_tree_at((depth - 1) as nat) == child
                    },
                    None => res[i] is None,
                },
        decreases depth, children.len(),
    {
        if children.len() == 0 {
            Seq::tracked_empty()
        } else {
            let ghost old_children = children;
            let tracked mut children = children;
            let tracked head = children.tracked_pop_front();
            let tracked mut rest = Self::tracked_cells_from_children(children, depth);
            let tracked wrapped = match head {
                Some(child) => {
                    let tracked node = Self::tracked_from_tree_at(child, (depth - 1) as nat);
                    Some(SubtreeLock::tracked_new(node))
                },
                None => None,
            };
            rest.tracked_push_front(wrapped);
            assert forall|i: int|
                0 <= i < old_children.len() implies match #[trigger] old_children[i] {
                Some(child) => {
                    &&& rest[i] matches Some(lock)
                    &&& rest[i]->0.stable() == child.value().stable()
                    &&& !rest[i]->0.is_vacant()
                    &&& rest[i]->0.node().value() == child.value()
                    &&& rest[i]->0.node().level() == child.level()
                    &&& rest[i]->0.node().inv()
                    &&& rest[i]->0.node().fully_locked_at((depth - 1) as nat)
                    &&& rest[i]->0.node().coherent_at((depth - 1) as nat)
                    &&& rest[i]->0.node().view_tree_at((depth - 1) as nat) == child
                },
                None => rest[i] is None,
            } by {
                if i > 0 {
                    assert(old_children.drop_first()[i - 1] == old_children[i]);
                }
            }
            rest
        }
    }

    /// Rebuilds a subtree in the resource world from a plain [`TreeNode`].
    ///
    /// Every cell in the result is freshly allocated, so no [`Loc`] from a
    /// subtree that was previously dissolved is recovered: a round trip out of
    /// and back into the resource world does not preserve cell identity.
    pub proof fn tracked_from_tree(tracked tree: TreeNode<T, N, L>) -> (tracked res: Self)
        requires
            tree.inv(),
        ensures
            res.value() == tree.value(),
            res.level() == tree.level(),
            res.inv(),
            res.fully_locked(),
            res.coherent(),
            res.view_tree() == tree,
    {
        let ghost level = tree.level();
        Self::tracked_from_tree_at(tree, (L - level) as nat)
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize> SubtreeLock<T, N, L> {
    /// Returns a linear ghost tree to the resource world behind a fresh cell.
    ///
    /// The inverse of [`Self::tracked_into_tree`] up to cell identity: the
    /// resulting lock, and every cell beneath it, is new.
    pub proof fn tracked_from_tree(tracked tree: TreeNode<T, N, L>) -> (tracked res: Self)
        requires
            tree.inv(),
        ensures
            !res.is_vacant(),
            res.stable() == tree.value().stable(),
            res.node().inv(),
            res.node().fully_locked(),
            res.node().coherent(),
            res.node().view_tree() == tree,
    {
        let tracked node = NodeResource::tracked_from_tree(tree);
        Self::tracked_new(node)
    }
}

} // verus!
