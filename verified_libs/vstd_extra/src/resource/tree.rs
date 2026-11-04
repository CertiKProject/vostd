//! Shared ghost trees whose subtrees are locked with counting permissions.
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
//! spine with one counting resource per node.
//!
//! # Structure
//!
//! A node's contents live inside the Leaf-style storage protocol of
//! [`CountResource`], and what that pool protects is a [`NodeResource`]: the
//! node's own value together with the *pools of its children*. Pools nest the
//! way nodes do:
//!
//! ```text
//!   SubtreeLock (pool, TOTAL units)
//!     └── NodeResource { value: T, children: [SubtreeLock, ...] }
//!                                              └── NodeResource { ... }
//! ```
//!
//! A pool is in one of three states, and the unit count is what distinguishes
//! them:
//!
//! | state                    | predicate                       | meaning                      |
//! |--------------------------|---------------------------------|------------------------------|
//! | all `TOTAL` units held   | [`SubtreeLock::is_unlocked`]    | writable, nobody reading     |
//! | `k` units issued         | `issued() == k`                 | `k` readers, contents frozen |
//! | contents withdrawn       | [`SubtreeLock::is_vacant`]      | one writer holds the node    |
//!
//! Issuing a unit yields a [`SubtreeRead`]; collecting them all back is the
//! precondition for withdrawing the node as a [`SubtreeWrite`]. That is an
//! ordinary reader-writer lock at one node. The tree structure is what makes
//! it a *subtree* lock:
//!
//! - **Writing descends by withdrawal.** A writer reaches a child only through
//!   the parent's [`NodeResource`], and holding that means the parent's pool is
//!   vacant, which required every one of the parent's units. So a writer
//!   anywhere inside a subtree has passed through the subtree's root pool.
//! - **Hence one unit excludes every writer below it.** A single
//!   [`SubtreeRead`] at the root leaves the root pool short of `TOTAL`, so it
//!   can never be withdrawn, so no descendant can be reached for writing.
//!   [`SubtreeLock::lemma_write_excludes_lease`] is the formal statement at one
//!   node; the hierarchical consequence follows from the nesting above.
//! - **Disjoint subtrees never interfere.** Two children's pools are separate
//!   [`Loc`]s, so locking one says nothing about the other.
//!
//! Acquiring a subtree lock is therefore a single operation on a single token,
//! not a walk that collects one token per node.
//!
//! # Frozen identity vs. protected contents
//!
//! A parent's invariant must survive a child being write-locked, otherwise
//! locking a child would invalidate its ancestors. So a node value is split:
//! [`SharedTreeValue::stable`] projects out the part fixed for the node's
//! lifetime (for a page table: its level and physical address), and
//! [`SharedTreeValue::rel_stable`] is the edge relation over that part alone.
//! [`SubtreeLock`] records its node's frozen identity *outside* the pool, so
//! [`NodeResource::inv_children`] holds in every lock state.
//!
//! The rest — the agreement between a parent's value and a child's full value,
//! [`NodeResource::coherent`] — is exactly what a [`SubtreeWrite`] holder may
//! break. It is not part of [`NodeResource::inv`], and
//! [`SubtreeLock::tracked_write_release`] is what forces identity and level to
//! be restored.
//!
//! # Reading a subtree
//!
//! [`NodeResource::tracked_borrow_descendant`] walks a [`TreePath`] using only
//! shared borrows, so one lease at the root grants read access to the whole
//! subtree for the lease's lifetime. It cannot mint an independent lease on a
//! descendant: that needs `&mut` on the descendant's pool, which is available
//! only from a [`SubtreeWrite`] on its parent. This is the right asymmetry —
//! bumping a child's count without holding the parent is a lock-free operation
//! that needs an atomic, not a ghost borrow (see *Not covered here*).
//!
//! # Reusing the existing specifications
//!
//! [`NodeResource::view_tree`] maps a shared subtree to the pure
//! [`TreeNode`] it currently denotes, with withdrawn children appearing absent,
//! and [`NodeResource::lemma_view_tree_inv`] shows a coherent subtree's view
//! satisfies [`TreeNode::inv`]. Every path lemma in [`crate::ghost_tree`] —
//! `recursive_visit`, `recursive_seek`, `trace`, `on_subtree`, `path_between` —
//! therefore applies unchanged to the shared tree's view.
//!
//! # Wiring to a real lock
//!
//! The pool is ghost state; a client ties it to a physical counter through
//! [`crate::resource_invariant::ResourceInvariant`], whose `inv` relates the
//! atomic's value to [`SubtreeLock::issued`]. The page table's existing
//! reference-count encoding already lines up: `REF_COUNT_UNUSED` is
//! [`SubtreeLock::is_vacant`], `REF_COUNT_UNIQUE` is
//! [`SubtreeLock::is_unlocked`], and `1..REF_COUNT_MAX` is `issued() == k`.
//! `TOTAL` is the counter's capacity, so the bounded count is a feature:
//! unlike the unbounded real fractions of [`crate::rcu_read_lease`], the number
//! of outstanding leases is observable and can be compared against the atomic.
//!
//! # Not covered here
//!
//! Lock-free acquisition of a lease on a node whose parent is not held — the
//! RCU read side — needs each pool to be reachable without its parent, i.e. a
//! registry mapping each node to its pool's [`Loc`] plus an invariant per
//! node. That is a layer above this one: it would pair a
//! `GhostMapAuth<TreePath<N>, Loc>` of pool identities with the nested pools
//! here, and is deliberately left out so that the hierarchical case stays free
//! of a global authority.
use crate::ghost_tree::{TreeNode, TreePath};
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::ghost_resource::count_auth::{Count, CountResource};
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
pub tracked struct NodeResource<
    T: SharedTreeValue<L>,
    const N: usize,
    const L: usize,
    const TOTAL: usize,
> {
    tracked value: T,
    ghost level: nat,
    // Boxed in `Tracked` for the same reason as `ghost_tree::TreeNode`;
    // see https://github.com/verus-lang/verus/issues/2627.
    tracked children: Tracked<Seq<Option<SubtreeLock<T, N, L, TOTAL>>>>,
}

/// The counting authority for the subtree rooted at one node.
pub tracked struct SubtreeLock<
    T: SharedTreeValue<L>,
    const N: usize,
    const L: usize,
    const TOTAL: usize,
> {
    ghost stable: T::Stable,
    tracked pool: CountResource<NodeResource<T, N, L, TOTAL>, TOTAL>,
}

/// One counted read lease on the subtree rooted at one node.
pub tracked struct SubtreeRead<
    T: SharedTreeValue<L>,
    const N: usize,
    const L: usize,
    const TOTAL: usize,
> {
    ghost stable: T::Stable,
    tracked tok: Count<NodeResource<T, N, L, TOTAL>, TOTAL>,
}

/// Exclusive access to the subtree rooted at one node.
pub tracked struct SubtreeWrite<
    T: SharedTreeValue<L>,
    const N: usize,
    const L: usize,
    const TOTAL: usize,
> {
    ghost id: Loc,
    ghost stable: T::Stable,
    ghost level: nat,
    tracked node: NodeResource<T, N, L, TOTAL>,
}

} // verus!
verus! {

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> NodeResource<
    T,
    N,
    L,
    TOTAL,
> {
    /// The lock-protected value stored in this node.
    pub closed spec fn value(self) -> T {
        self.value
    }

    /// The depth of this node below the root.
    pub closed spec fn level(self) -> nat {
        self.level
    }

    /// The locks of this node's children, `None` at absent slots.
    pub closed spec fn children(self) -> Seq<Option<SubtreeLock<T, N, L, TOTAL>>> {
        self.children@
    }

    /// Whether the `i`-th child exists.
    pub open spec fn has_child(self, i: int) -> bool {
        self.children()[i] is Some
    }

    /// The lock of the `i`-th child. Only meaningful when it exists.
    pub open spec fn child(self, i: int) -> SubtreeLock<T, N, L, TOTAL> {
        self.children()[i]->0
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
    /// obligation of the [`SubtreeWrite`] that holds it.
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> SubtreeLock<
    T,
    N,
    L,
    TOTAL,
> {
    /// The resource location identifying this lock.
    pub closed spec fn id(self) -> Loc {
        self.pool.id()
    }

    /// The frozen identity of the locked node.
    pub closed spec fn stable(self) -> T::Stable {
        self.stable
    }

    /// Whether the node is currently withdrawn by a [`SubtreeWrite`].
    pub closed spec fn is_vacant(self) -> bool {
        self.pool.is_resource_vacant()
    }

    /// The locked node. Only meaningful when the node is not withdrawn.
    pub closed spec fn node(self) -> NodeResource<T, N, L, TOTAL> {
        self.pool.resource()
    }

    /// The number of read leases currently outstanding.
    pub closed spec fn issued(self) -> int {
        if self.is_vacant() {
            0
        } else {
            TOTAL - self.pool.frac()
        }
    }

    /// Whether the subtree can be write-locked: present and unleased.
    pub open spec fn is_unlocked(self) -> bool {
        &&& !self.is_vacant()
        &&& self.issued() == 0
    }

    /// The pool is well formed, and a present node carries the frozen
    /// identity this lock advertises to its parent.
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& self.pool.wf()
        &&& !self.pool.is_resource_vacant() ==> self.pool.resource().value().stable() == self.stable
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> NodeResource<
    T,
    N,
    L,
    TOTAL,
> {
    /// Builds a node from its tracked parts.
    pub proof fn tracked_new(
        tracked value: T,
        level: nat,
        tracked children: Seq<Option<SubtreeLock<T, N, L, TOTAL>>>,
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
        Seq<Option<SubtreeLock<T, N, L, TOTAL>>>,
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
    pub proof fn tracked_borrow_child(tracked &self, i: int) -> (tracked res: &SubtreeLock<
        T,
        N,
        L,
        TOTAL,
    >)
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
        &mut SubtreeLock<T, N, L, TOTAL>)
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> SubtreeLock<
    T,
    N,
    L,
    TOTAL,
> {
    /// Creates an unlocked subtree lock holding `node`.
    pub proof fn tracked_new(tracked node: NodeResource<T, N, L, TOTAL>) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            !res.is_vacant(),
            res.node() == node,
            res.stable() == node.value().stable(),
            res.issued() == 0,
            res.is_unlocked(),
    {
        let ghost stable = node.value().stable();
        let tracked pool = CountResource::alloc(node);
        Self { stable, pool }
    }

    /// Borrows the locked node for reading.
    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeResource<T, N, L, TOTAL>)
        requires
            !self.is_vacant(),
        returns
            self.node(),
    {
        self.pool.tracked_borrow()
    }

    /// Acquires one read lease on this subtree.
    ///
    /// The lease is a counting permission: while any lease is outstanding the
    /// node cannot be withdrawn, so every lease observes the same
    /// [`NodeResource`].
    pub proof fn tracked_read_acquire(tracked &mut self) -> (tracked res: SubtreeRead<
        T,
        N,
        L,
        TOTAL,
    >)
        requires
            !old(self).is_vacant(),
            old(self).issued() < TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self).stable() == old(self).stable(),
            final(self).node() == old(self).node(),
            !final(self).is_vacant(),
            final(self).issued() == old(self).issued() + 1,
            res.id() == old(self).id(),
            res.stable() == old(self).stable(),
            res.node() == old(self).node(),
            res.count() == 1,
    {
        use_type_invariant(&*self);
        let ghost stable = self.stable;
        let tracked tok = self.pool.split_one();
        SubtreeRead { stable, tok }
    }

    /// Returns a read lease.
    pub proof fn tracked_read_release(tracked &mut self, tracked lease: SubtreeRead<T, N, L, TOTAL>)
        requires
            old(self).id() == lease.id(),
            !old(self).is_vacant(),
            old(self).issued() >= lease.count(),
        ensures
            final(self).id() == old(self).id(),
            final(self).stable() == old(self).stable(),
            final(self).node() == old(self).node(),
            !final(self).is_vacant(),
            final(self).issued() == old(self).issued() - lease.count(),
    {
        use_type_invariant(&*self);
        self.pool.combine(lease.tok);
    }

    /// Acquires exclusive access to this subtree, withdrawing the node.
    ///
    /// Only possible when no read lease is outstanding, which is what makes
    /// the counting permission a reader-writer lock.
    pub proof fn tracked_write_acquire(tracked &mut self) -> (tracked res: SubtreeWrite<
        T,
        N,
        L,
        TOTAL,
    >)
        requires
            old(self).is_unlocked(),
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
        SubtreeWrite { id: self.pool.id(), stable, level, node }
    }

    /// Releases exclusive access, depositing the node back into the lock.
    ///
    /// The guard must restore the node's frozen identity and level, which is
    /// what lets a parent's [`NodeResource::inv_children`] hold throughout.
    pub proof fn tracked_write_release(
        tracked &mut self,
        tracked guard: SubtreeWrite<T, N, L, TOTAL>,
    )
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
            final(self).is_unlocked(),
            final(self).issued() == 0,
            final(self).node() == guard.node(),
            final(self).node().level() == guard.level(),
            final(self).node().value().stable() == old(self).stable(),
    {
        use_type_invariant(&*self);
        let tracked SubtreeWrite { id: _, stable: _, level: _, node } = guard;
        self.pool.put_resource(node);
    }

    /// `is_unlocked` is exactly "present with no outstanding lease".
    pub proof fn lemma_unlocked_iff(tracked &self)
        ensures
            self.is_unlocked() <==> (!self.is_vacant() && self.issued() == 0),
    {
        use_type_invariant(self);
    }

    /// A write guard and a read lease cannot coexist on one subtree.
    ///
    /// This is the exclusion theorem the whole design rests on. Because a
    /// writer reaches a descendant only by withdrawing its ancestors' nodes in
    /// turn, and withdrawal demands the full count, one lease at the root of a
    /// subtree rules out a writer anywhere beneath it.
    pub proof fn lemma_write_excludes_lease(
        tracked &mut self,
        tracked lease: &SubtreeRead<T, N, L, TOTAL>,
    )
        requires
            old(self).is_vacant(),
        ensures
            *final(self) == *old(self),
            final(self).id() != lease.id(),
    {
        use_type_invariant(&*self);
        self.pool.lemma_vacant_excludes_frac(&lease.tok);
    }

    /// An outstanding read lease rules out write access.
    pub proof fn lemma_lease_blocks_write(
        tracked &self,
        tracked lease: &SubtreeRead<T, N, L, TOTAL>,
    )
        requires
            self.id() == lease.id(),
            !self.is_vacant(),
            self.issued() >= lease.count(),
        ensures
            lease.count() > 0,
            !self.is_unlocked(),
    {
        lease.lemma_count_positive();
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> SubtreeRead<
    T,
    N,
    L,
    TOTAL,
> {
    /// The lock this lease was issued by.
    pub closed spec fn id(self) -> Loc {
        self.tok.id()
    }

    /// The frozen identity of the leased node.
    pub closed spec fn stable(self) -> T::Stable {
        self.stable
    }

    /// The node observed through this lease.
    pub closed spec fn node(self) -> NodeResource<T, N, L, TOTAL> {
        self.tok.resource()
    }

    /// How many counting units this lease holds.
    pub closed spec fn count(self) -> int {
        self.tok.frac()
    }

    /// A lease always holds at least one counting unit.
    pub proof fn lemma_count_positive(tracked &self)
        ensures
            0 < self.count() <= TOTAL,
    {
        self.tok.bounded();
    }

    /// Borrows the leased node. Nothing can mutate it while the lease lives.
    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeResource<T, N, L, TOTAL>)
        returns
            self.node(),
    {
        self.tok.tracked_borrow()
    }

    /// Two leases on the same lock observe the same node.
    pub proof fn lemma_agree(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.node() == other.node(),
    {
        self.tok.agree(&other.tok);
    }
}

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> SubtreeWrite<
    T,
    N,
    L,
    TOTAL,
> {
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
    pub closed spec fn node(self) -> NodeResource<T, N, L, TOTAL> {
        self.node
    }

    /// Borrows the held node.
    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeResource<T, N, L, TOTAL>)
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
        TOTAL,
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> NodeResource<
    T,
    N,
    L,
    TOTAL,
> {
    /// The node reached by following `path`, provided every lock along the way
    /// still holds its node (no writer has withdrawn it).
    pub open spec fn seek(self, path: TreePath<N>) -> Option<NodeResource<T, N, L, TOTAL>>
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
    /// A single read lease on this node therefore grants read access to the
    /// whole subtree: every step down is a shared borrow, so no step can
    /// withdraw a node.
    pub proof fn tracked_borrow_descendant<'a>(tracked &'a self, path: TreePath<N>) -> (tracked res:
        &'a NodeResource<T, N, L, TOTAL>)
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
    pub proof fn tracked_insert_child(
        tracked &mut self,
        i: int,
        tracked lock: SubtreeLock<T, N, L, TOTAL>,
    )
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
        TOTAL,
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> SubtreeLock<
    T,
    N,
    L,
    TOTAL,
> {
    /// Dissolves an unleased, unwithdrawn lock and recovers its node.
    ///
    /// This is the reclamation step: it is admissible exactly when the
    /// counting pool is whole, i.e. no reader holds a lease.
    pub proof fn tracked_into_node(tracked self) -> (tracked res: NodeResource<T, N, L, TOTAL>)
        requires
            self.is_unlocked(),
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> NodeResource<
    T,
    N,
    L,
    TOTAL,
> {
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
    /// part of the tree invariant that a [`SubtreeWrite`] holder is allowed to
    /// break and must restore. A subtree with no writer inside it is coherent,
    /// and only then does its view satisfy [`TreeNode::inv`].
    pub open spec fn coherent_at(self, depth: nat) -> bool
        decreases depth,
    {
        depth > 0 ==> forall|i: int|
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

impl<T: SharedTreeValue<L>, const N: usize, const L: usize, const TOTAL: usize> NodeResource<
    T,
    N,
    L,
    TOTAL,
> {
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
