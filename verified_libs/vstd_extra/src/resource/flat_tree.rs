//! Trees of independently locked nodes, assembled into a ghost tree on demand.
//!
//! # Relation to [`crate::resource::tree`]
//!
//! [`crate::resource::tree`] nests each child's cell inside its parent's
//! contents, so checking out or returning a node needs `&mut` access through
//! the parent. That does not match a page table, where every node has its own
//! physical lock word that a thread takes and releases without touching the
//! parent:
//!
//! - A cursor may lock a mid-level node `C` (reached lock-free under RCU)
//!   while another cursor locks `C`'s parent `P` and then waits on `C`. When
//!   the first cursor unlocks `C`, `C`'s cell must go back to `C`'s own lock;
//!   it cannot be inside the second cursor's hold on `P`.
//! - A node can be detached from its parent (made stray) while another thread
//!   still reaches it and locks it.
//!
//! So here the cells are *flat*: a [`NodeCell`] lives in its own node's
//! [`NodeLock`], and a parent refers to a child only by the child's
//! [`LockedValue::Key`], which the parent's value already determines (for a
//! page table: the physical address in the PTE). Locking a node is one
//! operation on one lock, at any level, with no dependence on the parent.
//!
//! # Assembling a subtree
//!
//! A thread that has locked a node and some of its descendants holds their
//! cells, and may graft them into an ordinary [`TreeNode`] whose values are
//! the cells themselves ([`LockedTree`]). [`tree_wf`] says each grafted child
//! is the one its parent's value points to, so the result is a faithful
//! picture of that part of the shared tree, and every `ghost_tree` lemma
//! applies to it. [`complete`] says every child the values point to has been
//! grafted, i.e. the thread holds the whole subtree.
//!
//! Disassembly ([`tracked_detach`], [`tracked_into_cell`]) hands back the very
//! same cells, so each one can be returned to its own lock: unlike
//! `tree::SubtreeLock::tracked_from_tree`, no identity is lost on the way
//! back.
//!
//! # What lives where
//!
//! | piece                          | where                                     |
//! |--------------------------------|-------------------------------------------|
//! | identity (`loc`, level, key, consts) | the lock's constant, [`LockConst`]  |
//! | contents (`T`)                 | the [`NodeCell`], inside the lock or held  |
//! | parent→child edge              | [`LockedValue::child_key`] of the parent's `T` |
//!
//! # Not covered here
//!
//! Reading a node without its lock (the RCU read side), and the lifetime
//! argument that a key read from a parent still names a live node with the
//! same lock. Both belong to the client: in a page table, the parent's PTE
//! holds a reference to the child, so while the parent is locked the child's
//! metadata slot, and therefore its lock constant, cannot change.
use crate::ghost_tree::TreeNode;
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::ghost_resource::excl::UniqueToken;
use core::marker::PhantomData;
use vstd::atomic_ghost::{AtomicBool, AtomicInvariantPredicate};
use vstd::atomic_with_ghost;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// The contents of a lockable tree node.
pub trait LockedValue: Sized {
    /// How a parent names a child, e.g. the physical address of a page-table
    /// node. Fixed for the node's lifetime.
    type Key;

    /// Further identity that a parent does not see, e.g. the ids of the
    /// permissions inside the value. Fixed for the node's lifetime.
    type Consts;

    spec fn key(self) -> Self::Key;

    spec fn consts(self) -> Self::Consts;

    /// Which node, if any, child slot `i` points to.
    spec fn child_key(self, i: int) -> Option<Self::Key>;

    /// Node-local invariant at tree depth `level`, required whenever the node
    /// is unlocked.
    spec fn inv(self, level: nat) -> bool;
}

/// The constant of a [`NodeLock`]: everything about a node that is fixed for
/// its lifetime.
pub ghost struct LockConst<K, C> {
    pub loc: Loc,
    pub level: nat,
    pub key: K,
    pub consts: C,
}

/// The contents of one node: its value, plus a unique token whose location
/// ties the cell to exactly one lock.
pub tracked struct NodeCell<T: LockedValue, const N: usize, const L: usize> {
    tracked token: UniqueToken,
    tracked value: T,
    ghost level: nat,
}

impl<T: LockedValue, const N: usize, const L: usize> NodeCell<T, N, L> {
    pub closed spec fn loc(self) -> Loc {
        self.token.id()
    }

    pub closed spec fn value(self) -> T {
        self.value
    }

    pub closed spec fn level(self) -> nat {
        self.level
    }

    pub open spec fn key(self) -> T::Key {
        self.value().key()
    }

    /// The constant of the lock this cell belongs to.
    pub open spec fn lock_const(self) -> LockConst<T::Key, T::Consts> {
        LockConst {
            loc: self.loc(),
            level: self.level(),
            key: self.value().key(),
            consts: self.value().consts(),
        }
    }

    /// What must hold for the cell to be put back into its lock.
    pub open spec fn inv_cell(self) -> bool {
        &&& self.value().inv(self.level())
        &&& self.level() < L
        &&& self.level() + 1 == L ==> forall|i: int|
            0 <= i < N ==> (#[trigger] self.value().child_key(i)) is None
    }

    /// Creates the cell of a fresh node, with a fresh lock identity.
    pub proof fn tracked_new(tracked value: T, level: nat) -> (tracked res: Self)
        ensures
            res.value() == value,
            res.level() == level,
    {
        NodeCell { token: UniqueToken::alloc(()), value, level }
    }

    pub proof fn tracked_borrow_value(tracked &self) -> (tracked res: &T)
        returns
            self.value(),
    {
        &self.value
    }

    /// Mutably borrows the value. To put the cell back into its lock the
    /// caller must keep [`LockedValue::key`] and [`LockedValue::consts`]
    /// unchanged and restore [`Self::inv_cell`].
    pub proof fn tracked_borrow_mut_value(tracked &mut self) -> (tracked res: &mut T)
        ensures
            *res == old(self).value(),
            final(self).value() == *final(res),
            final(self).loc() == old(self).loc(),
            final(self).level() == old(self).level(),
    {
        &mut self.value
    }

    /// Takes the value out of the cell, discarding the lock identity. The
    /// value can then no longer be returned to its lock.
    pub proof fn tracked_into_value(tracked self) -> (tracked res: T)
        ensures
            res == self.value(),
    {
        self.value
    }

    /// Two cells never share a lock identity.
    pub proof fn lemma_distinct(tracked &mut self, tracked other: &Self)
        ensures
            *final(self) == *old(self),
            final(self).loc() != other.loc(),
    {
        self.token.validate_with_other(&other.token);
    }
}

/// Atomic invariant of a [`NodeLock`]: when unlocked, the lock holds the cell
/// whose identity is the lock's constant.
pub struct CellPred<T, const N: usize, const L: usize>(PhantomData<T>);

impl<T: LockedValue, const N: usize, const L: usize> AtomicInvariantPredicate<
    LockConst<T::Key, T::Consts>,
    bool,
    Option<NodeCell<T, N, L>>,
> for CellPred<T, N, L> {
    open spec fn atomic_inv(
        k: LockConst<T::Key, T::Consts>,
        locked: bool,
        g: Option<NodeCell<T, N, L>>,
    ) -> bool {
        match g {
            None => locked,
            Some(cell) => {
                &&& !locked
                &&& cell.lock_const() == k
                &&& cell.inv_cell()
            },
        }
    }
}

/// The lock of one node. Locking yields the node's [`NodeCell`]; no other
/// node's lock is involved.
pub struct NodeLock<T: LockedValue, const N: usize, const L: usize> {
    atomic: AtomicBool<LockConst<T::Key, T::Consts>, Option<NodeCell<T, N, L>>, CellPred<T, N, L>>,
}

impl<T: LockedValue, const N: usize, const L: usize> NodeLock<T, N, L> {
    /// The identity of the node this lock protects.
    pub closed spec fn id(&self) -> LockConst<T::Key, T::Consts> {
        self.atomic.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        self.atomic.well_formed()
    }

    /// Creates an unlocked lock holding `cell`.
    pub fn new(Tracked(cell): Tracked<NodeCell<T, N, L>>) -> (res: Self)
        requires
            cell.inv_cell(),
        ensures
            res.wf(),
            res.id() == cell.lock_const(),
    {
        let ghost k = cell.lock_const();
        NodeLock { atomic: AtomicBool::new(Ghost(k), false, Tracked(Some(cell))) }
    }

    /// Acquires the lock and returns the node's cell.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (res: Tracked<NodeCell<T, N, L>>)
        requires
            self.wf(),
        ensures
            res@.lock_const() == self.id(),
            res@.inv_cell(),
    {
        let tracked mut got: Option<NodeCell<T, N, L>> = None;
        loop
            invariant_except_break
                got is None,
            invariant
                self.wf(),
            ensures
                got matches Some(c) && c.lock_const() == self.id() && c.inv_cell(),
        {
            let res = atomic_with_ghost! {
                self.atomic => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        got = Some(g.tracked_take());
                    }
                }
            };
            if res.is_ok() {
                break;
            }
        }
        Tracked(got.tracked_unwrap())
    }

    /// Releases the lock, returning the node's cell to it.
    ///
    /// The cell's identity says which lock it goes to, so the caller needs
    /// nothing from the node's parent.
    pub fn unlock(&self, Tracked(cell): Tracked<NodeCell<T, N, L>>)
        requires
            self.wf(),
            cell.lock_const() == self.id(),
            cell.inv_cell(),
    {
        let tracked mut cell = cell;
        atomic_with_ghost! {
            self.atomic => store(false);
            ghost g => {
                // The lock cannot already hold a cell: it would have the same
                // identity as ours.
                if g is Some {
                    let tracked other = g.tracked_take();
                    cell.lemma_distinct(&other);
                }
                g = Some(cell);
            }
        }
    }
}

/// A subtree of held cells, as an ordinary ghost tree.
pub type LockedTree<T, const N: usize, const L: usize> = TreeNode<NodeCell<T, N, L>, N, L>;

impl<T: LockedValue, const N: usize, const L: usize> Inv for NodeCell<T, N, L> {
    open spec fn inv(self) -> bool {
        true
    }
}

/// The structural relations are carried by [`tree_wf`] rather than by
/// [`TreeNodeValue`], whose default-value lemmas rule out an edge relation
/// that depends on the parent's contents (as the page table's `EntryOwner`
/// does too).
impl<T: LockedValue, const N: usize, const L: usize> TreeNodeValue<L> for NodeCell<T, N, L> {
    closed spec fn default(lv: nat) -> Self {
        NodeCell { token: arbitrary(), value: arbitrary(), level: lv }
    }

    proof fn lemma_default_preserves_inv() {
    }

    open spec fn la_inv(self, lv: nat) -> bool {
        self.level() == lv
    }

    proof fn lemma_default_preserves_la_inv() {
    }

    open spec fn rel_children(self, index: int, child: Option<Self>) -> bool {
        true
    }

    proof fn lemma_default_preserves_rel_children(self, lv: nat) {
    }
}

/// Every cell is unlockable, and every grafted child is the node its parent's
/// value points to. Children the parent points to may be missing: they are in
/// their own locks, or held by someone else.
pub open spec fn tree_wf_at<T: LockedValue, const N: usize, const L: usize>(
    t: LockedTree<T, N, L>,
    depth: nat,
) -> bool
    decreases depth,
{
    &&& t.inv()
    &&& t.value().inv_cell()
    &&& depth > 0 ==> forall|i: int|
        0 <= i < N && #[trigger] t.has_child(i) ==> {
            &&& t.value().value().child_key(i) == Some(t.child(i).value().key())
            &&& tree_wf_at(t.child(i), (depth - 1) as nat)
        }
}

pub open spec fn tree_wf<T: LockedValue, const N: usize, const L: usize>(
    t: LockedTree<T, N, L>,
) -> bool {
    tree_wf_at(t, (L - t.level()) as nat)
}

/// Every child that some value in the tree points to has been grafted: the
/// holder has the whole subtree.
pub open spec fn complete_at<T: LockedValue, const N: usize, const L: usize>(
    t: LockedTree<T, N, L>,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 ==> forall|i: int|
        0 <= i < N ==> {
            &&& (#[trigger] t.value().value().child_key(i) is Some <==> t.has_child(i))
            &&& t.has_child(i) ==> complete_at(t.child(i), (depth - 1) as nat)
        }
}

pub open spec fn complete<T: LockedValue, const N: usize, const L: usize>(
    t: LockedTree<T, N, L>,
) -> bool {
    complete_at(t, (L - t.level()) as nat)
}

proof fn tracked_none_seq<A>(n: nat) -> (tracked res: Seq<Option<A>>)
    ensures
        res == Seq::new(n, |i| None::<A>),
    decreases n,
{
    if n == 0 {
        let tracked res = Seq::tracked_empty();
        assert(res =~= Seq::new(n, |i| None::<A>));
        res
    } else {
        let tracked mut res = tracked_none_seq((n - 1) as nat);
        res.tracked_push(None);
        assert(res =~= Seq::new(n, |i| None::<A>));
        res
    }
}

/// A held cell as a one-node tree.
pub proof fn tracked_leaf<T: LockedValue, const N: usize, const L: usize>(
    tracked cell: NodeCell<T, N, L>,
) -> (tracked res: LockedTree<T, N, L>)
    requires
        N > 0,
        cell.inv_cell(),
    ensures
        tree_wf(res),
        res.value() == cell,
        res.level() == cell.level(),
        forall|i: int| 0 <= i < N ==> !#[trigger] res.has_child(i),
{
    let ghost lv = cell.level();
    let tracked children = tracked_none_seq(N as nat);
    let tracked res = LockedTree::<T, N, L>::tracked_new(cell, lv, children);
    assert(res.inv());
    res
}

/// Grafts a held child subtree under slot `i` of a held parent subtree.
///
/// The child must be the node the parent points to at `i`, which the caller
/// knows because it found the child's lock by following the parent's value.
pub proof fn tracked_graft<T: LockedValue, const N: usize, const L: usize>(
    tracked parent: LockedTree<T, N, L>,
    i: int,
    tracked child: LockedTree<T, N, L>,
) -> (tracked res: LockedTree<T, N, L>)
    requires
        tree_wf(parent),
        tree_wf(child),
        0 <= i < N,
        !parent.has_child(i),
        child.level() == parent.level() + 1,
        parent.value().value().child_key(i) == Some(child.value().key()),
    ensures
        res == parent.insert(i, child),
        tree_wf(res),
{
    let ghost depth = (L - parent.level()) as nat;
    let ghost old_children = parent.children();
    let ghost lv = parent.level();
    let tracked (value, mut children) = parent.tracked_into_parts();
    let tracked _ = children.tracked_remove(i);
    children.tracked_insert(i, Some(child));
    assert(children =~= old_children.update(i, Some(child)));
    let tracked res = LockedTree::<T, N, L>::tracked_new(value, lv, children);
    assert(res == parent.insert(i, child));
    assert(res.inv());
    assert forall|j: int| 0 <= j < N && #[trigger] res.has_child(j) implies {
        &&& res.value().value().child_key(j) == Some(res.child(j).value().key())
        &&& tree_wf_at(res.child(j), (depth - 1) as nat)
    } by {
        if j != i {
            assert(parent.has_child(j));
        }
    }
    res
}

/// Detaches the child subtree at slot `i`, returning `(parent, child)`.
pub proof fn tracked_detach<T: LockedValue, const N: usize, const L: usize>(
    tracked parent: LockedTree<T, N, L>,
    i: int,
) -> (tracked res: (LockedTree<T, N, L>, LockedTree<T, N, L>))
    requires
        tree_wf(parent),
        0 <= i < N,
        parent.has_child(i),
    ensures
        res.0 == parent.remove(i),
        res.1 == parent.child(i),
        tree_wf(res.0),
        tree_wf(res.1),
        res.1.level() == parent.level() + 1,
        parent.value().value().child_key(i) == Some(res.1.value().key()),
{
    let ghost depth = (L - parent.level()) as nat;
    let ghost old_children = parent.children();
    let ghost lv = parent.level();
    let tracked (value, mut children) = parent.tracked_into_parts();
    let tracked child = children.tracked_remove(i).tracked_unwrap();
    children.tracked_insert(i, None);
    assert(children =~= old_children.update(i, None));
    let tracked rest = LockedTree::<T, N, L>::tracked_new(value, lv, children);
    assert(rest == parent.remove(i));
    assert(rest.inv());
    assert forall|j: int| 0 <= j < N && #[trigger] rest.has_child(j) implies {
        &&& rest.value().value().child_key(j) == Some(rest.child(j).value().key())
        &&& tree_wf_at(rest.child(j), (depth - 1) as nat)
    } by {
        assert(parent.has_child(j));
    }
    (rest, child)
}

/// Turns a childless held tree back into its cell, ready to be unlocked.
pub proof fn tracked_into_cell<T: LockedValue, const N: usize, const L: usize>(
    tracked t: LockedTree<T, N, L>,
) -> (tracked res: NodeCell<T, N, L>)
    requires
        tree_wf(t),
        forall|i: int| 0 <= i < N ==> !#[trigger] t.has_child(i),
    ensures
        res == t.value(),
        res.inv_cell(),
{
    let tracked (value, _children) = t.tracked_into_parts();
    value
}

} // verus!
