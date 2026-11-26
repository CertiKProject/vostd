//! A tree whose edges are linear tickets and whose locks live in a global
//! arena.
//!
//! | piece | where |
//! |---|---|
//! | a node's identity | [`NodeId`], fixed at creation |
//! | a node's lock | the [`LockArena`]'s array, at the node's own index |
//! | a node's contents | the [`NodeBundle`], in its lock or held by a thread |
//! | a parent-to-child edge | a [`Parentage`] ticket, inside the parent's bundle |
//! | the shape, as a tree | [`ArenaTree`] — a [`TreeNode`] of [`TreePlace`]s |
//!
//! # The edge is a resource
//!
//! Each node is created with exactly one [`Parentage`] ticket. Installing it
//! into a parent's bundle ([`tracked_install`]) *is* the edge; withdrawing it
//! ([`tracked_remove_edge`]) detaches the node. Because the ticket is
//! exclusive, two global facts hold with nothing stated or stored:
//!
//! - **one parent per node** — the ticket sits in at most one bundle, and
//!   [`Parentage::lemma_unique`] turns two tickets for one node into a
//!   contradiction;
//! - **acyclicity and a depth bound** — [`tracked_install`] demands
//!   `child.level == parent.level + 1`, and levels are fixed at creation and
//!   bounded by `L`.
//!
//! So there is no stored shape and no key-to-lock map to constrain: the shape
//! *is* the distribution of tickets. A withdrawn ticket held by a thread is a
//! stray subtree, so the global picture is a forest with a distinguished root
//! rather than a single tree — which is the honest shape, since a detached
//! node keeps its lock and goes on being lockable.
//!
//! The lock lives in the arena, not in the parent, so a node's lock is
//! acquirable and releasable whatever happens to its edge.
//!
//! # The shape as a tree
//!
//! [`ArenaTree`] is a [`TreeNode`] whose payload names an arena node and
//! records its parentage, and whose [`TreePlace::rel_children`] *is* the
//! parent-child relation — so the tree's own invariant governs parentage.
//! [`shape_of`] projects one out of a [`HeldTree`], and
//! [`lemma_shape_of_inv`] shows the result is well formed.
//!
//! It carries no [`Parentage`] ticket, so it is knowledge of the shape and
//! not permission over it: a snapshot costs nothing to hold, blocks nobody,
//! outlives the locks it was taken from, and may go stale once tickets move.
//! Authority over the shape stays with the tickets.
//!
//! # Acquisition discipline
//!
//! A held [`NodeBundle`] grants read-only access to its value. The only public
//! route to a change is [`tracked_update_root`], which requires an assembled
//! [`HeldTree`] that is [`tree_wf`] and [`complete`] — i.e. the thread holds
//! the whole subtree. It also requires the new value to keep the node's
//! [`NodeValue::consts`] and node-local invariant, which is what lets it
//! re-establish `tree_wf` and `complete` instead of leaving them broken.
//!
//! Installing and removing edges is separate, and needs only the parent's
//! bundle: it is a local operation under the parent's lock, with no claim on
//! the arena and no global invariant to open.
//!
//! # Not finished
//!
//! - **Discovering the shape needs an exec read.** After a bundle goes through
//!   a lock, its contents are no longer predictable — only its identity is.
//!   So a thread cannot learn where a node's children are from the ghost
//!   state alone; it must read them, which means the value must carry a
//!   permission to the memory holding them. That is why
//!   [`NodeLock::new_locked`] exists: a freshly built structure hands its
//!   bundles straight to its first owner. Wiring an exec-readable child
//!   projection into [`NodeValue`], agreeing with the tickets by
//!   [`NodeBundle::inv_bundle`], is the next step.
//! - **Updates are root-only.** [`tracked_update_root`] changes the value at
//!   the root of a held tree; a path-indexed update needs an update-at-path
//!   spec function to state its frame condition.
//!
//! # Not covered here
//!
//! Reaching a node without holding it — the RCU read side — and therefore any
//! argument that an index read from a parent still names a live node. The
//! ticket in the parent keeps the child alive; a lock-free reader holds no
//! ticket, so its claim must be temporal and comes from elsewhere. Nothing
//! here implements `Objective`, so these resources cannot pass through an
//! IRC11 lock.
use crate::ghost_tree::{TreeNode, TreePath};
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::ghost_resource::excl::UniqueToken;
use alloc::vec::Vec;
use core::marker::PhantomData;
use vstd::atomic_ghost::{AtomicBool, AtomicInvariantPredicate};
use vstd::atomic_with_ghost;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// The contents of a lockable node. `C` is identity fixed for the node's
/// lifetime that a parent does not see.
pub trait NodeValue<C>: Sized {
    spec fn consts(self) -> C;

    /// Node-local invariant at tree depth `level`.
    spec fn inv(self, level: nat) -> bool;

    /// The arena index of the node slot `i` points at, as recorded *in the
    /// value* — for a page table, read out of the PTE.
    ///
    /// [`NodeBundle::inv_bundle`] forces this to agree with the slot's
    /// [`Parentage`] ticket, so a holder cannot change where a slot points
    /// without moving the matching ticket.
    spec fn child_index(self, i: int) -> Option<usize>;
}

/// Everything about a node that is fixed for its lifetime.
pub ghost struct NodeId<C> {
    pub bundle_loc: Loc,
    pub ticket_loc: Loc,
    pub level: nat,
    pub index: usize,
    pub consts: C,
}

/// The exclusive right for a node to be some parent's child.
///
/// Minted once, with the node's bundle. Holding it means the node is detached.
pub tracked struct Parentage<C> {
    tracked token: UniqueToken,
    ghost id: NodeId<C>,
}

impl<C> Parentage<C> {
    pub closed spec fn id(self) -> NodeId<C> {
        self.id
    }

    pub closed spec fn loc(self) -> Loc {
        self.token.id()
    }

    pub open spec fn inv_ticket(self) -> bool {
        self.loc() == self.id().ticket_loc
    }

    /// **One parent per node.** Two tickets never name the same node, so a
    /// node cannot be the child of two parents.
    pub proof fn lemma_unique(tracked &mut self, tracked other: &Self)
        requires
            old(self).inv_ticket(),
            other.inv_ticket(),
        ensures
            *final(self) == *old(self),
            final(self).id() != other.id(),
            final(self).loc() != other.loc(),
    {
        self.token.validate_with_other(&other.token);
    }
}

} // verus!
verus! {

/// Everything the lock of one node hands over at once: the node's value, the
/// [`Parentage`] tickets of the children it points to, and a token whose
/// location ties this bundle to that one lock.
pub tracked struct NodeBundle<T: NodeValue<C>, C, const N: usize, const L: usize> {
    tracked token: UniqueToken,
    tracked value: T,
    tracked tickets: Map<int, Parentage<C>>,
    ghost id: NodeId<C>,
    ghost _nl: PhantomData<[(); N]>,
}

impl<T: NodeValue<C>, C, const N: usize, const L: usize> NodeBundle<T, C, N, L> {
    pub closed spec fn id(self) -> NodeId<C> {
        self.id
    }

    pub closed spec fn value(self) -> T {
        self.value
    }

    pub closed spec fn loc(self) -> Loc {
        self.token.id()
    }

    pub closed spec fn tickets(self) -> Map<int, Parentage<C>> {
        self.tickets
    }

    pub open spec fn level(self) -> nat {
        self.id().level
    }

    pub open spec fn index(self) -> usize {
        self.id().index
    }

    /// Whether this node points at a child in slot `i`.
    pub open spec fn has_edge(self, i: int) -> bool {
        self.tickets().contains_key(i)
    }

    /// The node slot `i` points at, if any.
    pub open spec fn edge(self, i: int) -> Option<NodeId<C>> {
        if self.has_edge(i) {
            Some(self.tickets()[i].id())
        } else {
            None
        }
    }

    /// What the lock promises about a bundle at rest.
    pub open spec fn inv_bundle(self) -> bool {
        &&& self.loc() == self.id().bundle_loc
        &&& self.value().consts() == self.id().consts
        &&& self.value().inv(self.level())
        &&& self.level() < L
        &&& forall|i: int|
            #![trigger self.tickets().contains_key(i)]
            self.has_edge(i) ==> {
                &&& 0 <= i < N
                &&& self.tickets()[i].inv_ticket()
                &&& self.tickets()[i].id().level == self.level() + 1
            }
            // A node at the deepest level can have no children, so this survives
            // a trip through the lock -- unlike anything about the value.
        &&& self.level() + 1 == L ==> forall|i: int|
            !#[trigger] self.has_edge(
                i,
            )
            // The value and the tickets agree about every slot. This is what
            // makes a bundle self-describing: its value says where its
            // children are, and the tickets say the same.
        &&& forall|i: int|
            0 <= i < N ==> ((#[trigger] self.value().child_index(i)) is Some <==> self.has_edge(i))
        &&& forall|i: int|
            0 <= i < N && (#[trigger] self.value().child_index(i)) is Some
                ==> self.value().child_index(i) == Some(self.tickets()[i].id().index)
    }

    /// Creates a fresh node at `index`: its bundle, and the one ticket that
    /// makes it someone's child.
    pub proof fn tracked_new(tracked value: T, level: nat, index: usize) -> (tracked res: (
        Self,
        Parentage<C>,
    ))
        requires
            level < L,
            value.inv(level),
            forall|i: int| (#[trigger] value.child_index(i)) is None,
        ensures
            res.0.value() == value,
            res.0.level() == level,
            res.0.index() == index,
            res.0.id() == res.1.id(),
            res.0.inv_bundle(),
            res.1.inv_ticket(),
            forall|i: int| !#[trigger] res.0.has_edge(i),
    {
        let tracked bundle_token = UniqueToken::alloc(());
        let tracked ticket_token = UniqueToken::alloc(());
        let ghost id = NodeId {
            bundle_loc: bundle_token.id(),
            ticket_loc: ticket_token.id(),
            level,
            index,
            consts: value.consts(),
        };
        let tracked bundle = NodeBundle {
            token: bundle_token,
            value,
            tickets: Map::tracked_empty(),
            id,
            _nl: PhantomData,
        };
        let tracked ticket = Parentage { token: ticket_token, id };
        (bundle, ticket)
    }

    /// Reads the value. There is deliberately no `&mut` counterpart: see
    /// [`tracked_update_root`].
    pub proof fn tracked_borrow_value(tracked &self) -> (tracked res: &T)
        returns
            self.value(),
    {
        &self.value
    }

    /// Replaces the value, keeping the bundle's identity and edges.
    proof fn tracked_with_value(tracked self, tracked v: T) -> (tracked res: Self)
        ensures
            res.id() == self.id(),
            res.loc() == self.loc(),
            res.tickets() == self.tickets(),
            res.value() == v,
    {
        let tracked NodeBundle { token, value: _old, tickets, id, _nl } = self;
        NodeBundle { token, value: v, tickets, id, _nl }
    }

    /// Two bundles never share a lock location.
    pub proof fn lemma_distinct(tracked &mut self, tracked other: &Self)
        requires
            old(self).inv_bundle(),
            other.inv_bundle(),
        ensures
            *final(self) == *old(self),
            final(self).loc() != other.loc(),
            final(self).id().bundle_loc != other.id().bundle_loc,
    {
        self.token.validate_with_other(&other.token);
    }
}

/// Installs `child` as this node's slot `i`: the ticket becomes the edge.
///
/// Needing `&mut NodeBundle` means needing the node's lock, so this is a local
/// operation — no claim on the arena, no global invariant opened.
pub proof fn tracked_install<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked parent: &mut NodeBundle<T, C, N, L>,
    i: int,
    tracked child: Parentage<C>,
    tracked new_value: T,
)
    requires
        old(parent).inv_bundle(),
        0 <= i < N,
        old(parent).level() + 1 < L,
        !old(parent).has_edge(i),
        child.inv_ticket(),
        child.id().level == old(parent).level() + 1,
        // The value must record the new edge, and nothing else about it may
        // change: writing the slot and moving the ticket are one step.
        new_value.consts() == old(parent).value().consts(),
        new_value.inv(old(parent).level()),
        new_value.child_index(i) == Some(child.id().index),
        forall|j: int|
            j != i ==> #[trigger] new_value.child_index(j) == old(parent).value().child_index(j),
    ensures
        final(parent).id() == old(parent).id(),
        final(parent).loc() == old(parent).loc(),
        final(parent).value() == new_value,
        final(parent).tickets() == old(parent).tickets().insert(i, child),
        final(parent).edge(i) == Some(child.id()),
        forall|j: int| j != i ==> #[trigger] final(parent).edge(j) == old(parent).edge(j),
        final(parent).inv_bundle(),
{
    parent.tickets.tracked_insert(i, child);
    parent.value = new_value;
    assert(parent.tickets() =~= old(parent).tickets().insert(i, child));
}

/// Withdraws slot `i`'s edge, handing back the child's ticket. The child is
/// now detached; its lock and bundle are untouched.
pub proof fn tracked_remove_edge<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked parent: &mut NodeBundle<T, C, N, L>,
    i: int,
    tracked new_value: T,
) -> (tracked res: Parentage<C>)
    requires
        old(parent).inv_bundle(),
        old(parent).has_edge(i),
        new_value.consts() == old(parent).value().consts(),
        new_value.inv(old(parent).level()),
        new_value.child_index(i) is None,
        forall|j: int|
            j != i ==> #[trigger] new_value.child_index(j) == old(parent).value().child_index(j),
    ensures
        res == old(parent).tickets()[i],
        res.inv_ticket(),
        res.id() == old(parent).edge(i)->0,
        final(parent).id() == old(parent).id(),
        final(parent).loc() == old(parent).loc(),
        final(parent).value() == new_value,
        final(parent).tickets() == old(parent).tickets().remove(i),
        !final(parent).has_edge(i),
        forall|j: int| j != i ==> #[trigger] final(parent).edge(j) == old(parent).edge(j),
        final(parent).inv_bundle(),
{
    let tracked res = parent.tickets.tracked_remove(i);
    parent.value = new_value;
    assert(parent.tickets() =~= old(parent).tickets().remove(i));
    res
}

} // verus!
verus! {

pub struct BundlePred<T, C, const N: usize, const L: usize>(PhantomData<(T, C)>);

impl<T: NodeValue<C>, C, const N: usize, const L: usize> AtomicInvariantPredicate<
    NodeId<C>,
    bool,
    Option<NodeBundle<T, C, N, L>>,
> for BundlePred<T, C, N, L> {
    open spec fn atomic_inv(k: NodeId<C>, locked: bool, g: Option<NodeBundle<T, C, N, L>>) -> bool {
        match g {
            None => locked,
            Some(bundle) => !locked && bundle.id() == k && bundle.inv_bundle(),
        }
    }
}

/// The lock of one node. Locking hands over that node's bundle and nothing else.
pub struct NodeLock<T: NodeValue<C>, C, const N: usize, const L: usize> {
    atomic: AtomicBool<NodeId<C>, Option<NodeBundle<T, C, N, L>>, BundlePred<T, C, N, L>>,
}

impl<T: NodeValue<C>, C, const N: usize, const L: usize> NodeLock<T, C, N, L> {
    pub closed spec fn id(&self) -> NodeId<C> {
        self.atomic.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        self.atomic.well_formed()
    }

    pub fn new(Tracked(bundle): Tracked<NodeBundle<T, C, N, L>>) -> (res: Self)
        requires
            bundle.inv_bundle(),
        ensures
            res.wf(),
            res.id() == bundle.id(),
    {
        let ghost k = bundle.id();
        NodeLock { atomic: AtomicBool::new(Ghost(k), false, Tracked(Some(bundle))) }
    }

    /// Creates a lock already in the locked state, holding no bundle.
    ///
    /// Lets a freshly built structure hand its bundles straight to its first
    /// owner: after locking, a bundle's contents are no longer predictable, so
    /// there would be no other way to start from known-edgeless bundles.
    pub fn new_locked(Ghost(id): Ghost<NodeId<C>>) -> (res: Self)
        ensures
            res.wf(),
            res.id() == id,
    {
        NodeLock { atomic: AtomicBool::new(Ghost(id), true, Tracked(None)) }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (res: Tracked<NodeBundle<T, C, N, L>>)
        requires
            self.wf(),
        ensures
            res@.id() == self.id(),
            res@.inv_bundle(),
    {
        let tracked mut got: Option<NodeBundle<T, C, N, L>> = None;
        loop
            invariant_except_break
                got is None,
            invariant
                self.wf(),
            ensures
                got matches Some(c) && c.id() == self.id() && c.inv_bundle(),
        {
            let res =
                atomic_with_ghost! {
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

    pub fn unlock(&self, Tracked(bundle): Tracked<NodeBundle<T, C, N, L>>)
        requires
            self.wf(),
            bundle.id() == self.id(),
            bundle.inv_bundle(),
    {
        let tracked mut bundle = bundle;
        atomic_with_ghost! {
            self.atomic => store(false);
            ghost g => {
                if g is Some {
                    let tracked other = g.tracked_take();
                    bundle.lemma_distinct(&other);
                }
                g = Some(bundle);
            }
        }
    }
}

/// The locks, in a global array indexed by node index.
///
/// There is no shape here: the arena only says which lock is where. The tree
/// is carried by the [`Parentage`] tickets inside the bundles.
pub struct LockArena<T: NodeValue<C>, C, const N: usize, const L: usize> {
    locks: Vec<NodeLock<T, C, N, L>>,
}

impl<T: NodeValue<C>, C, const N: usize, const L: usize> LockArena<T, C, N, L> {
    pub closed spec fn locks(&self) -> Seq<NodeLock<T, C, N, L>> {
        self.locks@
    }

    pub open spec fn wf(&self) -> bool {
        &&& N > 0
        &&& L > 0
        &&& forall|i: int|
            0 <= i < self.locks().len() ==> {
                &&& (#[trigger] self.locks()[i]).id().index == i
                &&& self.locks()[i].wf()
            }
    }

    /// The identity the arena records at `index`.
    pub open spec fn id_of(&self, index: usize) -> NodeId<C> {
        self.locks()[index as int].id()
    }

    /// Whether `id` is the identity this arena holds a lock for.
    pub open spec fn holds(&self, id: NodeId<C>) -> bool {
        &&& id.index < self.locks().len()
        &&& self.id_of(id.index) == id
    }

    pub fn new(locks: Vec<NodeLock<T, C, N, L>>) -> (res: Self)
        requires
            N > 0,
            L > 0,
            forall|i: int|
                0 <= i < locks@.len() ==> {
                    &&& (#[trigger] locks@[i]).id().index == i
                    &&& locks@[i].wf()
                },
        ensures
            res.wf(),
            res.locks() == locks@,
    {
        LockArena { locks }
    }

    /// Acquires the lock of the node `id` names, and takes its bundle.
    ///
    /// Only `&self` is needed, so threads may do this concurrently for
    /// different nodes, and a node's lock is reached with no claim on its
    /// parent.
    pub fn lock(&self, index: usize, Ghost(id): Ghost<NodeId<C>>) -> (res: Tracked<
        NodeBundle<T, C, N, L>,
    >)
        requires
            self.wf(),
            self.holds(id),
            id.index == index,
        ensures
            res@.id() == id,
            res@.inv_bundle(),
    {
        self.locks[index].lock()
    }

    /// Releases a bundle to its own lock. Nothing about the parent is consulted,
    /// so a detached node releases exactly as an attached one does.
    pub fn unlock(&self, index: usize, Tracked(bundle): Tracked<NodeBundle<T, C, N, L>>)
        requires
            self.wf(),
            self.holds(bundle.id()),
            bundle.index() == index,
            bundle.inv_bundle(),
    {
        self.locks[index].unlock(Tracked(bundle));
    }
}

} // verus!
verus! {

/// A subtree of held bundles, as an ordinary ghost tree.
pub type HeldTree<T, C, const N: usize, const L: usize> = TreeNode<NodeBundle<T, C, N, L>, N, L>;

impl<T: NodeValue<C>, C, const N: usize, const L: usize> Inv for NodeBundle<T, C, N, L> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<T: NodeValue<C>, C, const N: usize, const L: usize> TreeNodeValue<L> for NodeBundle<
    T,
    C,
    N,
    L,
> {
    open spec fn la_inv(self, lv: nat) -> bool {
        self.level() == lv
    }

    /// **The edge relation.** A present child is the node this bundle's
    /// ticket at that slot names, so [`TreeNode::inv`] on a [`HeldTree`]
    /// governs the tickets directly.
    open spec fn rel_children(self, index: int, child: Option<Self>) -> bool {
        match child {
            Some(c) => self.edge(index) == Some(c.id()),
            None => true,
        }
    }
}

/// Every bundle in the tree is unlockable.
///
/// The *edges* are not mentioned here: [`NodeBundle::rel_children`] states
/// them, so [`TreeNode::inv`] already governs them. All this adds is that
/// each bundle satisfies [`NodeBundle::inv_bundle`], which is what rules out
/// the synthetic node and so turns `rel_children` into the ticket relation —
/// see [`lemma_tree_edge`].
pub open spec fn tree_wf_at<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    depth: nat,
) -> bool
    decreases depth,
{
    &&& t.inv()
    &&& t.value().inv_bundle()
    &&& depth > 0 ==> forall|i: int|
        0 <= i < N && #[trigger] t.has_child(i) ==> tree_wf_at(t.child(i), (depth - 1) as nat)
}

/// The edge relation, recovered from the tree's own invariant.
pub proof fn lemma_tree_edge<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    i: int,
)
    requires
        tree_wf(t),
        0 <= i < N,
        t.has_child(i),
        t.value().level() + 1 < L,
    ensures
        t.value().edge(i) == Some(t.child(i).value().id()),
        t.child(i).value().level() == t.value().level() + 1,
{
    assert(t.inv());
    assert(t.value().la_inv(t.level()));
    assert(t.inv_children());
}

pub open spec fn tree_wf<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
) -> bool {
    tree_wf_at(t, (L - t.value().level()) as nat)
}

/// Every edge below here has been grafted: the thread holds the whole
/// subtree, which is what licenses modification.
pub open spec fn complete_at<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 ==> forall|i: int|
        0 <= i < N ==> {
            &&& (#[trigger] t.value().has_edge(i) <==> t.has_child(i))
            &&& t.has_child(i) ==> complete_at(t.child(i), (depth - 1) as nat)
        }
}

pub open spec fn complete<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
) -> bool {
    complete_at(t, (L - t.value().level()) as nat)
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

/// A single held bundle, as a one-node held tree.
pub proof fn tracked_leaf<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked bundle: NodeBundle<T, C, N, L>,
) -> (tracked res: HeldTree<T, C, N, L>)
    requires
        N > 0,
        bundle.inv_bundle(),
    ensures
        res.value() == bundle,
        res.level() == bundle.level(),
        forall|i: int| 0 <= i < N ==> !#[trigger] res.has_child(i),
        tree_wf(res),
{
    let ghost lv = bundle.level();
    let tracked children = tracked_none_seq(N as nat);
    let tracked res = HeldTree::<T, C, N, L>::tracked_new(bundle, lv, children);
    assert(res.inv());
    res
}

/// A held tree with no children and no edges is a complete collection.
pub proof fn lemma_leaf_complete<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
)
    requires
        forall|i: int| 0 <= i < N ==> !#[trigger] t.has_child(i),
        forall|i: int| 0 <= i < N ==> !#[trigger] t.value().has_edge(i),
    ensures
        complete(t),
{
}

/// Grafts a held child subtree under slot `i` of a held parent subtree.
///
/// The parent's ticket at `i` must name the child, which the caller knows
/// because it found the child's lock by following that ticket.
pub proof fn tracked_graft<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked parent: HeldTree<T, C, N, L>,
    i: int,
    tracked child: HeldTree<T, C, N, L>,
) -> (tracked res: HeldTree<T, C, N, L>)
    requires
        tree_wf(parent),
        tree_wf(child),
        0 <= i < N,
        !parent.has_child(i),
        parent.value().edge(i) == Some(child.value().id()),
        child.value().level() == parent.value().level() + 1,
    ensures
        res == parent.insert(i, child),
        tree_wf(res),
{
    let ghost depth = (L - parent.value().level()) as nat;
    let ghost old_children = parent.children();
    let ghost lv = parent.level();
    let tracked (value, mut children) = parent.tracked_into_parts();
    let tracked _ = children.tracked_remove(i);
    children.tracked_insert(i, Some(child));
    assert(children =~= old_children.update(i, Some(child)));
    let tracked res = HeldTree::<T, C, N, L>::tracked_new(value, lv, children);
    assert(res == parent.insert(i, child));
    assert(res.inv());
    assert forall|j: int| 0 <= j < N && #[trigger] res.has_child(j) implies tree_wf_at(
        res.child(j),
        (depth - 1) as nat,
    ) by {
        if j != i {
            assert(parent.has_child(j));
        }
    }
    res
}

/// Detaches the held child subtree at slot `i`. The *edge* is untouched: the
/// parent's ticket still names the child, so it can be grafted back.
pub proof fn tracked_detach<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked parent: HeldTree<T, C, N, L>,
    i: int,
) -> (tracked res: (HeldTree<T, C, N, L>, HeldTree<T, C, N, L>))
    requires
        tree_wf(parent),
        0 <= i < N,
        parent.has_child(i),
    ensures
        res.0 == parent.remove(i),
        res.1 == parent.child(i),
        tree_wf(res.0),
        tree_wf(res.1),
        parent.value().edge(i) == Some(res.1.value().id()),
        res.1.value().level() == parent.value().level() + 1,
{
    let ghost depth = (L - parent.value().level()) as nat;
    let ghost old_children = parent.children();
    let ghost lv = parent.level();
    let tracked (value, mut children) = parent.tracked_into_parts();
    let tracked child = children.tracked_remove(i).tracked_unwrap();
    children.tracked_insert(i, None);
    assert(children =~= old_children.update(i, None));
    let tracked rest = HeldTree::<T, C, N, L>::tracked_new(value, lv, children);
    assert(rest == parent.remove(i));
    assert(rest.inv());
    assert forall|j: int| 0 <= j < N && #[trigger] rest.has_child(j) implies tree_wf_at(
        rest.child(j),
        (depth - 1) as nat,
    ) by {
        assert(parent.has_child(j));
    }
    assert(parent.inv());
    assert(parent.value().la_inv(parent.level()));
    assert(child.level() == parent.level() + 1);
    assert(child.inv());
    assert(child.value().la_inv(child.level()));
    assert(tree_wf_at(child, (depth - 1) as nat));
    (rest, child)
}

/// Turns a childless held tree back into its bundle, ready to be unlocked.
pub proof fn tracked_into_bundle<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked t: HeldTree<T, C, N, L>,
) -> (tracked res: NodeBundle<T, C, N, L>)
    requires
        tree_wf(t),
        forall|i: int| 0 <= i < N ==> !#[trigger] t.has_child(i),
    ensures
        res == t.value(),
        res.inv_bundle(),
{
    let tracked (value, _children) = t.tracked_into_parts();
    value
}

} // verus!
verus! {

/// The node `path` leads to within a held tree, if every step is held.
pub open spec fn held_seek<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    path: TreePath<N>,
) -> Option<HeldTree<T, C, N, L>>
    decreases path.len(),
{
    if path.is_empty() {
        Some(t)
    } else {
        let (hd, tl) = path.pop_head();
        if 0 <= hd < N && t.has_child(hd) {
            held_seek(t.child(hd), tl)
        } else {
            None
        }
    }
}

/// The empty path resolves to the tree itself.
pub proof fn lemma_held_seek_empty<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    path: TreePath<N>,
)
    requires
        path.is_empty(),
    ensures
        held_seek(t, path) == Some(t),
{
}

/// One step of [`held_seek`], so callers need no fuel reasoning.
pub proof fn lemma_held_seek_step<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    path: TreePath<N>,
)
    requires
        !path.is_empty(),
        0 <= path.pop_head().0 < N,
        t.has_child(path.pop_head().0),
    ensures
        held_seek(t, path) == held_seek(t.child(path.pop_head().0), path.pop_head().1),
{
}

/// **The mutation gate.** Replaces the value at the root of an assembled held
/// tree.
///
/// The only public route to changing a value: [`NodeBundle`]'s fields are
/// private and it exposes only [`NodeBundle::tracked_borrow_value`]. A thread
/// that has merely taken locks cannot modify anything — it must assemble what
/// it holds into a [`tree_wf`] and [`complete`] tree, i.e. hold the whole
/// subtree.
///
/// The new value must keep the node's [`NodeValue::consts`] and node-local
/// invariant, which is what lets both predicates be re-established.
pub proof fn tracked_update_root<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked t: HeldTree<T, C, N, L>,
    tracked new_value: T,
) -> (tracked res: HeldTree<T, C, N, L>)
    requires
        tree_wf(t),
        complete(t),
        new_value.consts() == t.value().value().consts(),
        new_value.inv(t.value().level()),
        // Contents may change; edges may not. Rewiring a slot goes through
        // [`tracked_install`]/[`tracked_remove_edge`], which move the ticket
        // in the same step.
        forall|i: int|
            0 <= i < N ==> #[trigger] new_value.child_index(i) == t.value().value().child_index(i),
    ensures
        tree_wf(res),
        complete(res),
        res.level() == t.level(),
        res.value().id() == t.value().id(),
        res.value().tickets() == t.value().tickets(),
        res.value().value() == new_value,
        res.children() == t.children(),
{
    let ghost original = t;
    let ghost lv = t.level();
    let tracked (bundle, children) = t.tracked_into_parts();
    assert(original.value().inv_bundle());
    let tracked bundle = bundle.tracked_with_value(new_value);
    let ghost nc = bundle;
    assert(nc.id() == original.value().id());
    assert(nc.loc() == original.value().loc());
    assert(nc.tickets() == original.value().tickets());
    assert(nc.value() == new_value);
    assert(nc.level() == original.value().level());
    assert forall|i: int| nc.has_edge(i) implies {
        &&& 0 <= i < N
        &&& nc.tickets()[i].inv_ticket()
        &&& nc.tickets()[i].id().level == nc.level() + 1
    } by {
        assert(original.value().has_edge(i));
    }
    assert(nc.level() + 1 == L ==> forall|i: int| !#[trigger] nc.has_edge(i)) by {
        assert forall|i: int| nc.level() + 1 == L implies !#[trigger] nc.has_edge(i) by {
            assert(!original.value().has_edge(i));
        }
    }
    assert forall|i: int| 0 <= i < N implies ((#[trigger] nc.value().child_index(i)) is Some
        <==> nc.has_edge(i)) by {
        assert(original.value().value().child_index(i) is Some <==> original.value().has_edge(i));
    }
    assert forall|i: int|
        0 <= i < N && (#[trigger] nc.value().child_index(i)) is Some implies nc.value().child_index(
        i,
    ) == Some(nc.tickets()[i].id().index) by {
        assert(original.value().value().child_index(i) is Some);
    }
    assert(nc.inv_bundle());
    let tracked res = HeldTree::<T, C, N, L>::tracked_new(bundle, lv, children);
    assert(res.children() =~= original.children());
    assert(res.value() == nc);
    assert(res.inv()) by {
        assert(original.inv());
    }
    assert(res.value().inv_bundle());
    let ghost depth = (L - res.value().level()) as nat;
    assert forall|i: int| 0 <= i < N && #[trigger] res.has_child(i) implies tree_wf_at(
        res.child(i),
        (depth - 1) as nat,
    ) by {
        assert(original.has_child(i));
    }
    assert(complete_at(res, depth)) by {
        assert forall|i: int| 0 <= i < N implies {
            &&& (#[trigger] res.value().has_edge(i) <==> res.has_child(i))
            &&& res.has_child(i) ==> complete_at(res.child(i), (depth - 1) as nat)
        } by {
            assert(original.value().has_edge(i) <==> original.has_child(i));
        }
    }
    res
}

/// Reads the value of the node `path` leads to. Available without
/// [`complete`]: descending to find more locks needs reads, not writes.
pub proof fn tracked_borrow_at<'a, T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked t: &'a HeldTree<T, C, N, L>,
    path: TreePath<N>,
) -> (tracked res: &'a T)
    requires
        t.inv(),
        path.inv(),
        held_seek(*t, path) is Some,
    ensures
        *res == held_seek(*t, path)->0.value().value(),
    decreases path.len(),
{
    if path.is_empty() {
        t.tracked_borrow_value().tracked_borrow_value()
    } else {
        let (hd, tl) = path.pop_head();
        assert(t.child(hd).inv());
        let tracked child = t.tracked_borrow_child(hd);
        tracked_borrow_at(child, tl)
    }
}

/// Installs a fresh child under the root of a held tree: the ticket goes into
/// the root's bundle and the child's subtree is grafted in the same step.
///
/// Requires the root's slot to be free, so no existing edge is silently
/// dropped.
pub proof fn tracked_install_child<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked t: HeldTree<T, C, N, L>,
    i: int,
    tracked child: HeldTree<T, C, N, L>,
    tracked ticket: Parentage<C>,
    tracked new_value: T,
) -> (tracked res: HeldTree<T, C, N, L>)
    requires
        tree_wf(t),
        complete(t),
        tree_wf(child),
        complete(child),
        0 <= i < N,
        t.value().level() + 1 < L,
        !t.value().has_edge(i),
        !t.has_child(i),
        ticket.inv_ticket(),
        ticket.id() == child.value().id(),
        child.value().level() == t.value().level() + 1,
        new_value.consts() == t.value().value().consts(),
        new_value.inv(t.value().level()),
        new_value.child_index(i) == Some(ticket.id().index),
        forall|j: int|
            j != i ==> #[trigger] new_value.child_index(j) == t.value().value().child_index(j),
    ensures
        tree_wf(res),
        complete(res),
        res.level() == t.level(),
        res.value().id() == t.value().id(),
        res.value().value() == new_value,
        res.has_child(i),
        res.child(i) == child,
        res.value().has_edge(i),
        res.value().edge(i) == Some(child.value().id()),
        forall|j: int| j != i ==> #[trigger] res.value().edge(j) == t.value().edge(j),
        forall|j: int| j != i ==> #[trigger] res.children()[j] == t.children()[j],
{
    let ghost original = t;
    let ghost lv = t.level();
    let ghost old_children = t.children();
    let tracked (mut bundle, mut children) = t.tracked_into_parts();
    tracked_install(&mut bundle, i, ticket, new_value);
    let tracked _ = children.tracked_remove(i);
    children.tracked_insert(i, Some(child));
    assert(children =~= old_children.update(i, Some(child)));
    let tracked res = HeldTree::<T, C, N, L>::tracked_new(bundle, lv, children);
    assert(res.inv());
    let ghost depth = (L - res.value().level()) as nat;
    assert forall|j: int| 0 <= j < N && #[trigger] res.has_child(j) implies tree_wf_at(
        res.child(j),
        (depth - 1) as nat,
    ) by {
        if j != i {
            assert(original.has_child(j));
        }
    }
    assert(complete_at(res, depth)) by {
        assert forall|j: int| 0 <= j < N implies {
            &&& (#[trigger] res.value().has_edge(j) <==> res.has_child(j))
            &&& res.has_child(j) ==> complete_at(res.child(j), (depth - 1) as nat)
        } by {
            if j != i {
                assert(original.value().has_edge(j) <==> original.has_child(j));
            }
        }
    }
    res
}

/// Removes the root's child at slot `i`, returning the detached subtree and
/// its ticket. The subtree is now stray: every bundle in it keeps its own lock.
pub proof fn tracked_remove_child<T: NodeValue<C>, C, const N: usize, const L: usize>(
    tracked t: HeldTree<T, C, N, L>,
    i: int,
    tracked new_value: T,
) -> (tracked res: (HeldTree<T, C, N, L>, HeldTree<T, C, N, L>, Parentage<C>))
    requires
        tree_wf(t),
        complete(t),
        0 <= i < N,
        t.has_child(i),
        new_value.consts() == t.value().value().consts(),
        new_value.inv(t.value().level()),
        new_value.child_index(i) is None,
        forall|j: int|
            j != i ==> #[trigger] new_value.child_index(j) == t.value().value().child_index(j),
    ensures
        tree_wf(res.0),
        complete(res.0),
        res.0.level() == t.level(),
        res.0.value().id() == t.value().id(),
        !res.0.has_child(i),
        !res.0.value().has_edge(i),
        res.1 == t.child(i),
        tree_wf(res.1),
        res.2.inv_ticket(),
        res.2.id() == res.1.value().id(),
        res.0.value().value() == new_value,
        forall|j: int| j != i ==> #[trigger] res.0.value().edge(j) == t.value().edge(j),
        forall|j: int| j != i ==> #[trigger] res.0.children()[j] == t.children()[j],
{
    let ghost original = t;
    let ghost depth = (L - t.value().level()) as nat;
    let ghost lv = t.level();
    let ghost old_children = t.children();
    let tracked (rest, child) = tracked_detach(t, i);
    let tracked (mut bundle, mut children) = rest.tracked_into_parts();
    let tracked ticket = tracked_remove_edge(&mut bundle, i, new_value);
    let tracked res = HeldTree::<T, C, N, L>::tracked_new(bundle, lv, children);
    assert(res.children() =~= old_children.update(i, None));
    assert(res.inv()) by {
        assert(rest.inv());
    }
    assert forall|j: int| 0 <= j < N && #[trigger] res.has_child(j) implies tree_wf_at(
        res.child(j),
        (depth - 1) as nat,
    ) by {
        assert(rest.has_child(j));
    }
    assert(complete_at(res, depth)) by {
        assert forall|j: int| 0 <= j < N implies {
            &&& (#[trigger] res.value().has_edge(j) <==> res.has_child(j))
            &&& res.has_child(j) ==> complete_at(res.child(j), (depth - 1) as nat)
        } by {
            if j != i {
                assert(original.value().has_edge(j) <==> original.has_child(j));
            }
        }
    }
    (res, child, ticket)
}

} // verus!
verus! {

/// A node's place in the tree: which arena node it is, and whose child.
///
/// Pure ghost data — no [`Parentage`] ticket, so holding a place carries
/// knowledge of the shape and no permission to change it.
pub ghost struct TreePlace<C> {
    pub id: NodeId<C>,
    /// The parent this node is recorded under, `None` at a root.
    pub parent: Option<NodeId<C>>,
    /// Which of the parent's slots this node sits in.
    pub slot: int,
}

impl<C> Inv for TreePlace<C> {
    /// Nothing node-local to require: the level relation between a place and
    /// its parent is already carried by [`TreeNode::inv_children`] together
    /// with [`TreePlace::la_inv`], so stating it here too would be redundant
    /// and nothing would depend on it.
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C, const L: usize> TreeNodeValue<L> for TreePlace<C> {
    open spec fn la_inv(self, lv: nat) -> bool {
        self.id.level == lv
    }

    /// **Parentage.** A present child records *this* node as its parent, in
    /// the slot it actually occupies. So [`TreeNode::inv`] on an
    /// [`ArenaTree`] governs the parent-child relation outright.
    open spec fn rel_children(self, index: int, child: Option<Self>) -> bool {
        match child {
            Some(c) => c.parent == Some(self.id) && c.slot == index,
            None => true,
        }
    }
}

/// The arena's tree, as a tree: a [`TreeNode`] whose payload names an arena
/// node and records its parentage.
///
/// This is a *snapshot*. It is ghost data and freely duplicable, so holding
/// one blocks nobody; the authority over the shape stays with the
/// [`Parentage`] tickets, and a snapshot may go stale when they move.
pub type ArenaTree<C, const N: usize, const L: usize> = TreeNode<TreePlace<C>, N, L>;

/// The shape of a held tree, down to `depth`, as an [`ArenaTree`].
pub open spec fn shape_of_at<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    parent: Option<NodeId<C>>,
    slot: int,
    depth: nat,
) -> ArenaTree<C, N, L>
    decreases depth,
{
    TreeNode::new(
        TreePlace { id: t.value().id(), parent, slot },
        t.value().level(),
        Seq::new(
            N as nat,
            |i: int|
                if depth > 0 && 0 <= i < N && t.has_child(i) {
                    Some(shape_of_at(t.child(i), Some(t.value().id()), i, (depth - 1) as nat))
                } else {
                    None
                },
        ),
    )
}

/// The shape of a held tree, as an [`ArenaTree`] rooted here.
pub open spec fn shape_of<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
) -> ArenaTree<C, N, L> {
    shape_of_at(t, None, 0, (L - t.value().level()) as nat)
}

/// **Parentage, read out of the tree's own invariant.**
///
/// Takes any well-formed [`ArenaTree`] — not only one from [`shape_of`] — and
/// yields the parent-child relation, because that relation *is*
/// [`TreePlace::rel_children`].
pub proof fn lemma_arena_tree_parent<C, const N: usize, const L: usize>(
    s: ArenaTree<C, N, L>,
    i: int,
)
    requires
        s.inv(),
        0 <= i < N,
        s.has_child(i),
        s.value().id.level + 1 < L,
    ensures
        s.child(i).value().parent == Some(s.value().id),
        s.child(i).value().slot == i,
        s.child(i).value().id.level == s.value().id.level + 1,
{
    assert(<TreePlace<C> as TreeNodeValue<L>>::la_inv(s.value(), s.level()));
    assert(s.inv_children());
    assert(s.child(i).inv());
    assert(<TreePlace<C> as TreeNodeValue<L>>::la_inv(s.child(i).value(), s.child(i).level()));
}

/// The node-local fields of a shape snapshot.
pub proof fn lemma_shape_of_at_fields<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    parent: Option<NodeId<C>>,
    slot: int,
    depth: nat,
)
    ensures
        shape_of_at(t, parent, slot, depth).value() == (TreePlace {
            id: t.value().id(),
            parent,
            slot,
        }),
        shape_of_at(t, parent, slot, depth).level() == t.value().level(),
        shape_of_at(t, parent, slot, depth).children().len() == N,
{
}

/// One child of a shape snapshot, so callers need no fuel reasoning.
pub proof fn lemma_shape_of_at_child<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    parent: Option<NodeId<C>>,
    slot: int,
    depth: nat,
    i: int,
)
    requires
        0 <= i < N,
    ensures
        shape_of_at(t, parent, slot, depth).has_child(i) <==> (depth > 0 && t.has_child(i)),
        (depth > 0 && t.has_child(i)) ==> shape_of_at(t, parent, slot, depth).child(i)
            == shape_of_at(t.child(i), Some(t.value().id()), i, (depth - 1) as nat),
{
}

/// A held tree's shape is a well-formed [`ArenaTree`] — parentage and all.
pub proof fn lemma_shape_of_at_inv<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
    parent: Option<NodeId<C>>,
    slot: int,
    depth: nat,
)
    requires
        tree_wf(t),
        depth == L - t.value().level(),
        parent matches Some(p) ==> p.level + 1 == t.value().level(),
    ensures
        shape_of_at(t, parent, slot, depth).inv(),
    decreases depth,
{
    let s = shape_of_at(t, parent, slot, depth);
    assert(t.inv());
    assert(t.value().la_inv(t.level()));
    assert(s.value().id == t.value().id());
    assert(s.level() == t.value().level());
    assert(s.children().len() == N);
    if t.value().level() == L - 1 {
        assert forall|i: int| 0 <= i < N implies (#[trigger] s.children()[i]) is None by {
            assert(!t.has_child(i));
        }
    } else {
        assert forall|i: int| 0 <= i < N implies match #[trigger] s.children()[i] {
            Some(c) => {
                &&& c.level() == s.level() + 1
                &&& <TreePlace<C> as TreeNodeValue<L>>::rel_children(s.value(), i, Some(c.value()))
                &&& c.inv()
            },
            None => true,
        } by {
            if t.has_child(i) {
                assert(t.child(i).level() == t.level() + 1);
                assert(t.child(i).value().la_inv(t.child(i).level()));
                assert(tree_wf_at(t.child(i), (depth - 1) as nat));
                lemma_shape_of_at_inv(t.child(i), Some(t.value().id()), i, (depth - 1) as nat);
            }
        }
    }
}

/// A held tree's shape is a well-formed [`ArenaTree`].
pub proof fn lemma_shape_of_inv<T: NodeValue<C>, C, const N: usize, const L: usize>(
    t: HeldTree<T, C, N, L>,
)
    requires
        tree_wf(t),
    ensures
        shape_of(t).inv(),
{
    lemma_shape_of_at_inv(t, None, 0, (L - t.value().level()) as nat);
}

} // verus!
