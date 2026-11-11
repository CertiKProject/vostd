//! A worked instantiation of [`crate::resource::tree`].
//!
//! `Payload` is a two-field node value whose level is its frozen identity and
//! whose `val` is lock-protected. Each step a page-table cursor needs is a
//! separate contracted proof function below — build a leaf, graft children
//! under a guard, check two disjoint subtrees out, hand them back, dissolve
//! the result. [`publish_tree`] is the exec-level composition: a resource
//! tree in, a tracked [`TreeNode`] out.
use crate::ghost_tree::{TreeNode, TreePath};
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::tree::*;
use vstd::prelude::*;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// Node value: `lv` is frozen at allocation, `val` is lock-protected.
pub tracked struct Payload {
    pub ghost lv: nat,
    pub ghost val: u64,
}

impl Inv for Payload {
    open spec fn inv(self) -> bool {
        true
    }
}

impl TreeNodeValue<2> for Payload {
    open spec fn default(lv: nat) -> Self {
        Payload { lv, val: 0 }
    }

    proof fn lemma_default_preserves_inv() {
    }

    open spec fn la_inv(self, lv: nat) -> bool {
        self.lv == lv
    }

    proof fn lemma_default_preserves_la_inv() {
    }

    open spec fn rel_children(self, index: int, child: Option<Self>) -> bool {
        match child {
            Some(c) => c.lv == self.lv + 1,
            None => true,
        }
    }

    proof fn lemma_default_preserves_rel_children(self, lv: nat) {
    }
}

impl SharedTreeValue<2> for Payload {
    type Stable = nat;

    open spec fn stable(self) -> nat {
        self.lv
    }

    open spec fn rel_stable(self, index: int, child: Option<nat>) -> bool {
        match child {
            Some(clv) => clv == self.lv + 1,
            None => true,
        }
    }

    proof fn lemma_rel_children_refines_rel_stable(self, index: int, child: Option<Self>) {
    }
}

/// A binary tree of depth two: a root at level 0 over leaves at level 1.
pub type ExampleLock = SubtreeLock<Payload, 2, 2>;

pub type ExampleNode = NodeResource<Payload, 2, 2>;

pub type ExampleWriter = SubtreeWriter<Payload, 2, 2>;

pub type ExampleTree = TreeNode<Payload, 2, 2>;

/// Child slot `i` holds an available level-1 leaf.
pub open spec fn leaf_available(node: ExampleNode, i: int) -> bool {
    &&& node.has_child(i)
    &&& !node.child(i).is_vacant()
    &&& node.child(i).stable() == 1
    &&& node.child(i).node().level() == 1
    &&& node.child(i).node().inv()
    &&& node.child(i).node().is_childless()
}

/// Child slot `i` holds a level-1 leaf currently checked out by `g`.
pub open spec fn leaf_checked_out(node: ExampleNode, i: int, g: ExampleWriter) -> bool {
    &&& node.has_child(i)
    &&& node.child(i).is_vacant()
    &&& node.child(i).id() == g.id()
    &&& node.child(i).stable() == 1
    &&& g.stable() == 1
    &&& g.level() == 1
    &&& g.node().level() == 1
    &&& g.node().value().stable() == 1
    &&& g.node().inv()
    &&& g.node().is_childless()
}

/// A level-1 leaf behind its own cell, ready to be grafted in.
pub proof fn new_leaf_lock(val: u64) -> (tracked res: ExampleLock)
    ensures
        !res.is_vacant(),
        res.stable() == 1,
        res.node().inv(),
        res.node().level() == 1,
        res.node().value() == (Payload { lv: 1, val }),
        res.node().is_childless(),
{
    let tracked node = ExampleNode::tracked_new_leaf(Payload { lv: 1, val }, 1);
    ExampleLock::tracked_new(node)
}

/// A level-0 root behind its own cell, with no children yet.
pub proof fn new_root_lock(val: u64) -> (tracked res: ExampleLock)
    ensures
        !res.is_vacant(),
        res.stable() == 0,
        res.node().inv(),
        res.node().level() == 0,
        res.node().value() == (Payload { lv: 0, val }),
        res.node().is_childless(),
{
    let tracked node = ExampleNode::tracked_new_leaf(Payload { lv: 0, val }, 0);
    ExampleLock::tracked_new(node)
}

/// Grafts two leaf locks into the children of an exclusively held root.
pub proof fn graft_leaves(
    tracked guard: &mut ExampleWriter,
    tracked left: ExampleLock,
    tracked right: ExampleLock,
)
    requires
        old(guard).node().inv(),
        old(guard).node().level() == 0,
        old(guard).node().is_childless(),
        !left.is_vacant(),
        left.stable() == 1,
        left.node().inv(),
        left.node().level() == 1,
        left.node().is_childless(),
        !right.is_vacant(),
        right.stable() == 1,
        right.node().inv(),
        right.node().level() == 1,
        right.node().is_childless(),
    ensures
        final(guard).id() == old(guard).id(),
        final(guard).stable() == old(guard).stable(),
        final(guard).level() == old(guard).level(),
        final(guard).node().value() == old(guard).node().value(),
        final(guard).node().level() == 0,
        final(guard).node().inv(),
        final(guard).node().child(0) == left,
        final(guard).node().child(1) == right,
        leaf_available(final(guard).node(), 0),
        leaf_available(final(guard).node(), 1),
{
    left.lemma_stable_agrees();
    right.lemma_stable_agrees();
    let ghost l = left;
    let ghost r = right;
    let tracked node = guard.tracked_borrow_mut_node();
    node.tracked_insert_child(0, left);
    node.tracked_insert_child(1, right);
    assert(node.child(0) == l && node.child(1) == r);
    assert(node.inv_children());
}

/// Checks both children of an exclusively held root out at once.
///
/// The returned guards are owned, so each outlives the borrow that minted it
/// and could be handed to another thread. The root keeps its invariant:
/// [`NodeResource::inv_children`] quotes only the frozen identities, which a
/// checked-out child cannot move.
pub proof fn check_out_children(tracked guard: &mut ExampleWriter) -> (tracked res: (
    ExampleWriter,
    ExampleWriter,
))
    requires
        old(guard).node().inv(),
        old(guard).node().level() == 0,
        leaf_available(old(guard).node(), 0),
        leaf_available(old(guard).node(), 1),
    ensures
        final(guard).id() == old(guard).id(),
        final(guard).stable() == old(guard).stable(),
        final(guard).level() == old(guard).level(),
        final(guard).node().value() == old(guard).node().value(),
        final(guard).node().level() == 0,
        final(guard).node().inv(),
        res.0.id() == old(guard).node().child(0).id(),
        res.1.id() == old(guard).node().child(1).id(),
        res.0.node() == old(guard).node().child(0).node(),
        res.1.node() == old(guard).node().child(1).node(),
        leaf_checked_out(final(guard).node(), 0, res.0),
        leaf_checked_out(final(guard).node(), 1, res.1),
{
    let tracked node = guard.tracked_borrow_mut_node();
    let tracked left;
    {
        let tracked slot = node.tracked_borrow_mut_child(0);
        slot.lemma_stable_agrees();
        left = slot.tracked_write_acquire();
    }
    let tracked slot = node.tracked_borrow_mut_child(1);
    slot.lemma_stable_agrees();
    let tracked right = slot.tracked_write_acquire();
    assert(node.inv_children());
    (left, right)
}

/// Hands both child subtrees back to an exclusively held root.
pub proof fn return_children(
    tracked guard: &mut ExampleWriter,
    tracked left: ExampleWriter,
    tracked right: ExampleWriter,
)
    requires
        old(guard).node().inv(),
        old(guard).node().level() == 0,
        leaf_checked_out(old(guard).node(), 0, left),
        leaf_checked_out(old(guard).node(), 1, right),
    ensures
        final(guard).id() == old(guard).id(),
        final(guard).stable() == old(guard).stable(),
        final(guard).level() == old(guard).level(),
        final(guard).node().value() == old(guard).node().value(),
        final(guard).node().level() == 0,
        final(guard).node().inv(),
        final(guard).node().child(0).node() == left.node(),
        final(guard).node().child(1).node() == right.node(),
        leaf_available(final(guard).node(), 0),
        leaf_available(final(guard).node(), 1),
{
    let tracked node = guard.tracked_borrow_mut_node();
    {
        let tracked slot = node.tracked_borrow_mut_child(0);
        slot.tracked_write_release(left);
    }
    let tracked slot = node.tracked_borrow_mut_child(1);
    slot.tracked_write_release(right);
    assert(node.inv_children());
}

/// A root whose two children are available leaves is ready to exit the
/// resource world.
pub proof fn lemma_ready_to_dissolve(node: ExampleNode)
    requires
        node.inv(),
        node.level() == 0,
        leaf_available(node, 0),
        leaf_available(node, 1),
    ensures
        node.fully_locked(),
        node.coherent(),
{
    node.child(0).node().lemma_fully_locked_at_leaf(1);
    node.child(1).node().lemma_fully_locked_at_leaf(1);
    node.child(0).node().lemma_coherent_at_leaf(1);
    node.child(1).node().lemma_coherent_at_leaf(1);
    node.lemma_fully_locked_at_unfold(2);
    node.lemma_coherent_at_unfold(2);
}

/// Projects the root's and both leaves' values out of a dissolved tree.
pub proof fn lemma_tree_values(node: ExampleNode, tree: ExampleTree)
    requires
        node.level() == 0,
        leaf_available(node, 0),
        leaf_available(node, 1),
        tree == node.view_tree(),
    ensures
        tree.level() == 0,
        tree.value() == node.value(),
        tree.has_child(0),
        tree.has_child(1),
        tree.child(0).value() == node.child(0).node().value(),
        tree.child(1).value() == node.child(1).node().value(),
{
    node.lemma_view_tree_at_fields(2);
    node.lemma_view_tree_at_child(2, 0);
    node.lemma_view_tree_at_child(2, 1);
    node.child(0).node().lemma_view_tree_at_fields(1);
    node.child(1).node().lemma_view_tree_at_fields(1);
}

/// Assembles a two-level tree: a root over two leaves, nothing checked out.
///
/// This is what [`publish_tree`] consumes, so it also witnesses that
/// `publish_tree`'s preconditions are satisfiable.
pub proof fn build_tree(root_val: u64, left_val: u64, right_val: u64) -> (tracked res: ExampleLock)
    ensures
        !res.is_vacant(),
        res.node().inv(),
        res.node().level() == 0,
        res.node().value() == (Payload { lv: 0, val: root_val }),
        leaf_available(res.node(), 0),
        leaf_available(res.node(), 1),
        res.node().child(0).id() != res.node().child(1).id(),
        res.node().child(0).node().value() == (Payload { lv: 1, val: left_val }),
        res.node().child(1).node().value() == (Payload { lv: 1, val: right_val }),
{
    let tracked mut left = new_leaf_lock(left_val);
    let tracked right = new_leaf_lock(right_val);

    // Separately allocated cells are distinct. Allocation promises no fresh
    // location, so this comes from the authorities not composing.
    left.lemma_distinct(&right);

    let tracked mut lock = new_root_lock(root_val);
    let tracked mut guard = lock.tracked_write_acquire();
    graft_leaves(&mut guard, left, right);
    lock.tracked_write_release(guard);
    lock
}

/// Two roots agreeing on value, level, and both children's nodes have the
/// same view.
///
/// Needed because a child that is checked out and handed back leaves a
/// *different* [`SubtreeLock`] value in its slot — the cell round-tripped —
/// even though the node inside it is unchanged. [`NodeResource::view_tree`]
/// reads through to the child's node, so the view survives anyway.
pub proof fn lemma_same_view(a: ExampleNode, b: ExampleNode)
    requires
        a.level() == 0,
        b.level() == 0,
        a.value() == b.value(),
        leaf_available(a, 0),
        leaf_available(a, 1),
        leaf_available(b, 0),
        leaf_available(b, 1),
        a.child(0).node() == b.child(0).node(),
        a.child(1).node() == b.child(1).node(),
    ensures
        a.view_tree() == b.view_tree(),
{
    a.lemma_view_tree_at_fields(2);
    b.lemma_view_tree_at_fields(2);
    a.lemma_view_tree_at_child(2, 0);
    a.lemma_view_tree_at_child(2, 1);
    b.lemma_view_tree_at_child(2, 0);
    b.lemma_view_tree_at_child(2, 1);
    assert(a.view_tree().children() =~= b.view_tree().children());
}

/// Publishes a two-level resource tree as an ordinary ghost tree.
///
/// This is the exec-side shape of a cursor's work: take the root's guard,
/// check both subtrees out at once, hand them back, release the root, and
/// dissolve the result. The protocol is all ghost, so the steps sit in
/// `proof` blocks; a real client would interleave physical reads and writes
/// with them.
pub fn publish_tree(Tracked(lock): Tracked<ExampleLock>) -> (res: Tracked<ExampleTree>)
    requires
        !lock.is_vacant(),
        lock.node().inv(),
        lock.node().level() == 0,
        leaf_available(lock.node(), 0),
        leaf_available(lock.node(), 1),
        lock.node().child(0).id() != lock.node().child(1).id(),
    ensures
        res@ == lock.node().view_tree(),
        res@.inv(),
        res@.level() == 0,
        res@.value() == lock.node().value(),
        res@.has_child(0),
        res@.has_child(1),
        res@.child(0).value() == lock.node().child(0).node().value(),
        res@.child(1).value() == lock.node().child(1).node().value(),
{
    let tracked mut lock = lock;
    let ghost start = lock.node();
    let tracked tree;
    proof {
        // The root's node carries the identity its cell advertises, which is
        // what `tracked_write_release` will ask to have restored.
        lock.lemma_stable_agrees();
        let tracked mut guard = lock.tracked_write_acquire();

        // Both subtrees out at once, over distinct cells.
        let tracked (left_guard, right_guard) = check_out_children(&mut guard);
        assert(left_guard.id() != right_guard.id());

        return_children(&mut guard, left_guard, right_guard);
        lock.tracked_write_release(guard);

        // Nothing is checked out below, so the tree can become linear.
        let ghost published = lock.node();
        lemma_ready_to_dissolve(published);
        tree = lock.tracked_into_tree();
        lemma_same_view(published, start);
        lemma_tree_values(published, tree);
    }
    Tracked(tree)
}

/// Detaches child 0 as a plain ghost tree, leaving the parent in the resource
/// world.
///
/// The parent keeps its cell, its invariant, and its other child; only the
/// detached subtree becomes linear. The slot is left empty, which the parent's
/// [`NodeResource::inv_children`] tolerates in this example, but currently
/// wouldn't in a page table's invariant.
pub fn publish_strict_subtree(Tracked(lock): Tracked<ExampleLock>) -> (res: (
    Tracked<ExampleLock>,
    Tracked<ExampleTree>,
))
    requires
        !lock.is_vacant(),
        lock.node().inv(),
        lock.node().level() == 0,
        leaf_available(lock.node(), 0),
        leaf_available(lock.node(), 1),
    ensures
        !res.0@.is_vacant(),
        res.0@.id() == lock.id(),
        res.0@.node().inv(),
        res.0@.node().level() == 0,
        res.0@.node().value() == lock.node().value(),
        !res.0@.node().has_child(0),
        leaf_available(res.0@.node(), 1),
        res.0@.node().child(1) == lock.node().child(1),
        // The detached subtree has left the resource world.
        res.1@ == lock.node().child(0).node().view_tree(),
        res.1@.inv(),
        res.1@.level() == 1,
        res.1@.value() == lock.node().child(0).node().value(),
{
    let tracked mut lock = lock;
    let tracked tree;
    proof {
        lock.lemma_stable_agrees();
        let tracked mut guard = lock.tracked_write_acquire();

        // Take the child's cell out of the parent's slot.
        let tracked child_lock;
        {
            let tracked node = guard.tracked_borrow_mut_node();
            child_lock = node.tracked_remove_child(0);
            assert(node.value().rel_stable(0, None));
            assert(node.inv_children());
            assert(node.inv());
        }

        // Dissolve it on its own, while the parent is still locked.
        child_lock.node().lemma_fully_locked_at_leaf(1);
        child_lock.node().lemma_coherent_at_leaf(1);
        tree = child_lock.tracked_into_tree();

        lock.tracked_write_release(guard);
    }
    (Tracked(lock), Tracked(tree))
}

/// Detaches one leaf, then keeps locking the parent.
pub fn example_detach_then_keep_locking() -> (res: Tracked<ExampleTree>)
    ensures
        res@.inv(),
        res@.level() == 1,
        res@.value().val == 7,
{
    let tracked lock;
    proof {
        lock = build_tree(1, 7, 9);
    }
    let (parent, detached) = publish_strict_subtree(Tracked(lock));
    let Tracked(mut parent) = parent;
    proof {
        parent.lemma_stable_agrees();
        let tracked mut guard = parent.tracked_write_acquire();
        let tracked child_guard;
        {
            let tracked node = guard.tracked_borrow_mut_node();
            let tracked slot = node.tracked_borrow_mut_child(1);
            slot.lemma_stable_agrees();
            child_guard = slot.tracked_write_acquire();
        }
        assert(child_guard.node().value().val == 9);
        {
            let tracked node = guard.tracked_borrow_mut_node();
            let tracked slot = node.tracked_borrow_mut_child(1);
            slot.tracked_write_release(child_guard);
            assert(node.inv_children());
        }
        parent.tracked_write_release(guard);
        assert(!parent.is_vacant());
    }
    detached
}

/// Borrows a locked subtree as a ghost tree, dissolving nothing.
///
/// The lock arrives by shared reference and is handed back untouched; the
/// result is [`NodeResource::view_tree`] as a *ghost* value, carrying
/// [`TreeNode::inv`]. No `TreeNode` is ever built, so there is nothing to
/// take a tracked reference to — see the module note on why `&TreeNode` is
/// not obtainable.
pub proof fn borrow_as_ghost_tree(tracked lock: &ExampleLock) -> (res: ExampleTree)
    requires
        !lock.is_vacant(),
        lock.node().inv(),
        lock.node().coherent(),
    ensures
        res == lock.node().view_tree(),
        res.inv(),
{
    lock.node().lemma_view_tree_inv();
    lock.node().view_tree()
}

/// Runs `ghost_tree`'s own reasoning on a still-locked subtree, then goes on
/// locking it.
pub fn example_borrow_then_keep_locking() -> (res: Tracked<ExampleLock>)
    ensures
        !res@.is_vacant(),
        res@.node().inv(),
{
    let tracked mut lock;
    proof {
        lock = build_tree(1, 7, 9);
    }
    proof {
        lemma_ready_to_dissolve(lock.node());

        // Borrow the subtree as a ghost tree and use a `ghost_tree` lemma on
        // it -- `on_subtree` knows nothing about cells or locks.
        let ghost tree = borrow_as_ghost_tree(&lock);
        lemma_tree_values(lock.node(), tree);
        assert(tree.has_child(0));
        tree.lemma_child_on_subtree(0);
        assert(tree.on_subtree(tree.child(0)));
        assert(tree.child(0).value().val == 7);

        // The cells are untouched, so the subtree can still be locked.
        lock.lemma_stable_agrees();
        let tracked guard = lock.tracked_write_acquire();
        assert(guard.node().value().val == 1);
        lock.tracked_write_release(guard);
        assert(!lock.is_vacant());
    }
    Tracked(lock)
}

/// Takes a tree out of the resource world and puts it straight back.
///
/// The round trip is exact on the tree: what comes back denotes the same
/// [`TreeNode`]. It is *not* exact on identity — every cell in the restored
/// subtree is freshly allocated, so no [`Loc`] survives.
pub fn example_round_trip() -> (res: Tracked<ExampleLock>)
    ensures
        !res@.is_vacant(),
        res@.node().inv(),
        res@.node().value().val == 1,
        res@.node().child(0).node().value().val == 7,
        res@.node().child(1).node().value().val == 9,
{
    let tracked lock;
    proof {
        lock = build_tree(1, 7, 9);
    }
    let ghost before = lock.node().view_tree();
    let Tracked(restored) = publish_tree(Tracked(lock));
    let tracked back;
    proof {
        back = ExampleLock::tracked_from_tree(restored);
        assert(back.node().view_tree() == before);

        // The restored tree denotes what we started with, so its values read
        // back through the view lemmas.
        lemma_tree_values(back.node(), before);
    }
    Tracked(back)
}

/// Builds a two-level tree and publishes it, end to end.
pub fn example_build_then_publish() -> (res: Tracked<ExampleTree>)
    ensures
        res@.inv(),
        res@.level() == 0,
        res@.value().val == 1,
        res@.child(0).value().val == 7,
        res@.child(1).value().val == 9,
{
    let tracked lock;
    proof {
        lock = build_tree(1, 7, 9);
    }
    publish_tree(Tracked(lock))
}

/// Reads a descendant while holding a guard.
///
/// Read *sharing* is not this module's business, but a holder still needs to
/// look down its own subtree, and that is a plain shared borrow.
pub proof fn example_read_under_guard(tracked guard: ExampleWriter, path: TreePath<2>)
    requires
        guard.node().inv(),
        guard.node().reachable(path),
        path.inv(),
{
    let tracked node = guard.tracked_borrow_node();
    let tracked seen = node.tracked_borrow_descendant(path);
    assert(*seen == guard.node().seek(path)->0);
}

} // verus!
