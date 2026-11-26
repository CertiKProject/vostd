//! A worked instantiation of [`crate::resource::arena_tree`].
//!
//! Three nodes: a root at index 0 with children at indices 1 and 2. A
//! [`Payload`] records where its children are in `kids`, and
//! [`NodeBundle::inv_bundle`] forces that record to agree with the slot's
//! ticket — so a bundle describes its own structure, and installing an edge
//! means rewriting the value and moving the ticket in one step.
use crate::ghost_tree::TreePath;
use crate::resource::arena_tree::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// Node contents: a counter, plus where this node's children are.
pub tracked struct Payload {
    pub ghost val: u64,
    pub ghost kids: Seq<Option<usize>>,
}

impl NodeValue<()> for Payload {
    open spec fn consts(self) -> () {
        ()
    }

    open spec fn inv(self, level: nat) -> bool {
        self.kids.len() == 2
    }

    open spec fn child_index(self, i: int) -> Option<usize> {
        if 0 <= i < self.kids.len() {
            self.kids[i]
        } else {
            None
        }
    }
}

pub type ExBundle = NodeBundle<Payload, (), 2, 2>;

pub type ExLock = NodeLock<Payload, (), 2, 2>;

pub type ExArena = LockArena<Payload, (), 2, 2>;

pub type ExTree = HeldTree<Payload, (), 2, 2>;

/// Creates three nodes and an arena whose locks are all held, handing the
/// bundles and the two leaf tickets to the caller.
///
/// A freshly built structure gives its bundles to its first owner: once a
/// bundle has gone through a lock its contents are no longer predictable.
pub fn build_arena() -> (res: (
    ExArena,
    Ghost<(NodeId<()>, NodeId<()>, NodeId<()>)>,
    Tracked<(ExBundle, ExBundle, ExBundle)>,
    Tracked<(Parentage<()>, Parentage<()>)>,
))
    ensures
        res.0.wf(),
        res.0.holds(res.1@.0),
        res.0.holds(res.1@.1),
        res.0.holds(res.1@.2),
        res.1@.0.index == 0,
        res.1@.1.index == 1,
        res.1@.2.index == 2,
        res.2@.0.id() == res.1@.0,
        res.2@.0.inv_bundle(),
        res.2@.1.inv_bundle(),
        res.2@.2.inv_bundle(),
        res.2@.0.level() == 0,
        res.2@.1.level() == 1,
        res.2@.2.level() == 1,
        res.2@.1.id() == res.1@.1,
        res.2@.2.id() == res.1@.2,
        forall|i: int| (#[trigger] res.2@.0.value().child_index(i)) is None,
        res.3@.0.inv_ticket(),
        res.3@.1.inv_ticket(),
        res.3@.0.id() == res.1@.1,
        res.3@.1.id() == res.1@.2,
        res.3@.0.id().level == 1,
        res.3@.1.id().level == 1,
{
    let tracked (root_bundle, _root_ticket) = ExBundle::tracked_new(
        Payload { val: 10, kids: seq![None, None] },
        0,
        0,
    );
    let tracked (left_bundle, left_ticket) = ExBundle::tracked_new(
        Payload { val: 20, kids: seq![None, None] },
        1,
        1,
    );
    let tracked (right_bundle, right_ticket) = ExBundle::tracked_new(
        Payload { val: 30, kids: seq![None, None] },
        1,
        2,
    );

    let ghost root_id = root_bundle.id();
    let ghost left_id = left_bundle.id();
    let ghost right_id = right_bundle.id();

    let mut locks: Vec<ExLock> = Vec::new();
    locks.push(ExLock::new_locked(Ghost(root_id)));
    locks.push(ExLock::new_locked(Ghost(left_id)));
    locks.push(ExLock::new_locked(Ghost(right_id)));

    assert(locks@.len() == 3);
    assert(locks@[0].id() == root_id);
    assert(locks@[1].id() == left_id);
    assert(locks@[2].id() == right_id);

    (
        ExArena::new(locks),
        Ghost((root_id, left_id, right_id)),
        Tracked((root_bundle, left_bundle, right_bundle)),
        Tracked((left_ticket, right_ticket)),
    )
}

/// Gives a childless root its two edges. Each install rewrites the value's
/// `kids` and moves the ticket together — neither alone is allowed.
pub proof fn attach_children(
    tracked parent: &mut ExBundle,
    tracked left: Parentage<()>,
    tracked right: Parentage<()>,
)
    requires
        old(parent).inv_bundle(),
        old(parent).level() == 0,
        forall|i: int| (#[trigger] old(parent).value().child_index(i)) is None,
        left.inv_ticket(),
        right.inv_ticket(),
        left.id().level == 1,
        right.id().level == 1,
    ensures
        final(parent).id() == old(parent).id(),
        final(parent).inv_bundle(),
        final(parent).level() == 0,
        final(parent).edge(0) == Some(left.id()),
        final(parent).edge(1) == Some(right.id()),
        final(parent).value().child_index(0) == Some(left.id().index),
        final(parent).value().child_index(1) == Some(right.id().index),
{
    let ghost li = left.id().index;
    let ghost ri = right.id().index;

    // `inv_bundle` turns "the value records no children" into "no tickets".
    assert forall|i: int| 0 <= i < 2 implies !#[trigger] parent.has_edge(i) by {
        assert(parent.value().child_index(i) is None);
    }

    let ghost p0 = *parent;
    let ghost v0 = parent.value();
    let tracked v1 = Payload { val: v0.val, kids: v0.kids.update(0, Some(li)) };
    tracked_install(parent, 0, left, v1);
    assert(!parent.has_edge(1)) by {
        assert(!p0.has_edge(1));
        assert(parent.tickets() == p0.tickets().insert(0, p0.tickets()[0]) || true);
    }

    let ghost v1a = parent.value();
    let tracked v2 = Payload { val: v1a.val, kids: v1a.kids.update(1, Some(ri)) };
    tracked_install(parent, 1, right, v2);
}

/// A held root that has an edge but has not grafted that child is not a
/// complete collection — so the mutation gate is shut.
pub proof fn lemma_partial_is_not_complete(t: ExTree)
    requires
        t.value().level() == 0,
        t.value().has_edge(0),
        !t.has_child(0),
    ensures
        !complete(t),
{
    assert(complete_at(t, 2) ==> (t.value().has_edge(0) <==> t.has_child(0)));
}

/// Locks an existing tree out of a well-formed arena and returns it as an
/// ordinary ghost tree.
///
/// The root's bundle is already held and **describes its own structure**: its
/// value's `child_index` says which arena slots the children are in, and
/// `inv_bundle` guarantees those agree with the tickets. The indices are
/// still parameters because a bundle is tracked, so a real client reads them
/// out of the node's memory through a permission; these stand in for that
/// read, and the preconditions tie them to the value.
///
/// `arena.holds(..)` on each child's full identity is the remaining
/// obligation — "this index still names *this* node" — which is what RCU
/// would supply.
pub fn lock_existing_tree(
    arena: &ExArena,
    Tracked(root_bundle): Tracked<ExBundle>,
    left_index: usize,
    right_index: usize,
) -> (res: Tracked<ExTree>)
    requires
        arena.wf(),
        root_bundle.inv_bundle(),
        root_bundle.level() == 0,
        root_bundle.value().child_index(0) == Some(left_index),
        root_bundle.value().child_index(1) == Some(right_index),
        arena.holds(root_bundle.edge(0)->0),
        arena.holds(root_bundle.edge(1)->0),
    ensures
        tree_wf(res@),
        complete(res@),
        res@.value() == root_bundle,
        res@.has_child(0),
        res@.has_child(1),
        res@.child(0).value().id() == root_bundle.edge(0)->0,
        res@.child(1).value().id() == root_bundle.edge(1)->0,
{
    // `inv_bundle` turns the value's record into the tickets' ids.
    assert(root_bundle.value().child_index(0) is Some);
    assert(root_bundle.value().child_index(1) is Some);
    assert(root_bundle.has_edge(0) && root_bundle.has_edge(1));
    let ghost left_id = root_bundle.edge(0)->0;
    let ghost right_id = root_bundle.edge(1)->0;
    assert(left_id.index == left_index) by {
        assert(root_bundle.value().child_index(0) == Some(root_bundle.tickets()[0].id().index));
    }
    assert(right_id.index == right_index) by {
        assert(root_bundle.value().child_index(1) == Some(root_bundle.tickets()[1].id().index));
    }

    let Tracked(left_bundle) = arena.lock(left_index, Ghost(left_id));
    let Tracked(right_bundle) = arena.lock(right_index, Ghost(right_id));

    let tracked mut tree;
    proof {
        tree = tracked_leaf(root_bundle);
        let tracked left_leaf = tracked_leaf(left_bundle);
        let tracked right_leaf = tracked_leaf(right_bundle);
        // Level 1 is the deepest level, so `inv_bundle` already says these
        // have no edges — the one shape fact that survives a lock.
        lemma_leaf_complete(left_leaf);
        lemma_leaf_complete(right_leaf);

        let ghost lt = left_leaf;
        let ghost rt = right_leaf;
        let ghost t0 = tree;
        tree = tracked_graft(tree, 0, left_leaf);
        assert(tree.children() == t0.children().update(0, Some(lt)));
        assert(!t0.has_child(1));
        assert(tree.children()[1] == t0.children()[1]);
        assert(!tree.has_child(1));
        tree = tracked_graft(tree, 1, right_leaf);
        assert(tree.child(0) == lt && tree.child(1) == rt);
        assert(complete_at(tree.child(0), 1));
        assert(complete_at(tree.child(1), 1));
        assert(complete_at(tree, 2));
    }
    Tracked(tree)
}

/// The converse: releases a held tree's children back to their own locks,
/// leaving only the root held. The edges are untouched, so the tree is still
/// there — it is just no longer collected.
pub fn unlock_tree(
    arena: &ExArena,
    Tracked(tree): Tracked<ExTree>,
    left_index: usize,
    right_index: usize,
) -> (res: Tracked<ExBundle>)
    requires
        arena.wf(),
        tree_wf(tree),
        tree.value().level() == 0,
        tree.has_child(0),
        tree.has_child(1),
        arena.holds(tree.child(0).value().id()),
        arena.holds(tree.child(1).value().id()),
        tree.child(0).value().index() == left_index,
        tree.child(1).value().index() == right_index,
    ensures
        res@ == tree.value(),
        res@.inv_bundle(),
        res@.edge(0) == tree.value().edge(0),
        res@.edge(1) == tree.value().edge(1),
{
    let tracked left_bundle;
    let tracked right_bundle;
    let tracked root_bundle;
    proof {
        let tracked (rest, left_tree) = tracked_detach(tree, 0);
        assert(rest.has_child(1)) by {
            assert(rest.children()[1] == tree.children()[1]);
        }
        let tracked (rest2, right_tree) = tracked_detach(rest, 1);
        left_bundle = tracked_into_bundle(left_tree);
        right_bundle = tracked_into_bundle(right_tree);
        root_bundle = tracked_into_bundle(rest2);
        assert(left_bundle == tree.child(0).value());
        assert(right_bundle == tree.child(1).value());
    }
    arena.unlock(left_index, Tracked(left_bundle));
    arena.unlock(right_index, Tracked(right_bundle));
    Tracked(root_bundle)
}

/// Puts a held leaf subtree back under a parent that lives in the arena: the
/// subtree's bundle goes to its own lock, and its ticket plus the parent's
/// rewritten value become the edge.
pub fn reattach_leaf(
    arena: &ExArena,
    Tracked(parent): Tracked<ExBundle>,
    Tracked(leaf): Tracked<ExTree>,
    Tracked(ticket): Tracked<Parentage<()>>,
    leaf_index: usize,
) -> (res: Tracked<ExBundle>)
    requires
        arena.wf(),
        parent.inv_bundle(),
        parent.level() == 0,
        !parent.has_edge(0),
        tree_wf(leaf),
        forall|i: int| 0 <= i < 2 ==> !#[trigger] leaf.has_child(i),
        leaf.value().level() == 1,
        ticket.inv_ticket(),
        ticket.id() == leaf.value().id(),
        ticket.id().level == 1,
        ticket.id().index == leaf_index,
        arena.holds(leaf.value().id()),
        leaf.value().index() == leaf_index,
    ensures
        res@.id() == parent.id(),
        res@.inv_bundle(),
        res@.edge(0) == Some(ticket.id()),
        res@.value().child_index(0) == Some(leaf_index),
{
    let tracked mut parent = parent;
    let tracked leaf_bundle;
    proof {
        leaf_bundle = tracked_into_bundle(leaf);
        let ghost v = parent.value();
        let tracked nv = Payload { val: v.val, kids: v.kids.update(0, Some(leaf_index)) };
        tracked_install(&mut parent, 0, ticket, nv);
    }
    arena.unlock(leaf_index, Tracked(leaf_bundle));
    Tracked(parent)
}

/// The full round trip: publish nodes into the arena, lock the tree back out,
/// detach a child, reattach it, and unlock everything.
pub fn example_round_trip() {
    let (arena, ids, bundles, tickets) = build_arena();
    let ghost left_id = ids@.1;
    let ghost right_id = ids@.2;
    let tracked (mut root_bundle, left_bundle, right_bundle) = bundles.get();
    let tracked (left_ticket, right_ticket) = tickets.get();

    proof {
        attach_children(&mut root_bundle, left_ticket, right_ticket);
        assert(root_bundle.edge(0) == Some(left_id));
        assert(root_bundle.value().child_index(0) == Some(1usize));
        assert(root_bundle.value().child_index(1) == Some(2usize));
    }
    arena.unlock(1, Tracked(left_bundle));
    arena.unlock(2, Tracked(right_bundle));

    // ---- arena -> ghost tree ----
    let Tracked(tree) = lock_existing_tree(&arena, Tracked(root_bundle), 1, 2);
    proof {
        assert(tree.inv());
        tree.lemma_child_on_subtree(0);
        assert(tree.on_subtree(tree.child(0)));
    }

    // ---- the shape, as a tree ----
    // `shape_of` projects a tree of arena indices with parentage recorded.
    // It is ghost data with no ticket in it, so it costs nothing to hold and
    // blocks nobody.
    let ghost shape = shape_of(tree);
    proof {
        lemma_shape_of_inv(tree);
        lemma_shape_of_at_fields(tree, None, 0, 2);
        lemma_shape_of_at_child(tree, None, 0, 2, 0);
        lemma_shape_of_at_child(tree, None, 0, 2, 1);
        lemma_shape_of_at_fields(tree.child(0), Some(tree.value().id()), 0, 1);
        lemma_shape_of_at_fields(tree.child(1), Some(tree.value().id()), 1, 1);
        assert(shape.inv());
        assert(shape.value().id == tree.value().id());
        assert(shape.has_child(0) && shape.has_child(1));
        // Parentage comes from the tree's own invariant, not from how the
        // snapshot was built.
        lemma_arena_tree_parent(shape, 0);
        lemma_arena_tree_parent(shape, 1);
        assert(shape.child(0).value().parent == Some(shape.value().id));
        assert(shape.child(0).value().slot == 0);
        assert(shape.child(1).value().slot == 1);
        assert(shape.child(0).value().id.level == shape.value().id.level + 1);
        assert(tree.child(0).value().id() == left_id);
        assert(shape.child(0).value().id == tree.child(0).value().id());
        assert(shape.child(0).value().id.index == 1);
        // And it is an ordinary ghost tree.
        shape.lemma_child_on_subtree(0);
        assert(shape.on_subtree(shape.child(0)));
    }

    // ---- the gate: give up one held child and modification is refused ----
    let tracked mut tree = tree;
    proof {
        let tracked (rest, child) = tracked_detach(tree, 0);
        lemma_partial_is_not_complete(rest);
        assert(!complete(rest));
        tree = tracked_graft(rest, 0, child);
        assert(complete_at(tree.child(0), 1));
        assert(complete_at(tree.child(1), 1));
        assert(complete_at(tree, 2));
    }

    // ---- detach the left child entirely: edge and all ----
    let tracked stray_leaf;
    let tracked stray_ticket;
    let tracked trunk;
    proof {
        let ghost v = tree.value().value();
        let tracked nv = Payload { val: v.val, kids: v.kids.update(0, None) };
        let tracked (rest, detached, ticket) = tracked_remove_child(tree, 0, nv);
        trunk = rest;
        stray_leaf = detached;
        stray_ticket = ticket;
        assert(!trunk.value().has_edge(0) && !trunk.has_child(0));
    }

    // ---- hand the trunk's remaining child back to the arena ----
    let tracked trunk_bundle;
    let tracked right_back;
    proof {
        let tracked (rest, right_tree) = tracked_detach(trunk, 1);
        right_back = tracked_into_bundle(right_tree);
        trunk_bundle = tracked_into_bundle(rest);
    }
    arena.unlock(2, Tracked(right_back));

    // ---- reattach the stray leaf, then send the root home ----
    let Tracked(root_again) = reattach_leaf(
        &arena,
        Tracked(trunk_bundle),
        Tracked(stray_leaf),
        Tracked(stray_ticket),
        1,
    );
    proof {
        assert(root_again.edge(0) == Some(left_id));
        assert(root_again.id() == ids@.0) by {
            assert(trunk_bundle.id() == ids@.0);
        }
        assert(arena.holds(root_again.id()));
        assert(root_again.index() == 0);
    }
    arena.unlock(0, Tracked(root_again));

    // The snapshot survives: it never held a permission, so giving every lock
    // back does not take it away. It may of course now be stale — the ticket
    // for node 1 moved twice since it was taken.
    proof {
        assert(shape.inv());
        lemma_arena_tree_parent(shape, 0);
        assert(shape.child(0).value().parent == Some(shape.value().id));
    }
}

} // verus!
