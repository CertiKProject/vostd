//! A worked instantiation of [`crate::resource::tree`].
//!
//! `Cell` is a two-field node value whose level is its frozen identity and
//! whose `val` is lock-protected. The proofs below exercise the protocol a
//! page-table cursor needs: grow a tree under a write guard, publish it,
//! take a read lease, read a descendant through that lease, and reclaim.
use crate::ghost_tree::TreePath;
use crate::ownership::Inv;
use crate::prelude::TreeNodeValue;
use crate::resource::tree::*;
use vstd::prelude::*;

verus! {

/// Node value: `lv` is frozen at allocation, `val` is lock-protected.
pub tracked struct Cell {
    pub ghost lv: nat,
    pub ghost val: u64,
}

impl Inv for Cell {
    open spec fn inv(self) -> bool {
        true
    }
}

impl TreeNodeValue<2> for Cell {
    open spec fn default(lv: nat) -> Self {
        Cell { lv, val: 0 }
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

impl SharedTreeValue<2> for Cell {
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

/// A binary tree of depth two whose locks admit three concurrent readers.
pub type ExampleLock = SubtreeLock<Cell, 2, 2, 4>;

pub type ExampleNode = NodeResource<Cell, 2, 2, 4>;

/// Builds a root with one child, then reads the child through a read lease on
/// the root.
///
/// The read lease is the whole point: the returned child reference is obtained
/// without ever write-locking the root, and two leases coexist.
pub proof fn example_grow_then_share() {
    // A fresh leaf, and a fresh root, each behind their own counting pool.
    let tracked leaf = ExampleNode::tracked_new_leaf(Cell { lv: 1, val: 7 }, 1);
    let tracked leaf_lock = ExampleLock::tracked_new(leaf);
    assert(leaf_lock.is_unlocked());
    let ghost leaf_snapshot = leaf;
    let ghost leaf_lock_snapshot = leaf_lock;

    let tracked mut root = ExampleNode::tracked_new_leaf(Cell { lv: 0, val: 1 }, 0);
    let tracked root_lock = ExampleLock::tracked_new(root);

    // Graft the leaf in under a write guard on the root.
    let tracked mut root_lock = root_lock;
    let tracked mut guard = root_lock.tracked_write_acquire();
    let ghost stable_before = guard.stable();
    let ghost level_before = guard.level();
    {
        let tracked node = guard.tracked_borrow_mut_node();
        node.tracked_insert_child(0, leaf_lock);
        assert(node.children()[0] == Some(leaf_lock_snapshot));
        assert(node.has_child(0));
        assert(node.child(0) == leaf_lock_snapshot);
        assert(!node.child(0).is_vacant());
        assert(node.child(0).stable() == 1);
        assert(node.value().rel_stable(0, Some(node.child(0).stable())));
        assert(node.value().rel_stable(1, None));
        assert(node.inv_children());
        assert(node.inv());
    }
    assert(guard.node().value().stable() == stable_before);
    assert(guard.node().level() == level_before);
    root_lock.tracked_write_release(guard);

    // The tree is published again: now two readers can share it.
    assert(root_lock.is_unlocked());
    let tracked lease_a = root_lock.tracked_read_acquire();
    let tracked lease_b = root_lock.tracked_read_acquire();
    assert(root_lock.issued() == 2);
    assert(!root_lock.is_unlocked());
    lease_a.lemma_agree(&lease_b);

    // A single lease reaches the whole subtree.
    let ghost path = TreePath::<2>::new(seq![0int]);
    assert(path.inv());
    assert(!path.is_empty());
    assert(path.pop_head().0 == 0);
    assert(path.pop_head().1.is_empty()) by {
        assert(path.pop_head().1.len() == 0);
    }
    let tracked observed = lease_a.tracked_borrow_node();
    assert(observed.inv());
    assert(observed.child(0) == leaf_lock_snapshot);
    assert(leaf_lock_snapshot.node() == leaf_snapshot);
    let ghost tail = path.pop_head().1;
    leaf_snapshot.lemma_seek_empty(tail);
    observed.lemma_seek_step(path);
    assert(observed.seek(path) == Some(leaf_snapshot));
    let tracked child = observed.tracked_borrow_descendant(path);
    assert(child.value() == leaf_snapshot.value());
    assert(child.value().val == 7);
    assert(child.level() == 1);

    // Returning both leases restores write access.
    root_lock.tracked_read_release(lease_a);
    root_lock.tracked_read_release(lease_b);
    assert(root_lock.issued() == 0);
    assert(root_lock.is_unlocked());
}

/// A withdrawn node and a lease cannot name the same lock.
pub proof fn example_exclusion(tracked lease: SubtreeRead<Cell, 2, 2, 4>) {
    let tracked node = ExampleNode::tracked_new_leaf(Cell { lv: 1, val: 0 }, 1);
    let tracked mut lock = ExampleLock::tracked_new(node);
    let tracked guard = lock.tracked_write_acquire();
    assert(lock.is_vacant());
    lock.lemma_write_excludes_lease(&lease);
    assert(lock.id() != lease.id());
    lock.tracked_write_release(guard);
}

} // verus!
