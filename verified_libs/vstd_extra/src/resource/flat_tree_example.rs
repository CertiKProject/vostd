//! A worked instantiation of [`crate::resource::flat_tree`].
//!
//! Two nodes of a two-level tree: a root `P` and a child `C`, each with its own
//! [`NodeLock`] and its own two-entry "PTE" array in a [`PCell`]. A PTE holds
//! the address of the child it points to, or `0` for none. The examples are
//! the two situations that motivate keeping cells flat:
//!
//! - [`example_overlapping_cursors`]: one cursor holds `C` while another locks
//!   `P` and then wants `C`. The first returns `C` to `C`'s own lock without
//!   any help from the holder of `P`.
//! - [`example_stray_child`]: `C` is unmapped from `P` while another cursor
//!   holds `C`, and that cursor can still unlock it.
use crate::resource::flat_tree::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::cell::CellId;
use vstd::prelude::*;

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// The contents of a node: its PTE array, plus its address.
pub tracked struct Payload {
    pub ghost addr: usize,
    pub tracked ptes: PointsTo<[usize; 2]>,
}

impl LockedValue for Payload {
    type Key = usize;

    type Consts = CellId;

    open spec fn key(self) -> usize {
        self.addr
    }

    open spec fn consts(self) -> CellId {
        self.ptes.id()
    }

    open spec fn child_key(self, i: int) -> Option<usize> {
        let pte = self.ptes.value()@[i];
        if pte == 0 {
            None
        } else {
            Some(pte)
        }
    }

    open spec fn inv(self, level: nat) -> bool {
        self.addr != 0
    }
}

pub type ExCell = NodeCell<Payload, 2, 2>;

/// One node: its lock, and the PTE array the lock protects.
pub struct ExNode {
    pub addr: usize,
    pub ptes: PCell<[usize; 2]>,
    pub lock: NodeLock<Payload, 2, 2>,
}

impl ExNode {
    pub open spec fn wf(&self, level: nat) -> bool {
        &&& self.lock.wf()
        &&& self.lock.id().level == level
        &&& self.lock.id().key == self.addr
        &&& self.lock.id().consts == self.ptes.id()
    }

    fn new(addr: usize, level: Ghost<nat>, ptes: [usize; 2]) -> (res: Self)
        requires
            addr != 0,
            level@ < 2,
            level@ == 1 ==> ptes@[0] == 0 && ptes@[1] == 0,
        ensures
            res.wf(level@),
            res.addr == addr,
    {
        let (cell, Tracked(perm)) = PCell::new(ptes);
        let tracked payload = Payload { addr, ptes: perm };
        let tracked node_cell = ExCell::tracked_new(payload, level@);
        let lock = NodeLock::new(Tracked(node_cell));
        ExNode { addr, ptes: cell, lock }
    }
}

/// A root `P` and one child `C`. Nothing here records that `P` points to `C`:
/// that is in `P`'s PTEs, under `P`'s lock.
pub struct Tree2 {
    pub p: ExNode,
    pub c: ExNode,
}

impl Tree2 {
    pub open spec fn wf(&self) -> bool {
        &&& self.p.wf(0)
        &&& self.c.wf(1)
    }

    pub fn new() -> (res: Self)
        ensures
            res.wf(),
    {
        let c = ExNode::new(0x2000, Ghost(1), [0, 0]);
        let p = ExNode::new(0x1000, Ghost(0), [0x2000, 0]);
        Tree2 { p, c }
    }
}

/// Cursor B holds the mid-level node `C` while cursor A locks `P`. B then
/// unlocks `C` into `C`'s own lock, and A goes on to lock `C` and assemble
/// both into one ghost tree. Interleaved in one thread for illustration; no
/// step of B needs anything from A.
pub fn example_overlapping_cursors(t: &Tree2)
    requires
        t.wf(),
{
    // B: lock `C` directly, as after a lock-free walk down from the root.
    let Tracked(b_c) = t.c.lock.lock();

    // A: lock `P` and read its PTEs.
    let Tracked(a_p) = t.p.lock.lock();
    let tracked mut a_p = a_p;
    let ptes = *t.p.ptes.borrow(Tracked(&a_p.tracked_borrow_value().ptes));

    // B is done with `C`. The cell's identity says which lock it belongs to.
    t.c.lock.unlock(Tracked(b_c));

    if ptes[0] == t.c.addr && ptes[1] == 0 {
        // A follows PTE 0 to `C`'s lock.
        let Tracked(a_c) = t.c.lock.lock();
        let tracked mut a_c = a_c;
        proof {
            let tracked tp = tracked_leaf(a_p);
            let tracked tc = tracked_leaf(a_c);
            let tracked tree = tracked_graft(tp, 0, tc);

            // A now holds all of `P`'s subtree, as an ordinary ghost tree.
            assert(tree.inv());
            assert(complete_at(tree.child(0), 1));
            assert(complete(tree));

            // Taking it apart returns the same cells, for the same locks.
            let tracked (tp, tc) = tracked_detach(tree, 0);
            a_p = tracked_into_cell(tp);
            a_c = tracked_into_cell(tc);
        }
        t.c.lock.unlock(Tracked(a_c));
    }
    t.p.lock.unlock(Tracked(a_p));
}

/// Cursor A unmaps `C` from `P` while cursor B holds `C`. `C` is now stray,
/// so A can no longer graft it under `P` (`tracked_graft` needs `P`'s PTE to
/// point to `C`), but B still unlocks it normally.
pub fn example_stray_child(t: &Tree2)
    requires
        t.wf(),
{
    let Tracked(b_c) = t.c.lock.lock();

    let Tracked(a_p) = t.p.lock.lock();
    let tracked mut a_p = a_p;
    {
        let tracked a_p_val = a_p.tracked_borrow_mut_value();
        t.p.ptes.write(Tracked(&mut a_p_val.ptes), [0, 0]);
    }
    proof {
        assert(a_p.value().child_key(0) is None);
    }
    t.p.lock.unlock(Tracked(a_p));

    t.c.lock.unlock(Tracked(b_c));
}

} // verus!
