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
//!
//! [`unlock_tree`] puts a whole held tree back: it walks the tree by reading
//! each node's PTEs, as exec code must, and returns each cell to the lock its
//! key names.
use crate::resource::flat_tree::*;
use vstd::cell::CellId;
use vstd::cell::pcell::{PCell, PointsTo};
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

pub type ExTree = LockedTree<Payload, 2, 2>;

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
        &&& self.p.addr != self.c.addr
    }

    pub fn new() -> (res: Self)
        ensures
            res.wf(),
    {
        let c = ExNode::new(0x2000, Ghost(1), [0, 0]);
        let p = ExNode::new(0x1000, Ghost(0), [0x2000, 0]);
        Tree2 { p, c }
    }

    /// Whether some node has address `addr`.
    pub open spec fn has_node(&self, addr: usize) -> bool {
        addr == self.p.addr || addr == self.c.addr
    }

    /// The node with address `addr`, if any. In a page table this is the step
    /// from a physical address to the frame's metadata, where its lock is.
    pub open spec fn node_spec(&self, addr: usize) -> &ExNode {
        if addr == self.p.addr {
            &self.p
        } else {
            &self.c
        }
    }

    /// The constant of the lock with key `addr`.
    pub open spec fn id_of(&self, addr: usize) -> LockConst<usize, CellId> {
        self.node_spec(addr).lock.id()
    }

    fn node(&self, addr: usize) -> (res: &ExNode)
        requires
            self.has_node(addr),
        ensures
            res == self.node_spec(addr),
    {
        if addr == self.p.addr {
            &self.p
        } else {
            &self.c
        }
    }
}

/// Returns every cell of a held tree to its own lock.
///
/// The tree must be complete (every child its nodes point to is grafted), so
/// that following the PTEs finds exactly the grafted children, and every cell
/// must belong to `t`'s lock for its key ([`cells_belong`]), so that the lock
/// the walk finds is the cell's own. The walk reads each node's PTEs through
/// the node's cell, detaches and returns each child, then unlocks the node.
///
/// # In the page table
///
/// `ostd`'s `dfs_release_lock` (in `mm/page_table/cursor/locking.rs`) is the
/// same walk. Its cells are not in a tree: they are in a flat map
/// `cells: Map<usize, PtLockCell>`, keyed by each node's metadata-slot
/// address. The shape comes from the shared `OwnerSubtree`.
///
/// - `id` is the lookup from a node's address to its frame metadata, and from
///   there to `meta_value().lock.constant()`. Exec code does the same lookup
///   (`PageTableGuard::unlock` reaches the lock through `self.meta()`), as
///   [`Tree2::node`] does here. That each address names one lock needs no
///   assumption like `p.addr != c.addr`: there is one metadata slot per
///   address.
/// - [`cells_belong`] is split in two. `Guards::cells_wf(cells)` says each
///   held cell has the lock constant recorded in `guards.held` when it was
///   locked. `node_cell_held(node, cells)` says the cell at the node's address
///   belongs to the lock in the node's metadata. `dfs_held_below` is the
///   recursive form, like [`cells_belong_at`].
/// - Where [`tree_wf`] ties each grafted child to its parent's PTE, the
///   `OwnerSubtree` is the shape, and `NodeOwner::holds` (part of the stronger
///   `node_cell_ok`) ties the cell's PTEs to the node's `pte_view`. Where
///   [`complete`] says every child a PTE points to is grafted, the
///   `OwnerSubtree` has a child for every present PTE. In place of
///   [`tracked_detach`], the walk removes the cell from the map. Distinct nodes
///   have distinct addresses by `addr_under` and `metaregion_sound`.
///
/// Once the cursor zippers over a `LockedTree`, the map and `dfs_held_below`
/// would become one `cells_belong(tree, id)`, with `id` the metadata lookup.
/// That needs `id` to stay fixed while the tree is held. Lock constants live
/// in frame metadata, which stays fixed while the frame is a page-table node.
pub fn unlock_tree(t: &Tree2, Tracked(tree): Tracked<ExTree>, addr: usize)
    requires
        t.wf(),
        tree_wf(tree),
        complete(tree),
        cells_belong(tree, |k: usize| t.id_of(k)),
        tree.value().key() == addr,
        t.has_node(addr),
    decreases 2 - tree.level(),
{
    let ghost id = |k: usize| t.id_of(k);
    let ghost tree0 = tree;
    let tracked mut tree = tree;
    let node = t.node(addr);
    assert(tree.inv());
    assert(tree.value().lock_const() == node.lock.id());
    let ptes = *node.ptes.borrow(Tracked(&tree.tracked_borrow_value().tracked_borrow_value().ptes));
    assert(ptes@ == tree0.value().value().ptes.value()@);
    // Child 0, if the PTE points to one: complete, so it is grafted.
    if ptes[0] != 0 {
        let tracked child;
        proof {
            assert(tree.has_child(0));
            lemma_cells_belong_detach(tree, 0, id);
            let tracked (rest, c) = tracked_detach(tree, 0);
            tree = rest;
            child = c;
            assert(complete_at(child, (2 - child.level()) as nat));
            // The child's cell is the lock's for its key, so the key is a node's.
            assert(child.value().lock_const() == t.id_of(ptes[0]));
        }
        unlock_tree(t, Tracked(child), ptes[0]);
    }
    // Child 1 likewise.

    if ptes[1] != 0 {
        let tracked child;
        proof {
            assert(tree.children()[1] == tree0.children()[1]);
            assert(tree.has_child(1));
            lemma_cells_belong_detach(tree, 1, id);
            let tracked (rest, c) = tracked_detach(tree, 1);
            tree = rest;
            child = c;
            assert(complete_at(child, (2 - child.level()) as nat));
            assert(child.value().lock_const() == t.id_of(ptes[1]));
        }
        unlock_tree(t, Tracked(child), ptes[1]);
    }
    // No child is left: each grafted one was pointed to, and was returned.

    proof {
        assert forall|i: int| 0 <= i < 2 implies !#[trigger] tree.has_child(i) by {
            if i == 0 && ptes[0] == 0 {
                assert(tree.children()[0] == tree0.children()[0]);
            }
            if i == 1 && ptes[1] == 0 {
                assert(tree.children()[1] == tree0.children()[1]);
            }
        }
    }
    let tracked cell = tracked_into_cell(tree);
    node.lock.unlock(Tracked(cell));
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
        let ghost (gp, gc) = (a_p, a_c);
        let tracked tree = {
            let tracked tp = tracked_leaf(a_p);
            let tracked tc = tracked_leaf(a_c);
            tracked_graft(tp, 0, tc)
        };
        proof {
            // A now holds all of `P`'s subtree, as an ordinary ghost tree, and
            // each cell came from the lock its key names.
            assert(tree.inv());
            assert(complete_at(tree.child(0), 1));
            assert(complete(tree));
            let id = |k: usize| t.id_of(k);
            assert(tree.value() == gp && tree.child(0).value() == gc);
            assert(gp.lock_const() == id(gp.key()));
            assert(gc.lock_const() == id(gc.key()));
            assert(cells_belong_at(tree.child(0), id, 1));
            assert(cells_belong(tree, id));
        }
        // A puts the whole tree back: each cell into its own lock.
        unlock_tree(t, Tracked(tree), t.p.addr);
    } else {
        t.p.lock.unlock(Tracked(a_p));
    }
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
