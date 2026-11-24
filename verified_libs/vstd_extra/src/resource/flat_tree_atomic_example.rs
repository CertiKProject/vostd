//! [`crate::resource::flat_tree_example`], with PTEs that can be read without
//! the lock.
//!
//! A page-table walk reads PTEs without taking any lock, and relies on the
//! RCU to keep what they point to alive. So the PTE words cannot be a
//! permission inside the lock cell, as they are in the first example: only
//! the lock holder could read them. Here each PTE is an atomic word, whose
//! atomic invariant holds one half of a ghost variable ([`GhostVar`]) that
//! records the word's value. The other half ([`GhostVarAuth`]) is in the
//! node's lock cell. So:
//!
//! - anyone can load a word, and learns only what the atomic invariant
//!   promises about every value the word can have ([`pte_ok`]: `0`, or the
//!   address of some node);
//! - the lock holder can load a word and learn its exact value, because the
//!   two halves agree ([`ExNode::read`]);
//! - only the lock holder can store to a word, because a store must update
//!   both halves ([`ExNode::write`]).
//!
//! The lock cell's [`LockedValue::child_key`] is read off the authoritative
//! halves, so grafting and [`unlock_tree`] work as before. [`pte_ok`] here
//! stands for "points to a node that is still alive", which the RCU would
//! provide; this example has a fixed set of nodes, so it is just membership.
use crate::resource::flat_tree::*;
use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicUsize};
use vstd::atomic_with_ghost;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};

verus! {

broadcast use crate::ghost_tree::group_ghost_tree_lemmas;

/// What every reader may assume about a PTE word: it is absent (`0`), or
/// it points to one of the nodes in `valid`.
pub open spec fn pte_ok(v: usize, valid: Set<usize>) -> bool {
    v == 0 || valid.contains(v)
}

/// The constant of a PTE word: the identity of its ghost variable, and the
/// nodes it may point to.
pub ghost struct PteConst {
    pub id: Loc,
    pub valid: Set<usize>,
}

/// The atomic invariant of a PTE word: it holds the non-authoritative half
/// of the word's ghost variable, which records the word's value.
pub struct PtePred;

impl AtomicInvariantPredicate<PteConst, usize, GhostVar<usize>> for PtePred {
    open spec fn atomic_inv(k: PteConst, v: usize, g: GhostVar<usize>) -> bool {
        &&& g.id() == k.id
        &&& g@ == v
        &&& pte_ok(v, k.valid)
    }
}

pub type PteWord = AtomicUsize<PteConst, GhostVar<usize>, PtePred>;

/// The contents of a node's lock cell: the authoritative halves of its PTE
/// words' ghost variables, plus its address.
pub tracked struct Payload {
    pub ghost addr: usize,
    pub tracked pte0: GhostVarAuth<usize>,
    pub tracked pte1: GhostVarAuth<usize>,
}

impl Payload {
    /// The value of PTE `i`, as the lock holder knows it.
    pub open spec fn pte(self, i: int) -> usize {
        if i == 0 {
            self.pte0@
        } else {
            self.pte1@
        }
    }
}

impl LockedValue<usize, (Loc, Loc)> for Payload {
    open spec fn key(self) -> usize {
        self.addr
    }

    open spec fn consts(self) -> (Loc, Loc) {
        (self.pte0.id(), self.pte1.id())
    }

    open spec fn child_key(self, i: int) -> Option<usize> {
        if self.pte(i) == 0 {
            None
        } else {
            Some(self.pte(i))
        }
    }

    open spec fn inv(self, level: nat) -> bool {
        self.addr != 0
    }
}

pub type ExCell = NodeCell<Payload, usize, (Loc, Loc), 2, 2>;

pub type ExTree = LockedTree<Payload, usize, (Loc, Loc), 2, 2>;

/// One node: its lock, and its two PTE words. The words are outside the
/// lock: the lock protects only the right to change them.
pub struct ExNode {
    pub addr: usize,
    pub pte0: PteWord,
    pub pte1: PteWord,
    pub lock: NodeLock<Payload, usize, (Loc, Loc), 2, 2>,
}

impl ExNode {
    pub open spec fn word(&self, i: int) -> &PteWord {
        if i == 0 {
            &self.pte0
        } else {
            &self.pte1
        }
    }

    /// The nodes this node's PTEs may point to.
    pub open spec fn valid(&self) -> Set<usize> {
        self.pte0.constant().valid
    }

    /// The PTE words are well formed, and the lock's cell holds the
    /// authoritative halves of exactly these words' ghost variables.
    pub open spec fn words_wf(&self) -> bool {
        &&& self.pte0.well_formed()
        &&& self.pte1.well_formed()
        &&& self.pte1.constant().valid == self.valid()
        &&& self.lock.id().consts == (self.pte0.constant().id, self.pte1.constant().id)
    }

    pub open spec fn wf(&self, level: nat) -> bool {
        &&& self.lock.wf()
        &&& self.lock.id().level == level
        &&& self.lock.id().key == self.addr
        &&& self.words_wf()
    }

    fn new(addr: usize, level: Ghost<nat>, ptes: [usize; 2], valid: Ghost<Set<usize>>) -> (res:
        Self)
        requires
            addr != 0,
            level@ < 2,
            level@ == 1 ==> ptes@[0] == 0 && ptes@[1] == 0,
            pte_ok(ptes@[0], valid@),
            pte_ok(ptes@[1], valid@),
        ensures
            res.wf(level@),
            res.addr == addr,
            res.valid() == valid@,
    {
        let tracked (a0, g0) = GhostVarAuth::<usize>::new(ptes[0]);
        let tracked (a1, g1) = GhostVarAuth::<usize>::new(ptes[1]);
        let pte0 = PteWord::new(
            Ghost(PteConst { id: g0.id(), valid: valid@ }),
            ptes[0],
            Tracked(g0),
        );
        let pte1 = PteWord::new(
            Ghost(PteConst { id: g1.id(), valid: valid@ }),
            ptes[1],
            Tracked(g1),
        );
        let tracked payload = Payload { addr, pte0: a0, pte1: a1 };
        let tracked cell = ExCell::tracked_new(payload, level@);
        let lock = NodeLock::new(Tracked(cell));
        ExNode { addr, pte0, pte1, lock }
    }

    fn word_exec(&self, i: usize) -> (res: &PteWord)
        requires
            i < 2,
        ensures
            res == self.word(i as int),
    {
        if i == 0 {
            &self.pte0
        } else {
            &self.pte1
        }
    }

    /// Reads PTE `i` without the lock, as a page-table walk does. The value
    /// may be stale by the time it is used, and the reader learns only that
    /// it is [`pte_ok`].
    pub fn read_unlocked(&self, i: usize) -> (v: usize)
        requires
            self.words_wf(),
            i < 2,
        ensures
            pte_ok(v, self.valid()),
    {
        let w = self.word_exec(i);
        atomic_with_ghost! {
            w => load();
            returning r;
            ghost g => {
                assert(pte_ok(r, self.valid()));
            }
        }
    }

    /// Reads PTE `i` while holding the node's cell: the value is exactly the
    /// one the cell records, because only the cell's holder can change it.
    pub fn read(&self, i: usize, Tracked(cell): Tracked<&ExCell>) -> (v: usize)
        requires
            self.words_wf(),
            cell.lock_const() == self.lock.id(),
            i < 2,
        ensures
            v == cell.value().pte(i as int),
    {
        let w = self.word_exec(i);
        atomic_with_ghost! {
            w => load();
            returning r;
            ghost g => {
                if i == 0 {
                    cell.tracked_borrow_value().pte0.agree(&g);
                } else {
                    cell.tracked_borrow_value().pte1.agree(&g);
                }
            }
        }
    }

    /// Writes PTE `i`, which takes the node's cell: the store updates the
    /// word and both halves of its ghost variable together. Readers without
    /// the lock see either the old value or the new one, both [`pte_ok`].
    pub fn write(&self, i: usize, v: usize, Tracked(cell): Tracked<&mut ExCell>)
        requires
            self.words_wf(),
            old(cell).lock_const() == self.lock.id(),
            i < 2,
            pte_ok(v, self.valid()),
        ensures
            final(cell).lock_const() == old(cell).lock_const(),
            final(cell).value().pte(i as int) == v,
            final(cell).value().pte(1 - i) == old(cell).value().pte(1 - i),
    {
        let w = self.word_exec(i);
        atomic_with_ghost! {
            w => store(v);
            ghost g => {
                let tracked val = cell.tracked_borrow_mut_value();
                if i == 0 {
                    val.pte0.update(&mut g, v);
                } else {
                    val.pte1.update(&mut g, v);
                }
            }
        }
    }
}

/// A root `P` and one child `C`. Nothing here records that `P` points to `C`:
/// that is in `P`'s PTE words, which only `P`'s lock holder can change.
pub struct Tree2 {
    pub p: ExNode,
    pub c: ExNode,
}

impl Tree2 {
    /// The nodes of the tree: what a PTE may point to.
    pub open spec fn valid(&self) -> Set<usize> {
        set![self.p.addr, self.c.addr]
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.p.wf(0)
        &&& self.c.wf(1)
        &&& self.p.addr != self.c.addr
        &&& self.p.valid() == self.valid()
        &&& self.c.valid() == self.valid()
    }

    pub fn new() -> (res: Self)
        ensures
            res.wf(),
    {
        let ghost valid = set![0x1000usize, 0x2000usize];
        let c = ExNode::new(0x2000, Ghost(1), [0, 0], Ghost(valid));
        let p = ExNode::new(0x1000, Ghost(0), [0x2000, 0], Ghost(valid));
        Tree2 { p, c }
    }

    /// Whether some node has address `addr`.
    pub open spec fn has_node(&self, addr: usize) -> bool {
        self.valid().contains(addr)
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
    pub open spec fn id_of(&self, addr: usize) -> LockConst<usize, (Loc, Loc)> {
        self.node_spec(addr).lock.id()
    }

    fn node(&self, addr: usize) -> (res: &ExNode)
        requires
            self.wf(),
            self.has_node(addr),
        ensures
            res == self.node_spec(addr),
            res.words_wf(),
            res.lock.wf(),
            res.lock.id().key == addr,
    {
        if addr == self.p.addr {
            &self.p
        } else {
            &self.c
        }
    }
}

/// A lock-free walk, as before `lock_range` locks anything: read `P`'s PTE
/// without `P`'s lock, and lock the node it points to. The reader learns
/// only that the PTE names some node, which is enough to find that node's
/// lock. It does not learn that `P` still points there: by the time it has
/// the lock, `P`'s holder may have changed the PTE.
pub fn example_lock_free_walk(t: &Tree2)
    requires
        t.wf(),
{
    let v = t.p.read_unlocked(0);
    if v != 0 {
        let n = t.node(v);
        let Tracked(cell) = n.lock.lock();
        proof {
            // The cell is the node's, whichever node it is.
            assert(cell.key() == v);
        }
        n.lock.unlock(Tracked(cell));
    }
}

/// Returns every cell of a held tree to its own lock, as in the first
/// example. The walk reads each node's PTEs through the node's cell, which
/// gives their exact values.
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
    let pte0 = node.read(0, Tracked(tree.tracked_borrow_value()));
    let pte1 = node.read(1, Tracked(tree.tracked_borrow_value()));
    // Child 0, if the PTE points to one: complete, so it is grafted.
    if pte0 != 0 {
        let tracked child;
        proof {
            assert(tree.has_child(0));
            lemma_cells_belong_detach(tree, 0, id);
            let tracked (rest, c) = tracked_detach(tree, 0);
            tree = rest;
            child = c;
            assert(complete_at(child, (2 - child.level()) as nat));
            // The child's cell is the lock's for its key, so the key is a node's.
            assert(child.value().lock_const() == t.id_of(pte0));
        }
        unlock_tree(t, Tracked(child), pte0);
    }
    // Child 1 likewise.

    if pte1 != 0 {
        let tracked child;
        proof {
            assert(tree.children()[1] == tree0.children()[1]);
            assert(tree.has_child(1));
            lemma_cells_belong_detach(tree, 1, id);
            let tracked (rest, c) = tracked_detach(tree, 1);
            tree = rest;
            child = c;
            assert(complete_at(child, (2 - child.level()) as nat));
            assert(child.value().lock_const() == t.id_of(pte1));
        }
        unlock_tree(t, Tracked(child), pte1);
    }
    // No child is left: each grafted one was pointed to, and was returned.

    proof {
        assert forall|i: int| 0 <= i < 2 implies !#[trigger] tree.has_child(i) by {
            if i == 0 && pte0 == 0 {
                assert(tree.children()[0] == tree0.children()[0]);
            }
            if i == 1 && pte1 == 0 {
                assert(tree.children()[1] == tree0.children()[1]);
            }
        }
    }
    let tracked cell = tracked_into_cell(tree);
    node.lock.unlock(Tracked(cell));
}

/// Cursor B holds `C` while cursor A locks `P`, then B unlocks `C` and A
/// locks it and assembles both into one ghost tree, as in the first example.
pub fn example_overlapping_cursors(t: &Tree2)
    requires
        t.wf(),
{
    // B: lock `C` directly, as after a lock-free walk down from the root.
    let Tracked(b_c) = t.c.lock.lock();

    // A: lock `P` and read its PTEs, exactly, through its cell.
    let Tracked(a_p) = t.p.lock.lock();
    let pte0 = t.p.read(0, Tracked(&a_p));
    let pte1 = t.p.read(1, Tracked(&a_p));

    // B is done with `C`.
    t.c.lock.unlock(Tracked(b_c));

    if pte0 == t.c.addr && pte1 == 0 {
        // A follows PTE 0 to `C`'s lock.
        let Tracked(a_c) = t.c.lock.lock();
        let ghost (gp, gc) = (a_p, a_c);
        let tracked tree = {
            let tracked tp = tracked_leaf(a_p);
            let tracked tc = tracked_leaf(a_c);
            tracked_graft(tp, 0, tc)
        };
        proof {
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
        unlock_tree(t, Tracked(tree), t.p.addr);
    } else {
        t.p.lock.unlock(Tracked(a_p));
    }
}

/// Cursor A unmaps `C` from `P` while cursor B holds `C`, and a lock-free
/// reader R read `P`'s PTE before the unmap. `C` is now stray. B still
/// unlocks it, and R can still lock it: R's stale PTE value names a node
/// that exists, just no longer one that `P` points to.
pub fn example_stray_child(t: &Tree2)
    requires
        t.wf(),
{
    // R reads P's PTE 0 without any lock.
    let r_pte = t.p.read_unlocked(0);

    let Tracked(b_c) = t.c.lock.lock();

    let Tracked(a_p) = t.p.lock.lock();
    let tracked mut a_p = a_p;
    t.p.write(0, 0, Tracked(&mut a_p));
    t.p.write(1, 0, Tracked(&mut a_p));
    proof {
        assert(a_p.value().child_key(0) is None);
        assert(a_p.value().child_key(1) is None);
    }
    t.p.lock.unlock(Tracked(a_p));

    t.c.lock.unlock(Tracked(b_c));

    // R follows its stale value, and gets whichever node it names.
    if r_pte != 0 {
        let n = t.node(r_pte);
        let Tracked(r_cell) = n.lock.lock();
        n.lock.unlock(Tracked(r_cell));
    }
}

} // verus!
