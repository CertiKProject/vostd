//! Accessors to the page table entries in a node.
//!
//! Model of `ostd::src::mm::page_table::node::entry` and
//! `ostd::specs::mm::page_table::node::entry`.
//!
//! An [`Entry`] is a mutable handle to one PTE of a locked node. It caches the
//! PTE value rather than holding a `&mut Pte`, because other CPUs may write
//! the accessed/dirty bits of the same word concurrently — a `&mut` would
//! violate Rust's aliasing rules.
//!
//! Note how much of the ghost plumbing has gone. The parent node's ownership
//! rides inside the `&mut PageTableGuard`, so there is no `parent_owner`
//! argument, and there is no region argument at all — only the entry's own
//! [`EntryOwner`] is threaded through.
use vstd::modes::tracked_swap;
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::node::child::*;
use crate::node::entry_owners::*;
use crate::node::frac::*;
use crate::node::owners::*;
use crate::node::{PageTableGuard, PageTableNode};
use crate::pte::Pte;

verus! {

pub struct Entry<'a, 'rcu> {
    /// The cached page table entry.
    pub pte: Pte,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry — and, via its `Tracked<NodeOwner>`,
    /// the parent's ownership.
    pub node: &'a mut PageTableGuard<'rcu>,
}

impl<'a, 'rcu> Entry<'a, 'rcu> {
    /// Everything that must hold of an entry and its owner.
    ///
    /// This merges what used to be `invariants` + `node_matching`: since the
    /// guard now carries the parent's `NodeOwner`, the two are no longer
    /// separable.
    pub open spec fn invariants(self, owner: EntryOwner) -> bool {
        &&& self.idx < NR_ENTRIES
        &&& self.node.wf()
        &&& owner.inv()
        &&& owner.parent_level == self.node.owner@.level
        &&& self.pte == self.node.owner@.children_perm.value()[self.idx as int]
        &&& owner.match_pte(self.pte, owner.parent_level)
    }

    /// What `replace` would have asserted at runtime under `allow_panic`: a
    /// child node must be exactly one level below its parent, and a mapped
    /// frame must be at the parent's level.
    pub open spec fn replace_nonpanic_condition(parent: NodeOwner, new_owner: EntryOwner) -> bool {
        if new_owner.is_node() {
            parent.level - 1 == new_owner.node().level()
        } else if new_owner.is_frame() {
            parent.level == new_owner.parent_level
        } else {
            true
        }
    }

    /// Everything about the parent that an operation on *one* entry must
    /// leave alone: the other `NR_ENTRIES - 1` PTEs, and the node's identity.
    pub open spec fn parent_perms_preserved(self, p0: NodeOwner, p1: NodeOwner) -> bool {
        &&& forall|i: int|
            0 <= i < NR_ENTRIES && i != self.idx ==> #[trigger] p0.children_perm.value()[i]
                == p1.children_perm.value()[i]
        &&& p1.slot_index == p0.slot_index
        &&& p1.level == p0.level
        &&& p1.meta_own.nr_children.id() == p0.meta_own.nr_children.id()
        &&& p1.meta_own.stray == p0.meta_own.stray
    }
}

#[verus_verify]
impl<'a, 'rcu> Entry<'a, 'rcu> {
    #[verus_spec(res =>
        ensures
            res.pte == pte,
            res.idx == idx,
            *res.node == *old(node),
            *final(node) == *final(res.node),
    )]
    pub fn new(pte: Pte, idx: usize, node: &'a mut PageTableGuard<'rcu>) -> Self {
        Self { pte, idx, node }
    }

    /// Returns whether the entry does not map anything.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&EntryOwner>,
        requires
            self.invariants(*owner),
        returns
            owner.is_absent(),
    )]
    pub fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns whether the entry maps to a page table node.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&EntryOwner>,
        requires
            self.invariants(*owner),
        returns
            owner.is_node(),
    )]
    pub fn is_node(&self) -> bool {
        self.pte.is_present() && !self.pte.is_last(self.node.level())
    }

    /// Gets a *reference* to the child.
    ///
    /// Takes `&mut EntryOwner` because producing a `ChildRef` means lending a
    /// fraction out of the child's authority. The child must therefore have a
    /// spare fraction — expressed as `frac() > 1`, the fractional analogue of
    /// "the reference count has not saturated".
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner>,
        requires
            self.invariants(*old(owner)),
            old(owner).is_node() ==> {
                &&& !old(owner).node().is_lent_out()
                &&& old(owner).node().frac() > 1
            },
        ensures
            res.invariants(*final(owner)),
            final(owner).parent_level == old(owner).parent_level,
            final(owner).is_node() == old(owner).is_node(),
            final(owner).is_absent() == old(owner).is_absent(),
            final(owner).match_pte(self.pte, final(owner).parent_level),
    )]
    pub fn to_ref(&self) -> ChildRef<'rcu> {
        let level = self.node.level();
        // SAFETY:
        //  - The PTE outlives the reference (we hold `&self`).
        //  - The level matches the current node.
        unsafe {
            #[verus_spec(with Tracked(owner))]
            ChildRef::from_pte(&self.pte, level)
        }
    }

    /// Replaces the entry with a new child, returning the old one.
    ///
    /// This is where the node's `nr_children` bookkeeping happens. Note the
    /// order: the counter is adjusted *before* the PTE is written, so between
    /// the two the node's `settled()` invariant is momentarily false — which
    /// is exactly why that clause lives in [`NodeOwner::settled`] rather than
    /// in `NodeOwner::inv()`, and hence why a [`NodeFrac`] never promises it.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner>,
             Tracked(new_owner): Tracked<EntryOwner>,
                 -> old_owner: Tracked<EntryOwner>,
        requires
            old(self).invariants(*old(owner)),
            old(self).node.owner@.settled(),
            new_child.invariants(new_owner),
            new_owner.inv(),
            new_owner.parent_level == old(owner).parent_level,
            Self::replace_nonpanic_condition(old(self).node.owner@, new_owner),
        ensures
            final(self).invariants(*final(owner)),
            final(self).node.owner@.settled(),
            *final(owner) == new_owner,
            old_owner@ == *old(owner),
            res.invariants(old_owner@),
            final(self).idx == old(self).idx,
            final(self).parent_perms_preserved(old(self).node.owner@, final(self).node.owner@),
            res is None <==> old(owner).is_absent(),
    )]
    pub fn replace(&mut self, new_child: Child) -> Child {
        // Snapshot the parent's PTE array before the counter update and the
        // PTE write, for restoring `settled()` at the end.
        let ghost cp0 = self.node.owner@.children_perm.value();

        let level = self.node.level();

        // SAFETY:
        //  - The PTE is not referenced by any `ChildRef` (we hold `&mut self`).
        //  - The level matches the current node.
        let old_child = unsafe {
            #[verus_spec(with Tracked(&*owner))]
            Child::from_pte(self.pte, level)
        };

        let old_is_none = old_child.is_none();
        let new_is_none = new_child.is_none();
        let cur = self.node.nr_children();

        if old_is_none && !new_is_none {
            proof {
                self.node.owner@.nr_children_absent_slot_bound(self.idx);
            }
            self.node.set_nr_children(cur + 1);
        } else if !old_is_none && new_is_none {
            proof {
                self.node.owner@.nr_children_present_slot_bound(self.idx);
            }
            self.node.set_nr_children(cur - 1);
        }
        let new_pte = {
            #[verus_spec(with Tracked(&new_owner))]
            new_child.into_pte()
        };

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child at the node's level.
        //  3. The node takes over ownership of the child.
        unsafe { self.node.write_pte(self.idx, new_pte) };

        self.pte = new_pte;

        proof_decl! {
            // `out` starts life holding the *new* owner; the swap below leaves
            // the new owner in `*owner` and hands the old one back out.
            let tracked mut out = new_owner;
        }
        proof {
            lemma_count_present_upto_update(cp0, NR_ENTRIES as int, self.idx as int, new_pte);
            tracked_swap(owner, &mut out);
        }
        proof_with!(|= Tracked(out));

        old_child
    }

    /// Allocates a new child page table node and installs it in this entry.
    ///
    /// Fails (returns `None`) if the entry is already present, or if the
    /// parent is a level 1 node and therefore cannot have child nodes.
    /// Otherwise the lock guard of the *new* node is returned.
    ///
    /// # No lock axiom
    ///
    /// The guard is produced by [`NodeAuth::into_exclusive`], which is
    /// **proved**, not assumed: a node that has just been allocated has every
    /// one of its fractions still at home, so exclusive access follows from
    /// the ownership algebra. The old model reached for the axiomatised
    /// `lock()` here.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner>,
        requires
            old(self).invariants(*old(owner)),
            old(self).node.owner@.settled(),
        ensures
            final(self).invariants(*final(owner)),
            final(self).node.owner@.settled(),
            final(self).idx == old(self).idx,
            final(self).parent_perms_preserved(old(self).node.owner@, final(self).node.owner@),
            res is Some <==> (old(owner).is_absent() && old(self).node.owner@.level > 1),
            old(owner).is_absent() && old(self).node.owner@.level > 1 ==> {
                &&& final(owner).is_node()
                &&& final(owner).parent_level == old(owner).parent_level
                &&& final(owner).node().level() == old(self).node.owner@.level - 1
                &&& final(owner).node().is_lent_out()
                &&& res->0.wf()
                &&& res->0@.settled()
                &&& res->0@.level == old(self).node.owner@.level - 1
                &&& res->0@.meta_own.nr_children.value() == 0
                // Every PTE of the fresh node is absent.
                &&& forall|i: int| 0 <= i < NR_ENTRIES
                    ==> #[trigger] res->0@.children_perm.value()[i] == Pte::new_absent_spec()
            },
            !(old(owner).is_absent() && old(self).node.owner@.level > 1) ==> {
                &&& *final(owner) == *old(owner)
                &&& final(self).pte == old(self).pte
                &&& final(self).node.owner@ == old(self).node.owner@
            },
    )]
    pub fn alloc_if_none(&mut self) -> Option<PageTableGuard<'rcu>> {
        let entry_is_present = self.pte.is_present();
        let ghost cp0 = self.node.owner@.children_perm.value();
        let level = self.node.level();

        if entry_is_present || level <= 1 {
            None
        } else {
            proof {
                self.node.owner@.nr_children_absent_slot_bound(self.idx);
            }

            let (new_page, Tracked(new_node_owner)) = PageTableNode::alloc(level - 1);
            let paddr = new_page.start_paddr();

            proof {
                broadcast use group_page_meta;

                lemma_index_to_meta_biinjective(new_node_owner.slot_index);
                lemma_index_to_frame_biinjective(new_node_owner.slot_index);
            }

            // Take the authority, then immediately take exclusive ownership.
            // Proved, not axiomatised: nothing else holds a fraction yet.
            let tracked mut auth = NodeAuth::alloc(new_node_owner);
            let tracked exclusive = auth.into_exclusive();
            let guard = PageTableGuard {
                inner: new_page,
                owner: Tracked(exclusive),
                _marker: core::marker::PhantomData,
            };

            // Publish the PTE only after the node is exclusively held.
            let new_pte = Pte::new_pt(paddr);
            proof {
                broadcast use Pte::group_pte_laws;

            }
            unsafe { self.node.write_pte(self.idx, new_pte) };
            self.pte = new_pte;

            let cur = self.node.nr_children();
            self.node.set_nr_children(cur + 1);

            proof {
                lemma_count_present_upto_update(cp0, NR_ENTRIES as int, self.idx as int, new_pte);
                let tracked mut installed = EntryOwner::tracked_new_node(auth);
                tracked_swap(owner, &mut installed);
            }

            Some(guard)
        }
    }
}

} // verus!
