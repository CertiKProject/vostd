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
//! On the proof side the cached value is related to an [`EntryOwner`] by
//! `match_pte`. Only one `Entry` can exist for a node at a time, which the
//! `&'a mut PageTableGuard` field enforces.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::frame::owners::*;
use crate::node::child::*;
use crate::node::entry_owners::*;
use crate::node::owners::*;
use crate::node::{PageTableGuard, PageTableNode, PageTableNodeRef, Regions};
use crate::pte::Pte;

verus! {

pub struct Entry<'a, 'rcu> {
    /// The cached page table entry.
    pub pte: Pte,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a mut PageTableGuard<'rcu>,
}

impl<'a, 'rcu> OwnerOf for Entry<'a, 'rcu> {
    type Owner = EntryOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.idx < NR_ENTRIES
        &&& owner.match_pte(self.pte, owner.parent_level)
        &&& valid_frame_paddr(self.pte.paddr())
    }
}

impl<'a, 'rcu> Entry<'a, 'rcu> {
    pub open spec fn invariants(self, owner: EntryOwner, regions: Regions) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }

    /// The entry's cached PTE agrees with the parent node's array, and the
    /// guard really is the guard of that parent.
    pub open spec fn node_matching(
        self,
        owner: EntryOwner,
        parent_owner: NodeOwner,
        guard: PageTableGuard<'rcu>,
    ) -> bool {
        &&& parent_owner.level == owner.parent_level
        &&& parent_owner.inv()
        &&& guard.inner.inner.ptr.addr() == parent_owner.meta_vaddr()
        &&& guard.inner.inner.wf(parent_owner)
        &&& owner.match_pte(parent_owner.children_perm.value()[self.idx as int], owner.parent_level)
        &&& self.pte == parent_owner.children_perm.value()[self.idx as int]
    }

    /// What `replace` would have asserted at runtime under `allow_panic`: a
    /// child node must be exactly one level below its parent, and a mapped
    /// frame must be at the parent's level.
    pub open spec fn replace_nonpanic_condition(
        parent_owner: NodeOwner,
        new_owner: EntryOwner,
    ) -> bool {
        if new_owner.is_node() {
            parent_owner.level - 1 == new_owner.node().level
        } else if new_owner.is_frame() {
            parent_owner.level == new_owner.parent_level
        } else {
            true
        }
    }

    /// Everything about the parent that an operation on *one* entry must
    /// leave alone: the other `NR_ENTRIES - 1` PTEs, and the node's identity.
    pub open spec fn parent_perms_preserved(
        self,
        parent_owner0: NodeOwner,
        parent_owner1: NodeOwner,
    ) -> bool {
        &&& forall|i: int|
            0 <= i < NR_ENTRIES && i != self.idx
                ==> #[trigger] parent_owner0.children_perm.value()[i]
                == parent_owner1.children_perm.value()[i]
        &&& parent_owner1.slot_index == parent_owner0.slot_index
        &&& parent_owner1.level == parent_owner0.level
        &&& parent_owner1.meta_own.nr_children.id() == parent_owner0.meta_own.nr_children.id()
        &&& parent_owner1.meta_own.stray == parent_owner0.meta_own.stray
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
            self.wf(*owner),
            owner.inv(),
        returns
            owner.is_absent(),
    )]
    pub fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns whether the entry maps to a page table node.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&EntryOwner>,
             Tracked(parent_owner): Tracked<&NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            owner.inv(),
            self.wf(*owner),
            parent_owner.relate_guard(*self.node),
            parent_owner.inv(),
            parent_owner.level == owner.parent_level,
            regions.inv(),
            parent_owner.metaregion_sound_node(*regions),
        returns
            owner.is_node(),
    )]
    pub fn is_node(&self) -> bool {
        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(parent_owner), Tracked(regions))]
            self.node.inner.inner.level(),
        )
    }

    /// Gets a *reference* to the child.
    ///
    /// Nothing is taken out of the entry, so the region is provably unchanged
    /// — which is what makes this safe to call while other entries are live.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&EntryOwner>,
             Tracked(parent_owner): Tracked<&NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            self.invariants(*owner, *regions),
            self.node_matching(*owner, *parent_owner, *self.node),
            parent_owner.metaregion_sound_node(*regions),
        ensures
            res.invariants(*owner, *regions),
    )]
    pub fn to_ref(&self) -> ChildRef<'rcu> {
        #[verus_spec(with Tracked(parent_owner), Tracked(regions))]
        let level = self.node.inner.inner.level();

        // SAFETY:
        //  - The PTE outlives the reference (we hold `&self`).
        //  - The level matches the current node.
        unsafe {
            #[verus_spec(with Tracked(regions), Tracked(owner))]
            ChildRef::from_pte(&self.pte, level)
        }
    }

    /// Replaces the entry with a new child, returning the old one.
    ///
    /// This is where the node's `nr_children` bookkeeping happens. Note the
    /// order: the counter is adjusted *before* the PTE is written, so between
    /// the two the node's `count_consistent` invariant is momentarily false —
    /// which is exactly why that invariant lives in `metaregion_sound_node`
    /// rather than in `NodeOwner::inv()`.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&Regions>,
             Tracked(owner): Tracked<&EntryOwner>,
             Tracked(new_owner): Tracked<&EntryOwner>,
             Tracked(parent_owner): Tracked<&mut NodeOwner>,
        requires
            old(self).invariants(*owner, *regions),
            new_child.invariants(*new_owner, *regions),
            new_owner.inv(),
            old(self).node_matching(*owner, *old(parent_owner), *old(self).node),
            old(parent_owner).metaregion_sound_node(*regions),
            new_owner.parent_level == owner.parent_level,
            Self::replace_nonpanic_condition(*old(parent_owner), *new_owner),
        ensures
            final(self).invariants(*new_owner, *regions),
            res.invariants(*owner, *regions),
            final(self).node_matching(*new_owner, *final(parent_owner), *final(self).node),
            final(self).idx == old(self).idx,
            *final(self).node == *old(self).node,
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(parent_owner).metaregion_sound_node(*regions),
            res is None <==> owner.is_absent(),
    )]
    pub fn replace(&mut self, new_child: Child) -> Child {
        // For restoring `count_consistent` at the end: snapshot the parent's
        // PTE array before the counter update and the PTE write.
        let ghost cp0 = parent_owner.children_perm.value();

        #[verus_spec(with Tracked(&*parent_owner), Tracked(regions))]
        let level = self.node.inner.inner.level();

        // SAFETY:
        //  - The PTE is not referenced by any `ChildRef` (we hold `&mut self`).
        //  - The level matches the current node.
        let old_child = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(owner))]
            Child::from_pte(self.pte, level)
        };

        let old_is_none = old_child.is_none();
        let new_is_none = new_child.is_none();

        if old_is_none && !new_is_none {
            proof {
                parent_owner.nr_children_absent_slot_bound(self.idx);
            }
            #[verus_spec(with Tracked(regions), Tracked(parent_owner))]
            self.bump_nr_children(1);
        } else if !old_is_none && new_is_none {
            proof {
                parent_owner.nr_children_present_slot_bound(self.idx);
            }
            #[verus_spec(with Tracked(regions), Tracked(parent_owner))]
            self.bump_nr_children(-1);
        }
        #[verus_spec(with Tracked(new_owner), Tracked(regions))]
        let new_pte = new_child.into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child at the node's level.
        //  3. The node takes over ownership of the child.
        unsafe {
            #[verus_spec(with Tracked(parent_owner), Tracked(regions))]
            self.node.write_pte(self.idx, new_pte)
        };

        self.pte = new_pte;

        proof {
            lemma_count_present_upto_update(cp0, NR_ENTRIES as int, self.idx as int, new_pte);
        }

        old_child
    }

    /// Adjusts the parent's `nr_children` by `delta` (which is `1` or `-1`).
    ///
    /// Factored out of [`Self::replace`]; the real code inlines both arms.
    #[verus_spec(
        with Tracked(slot_regions): Tracked<&Regions>,
             Tracked(parent_owner): Tracked<&mut NodeOwner>,
        requires
            slot_regions.inv(),
            old(parent_owner).inv(),
            old(self).node.inner.inner.ptr.addr() == old(parent_owner).meta_vaddr(),
            // Only the metadata bridge is needed, not the full node
            // invariant: `count_consistent` is exactly what this call breaks.
            old(parent_owner).meta_bridge(*slot_regions),
            delta == 1int ==> old(parent_owner).meta_own.nr_children.value() < NR_ENTRIES,
            delta == -1int ==> old(parent_owner).meta_own.nr_children.value() > 0,
            delta == 1int || delta == -1int,
        ensures
            final(parent_owner).inv(),
            final(parent_owner).meta_bridge(*slot_regions),
            final(parent_owner).meta_own.nr_children.value()
                == old(parent_owner).meta_own.nr_children.value() + delta,
            final(parent_owner).meta_own.nr_children.id()
                == old(parent_owner).meta_own.nr_children.id(),
            final(parent_owner).meta_own.stray == old(parent_owner).meta_own.stray,
            final(parent_owner).children_perm == old(parent_owner).children_perm,
            final(parent_owner).level == old(parent_owner).level,
            final(parent_owner).slot_index == old(parent_owner).slot_index,
            final(self).idx == old(self).idx,
            final(self).pte == old(self).pte,
            *final(self).node == *old(self).node,
    )]
    fn bump_nr_children(&mut self, delta: i32) {
        let tracked slot = slot_regions.tracked_borrow_slot(parent_owner.slot_index);
        #[verus_spec(with
            Tracked(slot),
            Ghost(parent_owner.meta_own.nr_children.id())
        )]
        let nr_children = self.node.nr_children_mut();
        let cur = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
        let next = if delta == 1 {
            cur + 1
        } else {
            cur - 1
        };
        nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), next);
    }

    /// Allocates a new child page table node and installs it in this entry.
    ///
    /// Fails (returns `None`) if the entry is already present, or if the
    /// parent is a level 1 node and therefore cannot have child nodes.
    /// Otherwise the lock guard of the *new* node is returned — the node is
    /// locked before its PTE is published, so nobody can reach it first.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner>,
             Tracked(parent_owner): Tracked<&mut NodeOwner>,
             Tracked(regions): Tracked<&mut Regions>,
             Tracked(guards): Tracked<&mut Guards<'rcu>>,
        requires
            old(self).invariants(*old(owner), *old(regions)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(self).node),
            old(parent_owner).metaregion_sound_node(*old(regions)),
        ensures
            final(self).invariants(*final(owner), *final(regions)),
            final(self).node_matching(*final(owner), *final(parent_owner), *final(self).node),
            final(self).idx == old(self).idx,
            *final(self).node == *old(self).node,
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(parent_owner).metaregion_sound_node(*final(regions)),
            // A node is allocated exactly when the entry was absent and the
            // parent can have children at all.
            res is Some <==> (old(owner).is_absent() && old(parent_owner).level > 1),
            old(owner).is_absent() && old(parent_owner).level > 1 ==> {
                &&& final(owner).is_node()
                &&& final(owner).parent_level == old(owner).parent_level
                &&& final(owner).node().level == old(parent_owner).level - 1
                &&& final(owner).node().meta_own.nr_children.value() == 0
                &&& final(guards).lock_held(final(owner).node().meta_vaddr())
                &&& final(owner).node().relate_guard(res->0)
                &&& final(owner).metaregion_sound(*final(regions))
                // Every PTE of the fresh node is absent.
                &&& forall|i: int| 0 <= i < NR_ENTRIES
                    ==> #[trigger] final(owner).node().children_perm.value()[i]
                        == Pte::new_absent_spec()
            },
            !(old(owner).is_absent() && old(parent_owner).level > 1) ==> {
                &&& *final(owner) == *old(owner)
                &&& *final(parent_owner) == *old(parent_owner)
                &&& *final(regions) == *old(regions)
                &&& *final(guards) == *old(guards)
                &&& final(self).pte == old(self).pte
            },
    )]
    pub fn alloc_if_none(&mut self) -> Option<PageTableGuard<'rcu>> {
        let entry_is_present = self.pte.is_present();
        // For restoring `count_consistent` after adding the child below.
        let ghost cp0 = parent_owner.children_perm.value();

        #[verus_spec(with Tracked(&*parent_owner), Tracked(&*regions))]
        let level = self.node.inner.inner.level();

        if entry_is_present || level <= 1 {
            None
        } else {
            proof {
                parent_owner.nr_children_absent_slot_bound(self.idx);
            }

            proof_decl! {
                let tracked mut new_node_owner: NodeOwner;
            }
            #[verus_spec(with Tracked(regions), Tracked(&*guards) => Tracked(new_node_owner))]
            let new_page = PageTableNode::alloc(level - 1);

            proof {
                // The freshly allocated slot was free, so it is not the
                // parent's — the parent's slot is live.
                assert(new_node_owner.slot_index != parent_owner.slot_index);
            }

            let tracked new_slot = regions.tracked_borrow_slot(new_node_owner.slot_index);
            #[verus_spec(with Tracked(new_slot))]
            let paddr = new_page.start_paddr();

            proof_decl! {
                let tracked new_entry_owner = EntryOwner::tracked_new_node(new_node_owner);
            }

            let new_pte = {
                #[verus_spec(with Tracked(&new_entry_owner), Tracked(&*regions))]
                Child::PageTable(new_page).into_pte()
            };
            self.pte = new_pte;

            let pt_ref = unsafe {
                #[verus_spec(with Tracked(&*regions))]
                PageTableNodeRef::borrow_paddr(paddr)
            };

            // Lock before publishing the PTE, so nobody can reach the node
            // through the page table until we are done with it.
            let pt_lock_guard = {
                #[verus_spec(with Tracked(new_entry_owner.tracked_borrow_node()), Tracked(guards))]
                pt_ref.lock()
            };

            // SAFETY:
            //  1. The index is within the bounds.
            //  2. The new PTE is a child node at the correct level.
            //  3. The ownership of the child is passed to the node.
            unsafe {
                #[verus_spec(with Tracked(parent_owner), Tracked(&*regions))]
                self.node.write_pte(self.idx, self.pte)
            };

            #[verus_spec(with Tracked(&*regions), Tracked(parent_owner))]
            self.bump_nr_children(1);

            proof {
                lemma_count_present_upto_update(cp0, NR_ENTRIES as int, self.idx as int, self.pte);
                *owner = new_entry_owner;
            }

            Some(pt_lock_guard)
        }
    }
}

} // verus!
