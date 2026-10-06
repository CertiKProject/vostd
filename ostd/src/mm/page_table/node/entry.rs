// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::prelude::*;

use vstd::simple_pptr::*;

use vstd_extra::cast_ptr;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use crate::{
    mm::{nr_subpage_per_huge, page_prop::PageProperty, page_table::PageTableNodeRef},
    //    sync::RcuDrop,
    //    task::atomic_mode::InAtomicMode,
};

use super::ChildRef;

verus! {

impl<'a, 'rcu, C: PageTableConfig> Entry<'rcu, C> {
    /// Returns if the entry does not map to anything.
    #[rustc_allow_incoherent_impl]
    #[verus_spec]
    pub fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns if the entry maps to a page table node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&EntryOwner<'rcu, C>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>
    )]
    #[verusfmt::skip]
    pub fn is_node(&self) -> (res: bool)
        requires
            owner.inv(),
            self.wf(owner),
            owner.relate_slot_owner(slot_own),
        ensures
            res == (self.pte.is_present() && !self.pte.is_last(owner.node_own.meta_perm@.value().level)),
    {
        let guard = self.node.borrow(Tracked(owner.guard_perm.borrow()));

        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(slot_own),
                                                Tracked(owner.slot_perm.borrow()),
                                                Tracked(owner.node_own.meta_perm.borrow()))]
            guard.level()
        )
    }

    /// Gets a reference to the child.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn to_ref(&self) -> ChildRef<'rcu, C>
        requires
            self.wf(owner),
            owner.inv(),
            old(regions).inv(),
            self.pte.paddr() == meta_to_frame(owner.slot_perm@.addr()),
            owner.slot_perm@.value().wf(
                &old(regions).slot_owners[frame_to_index(self.pte.paddr())],
            ),
            old(regions).dropped_slots.contains_key(frame_to_index(self.pte.paddr())),
            !old(regions).slots.contains_key(frame_to_index(self.pte.paddr())),
    {
        let guard = self.node.borrow(Tracked(owner.guard_perm.borrow()));

        assert(regions.slot_owners.contains_key(frame_to_index(self.pte.paddr())));

        #[verus_spec(with Tracked(regions.slot_owners.tracked_borrow(
            frame_to_index(meta_to_frame(owner.slot_perm@.addr())))),
            Tracked(owner.slot_perm.borrow()),
            Tracked(owner.node_own.meta_perm.borrow()))]
        let level = guard.level();
        // SAFETY:
        //  - The PTE outlives the reference (since we have `&self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(regions))]
        ChildRef::from_pte(&self.pte, level)
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut EntryOwner<'rcu, C>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>
    )]
    pub fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty)
        requires
            old(owner).inv(),
            old(self).wf(&*old(owner)),
            old(owner).relate_slot_owner(slot_own),
            op.requires((old(self).pte.prop(),)),
    {
        if !self.pte.is_present() {
            return;
        }
        let prop = self.pte.prop();
        let new_prop = op(prop);

        /*        if prop == new_prop {
            return;
        }*/

        self.pte.set_prop(new_prop);

        let mut guard = self.node.take(Tracked(owner.guard_perm.borrow_mut()));

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. We replace the PTE with a new one, which differs only in
        //     `PageProperty`, so the level still matches the current
        //     page table node.
        #[verus_spec(with Tracked(&mut owner.node_own), Tracked(slot_own), Tracked(owner.slot_perm.borrow()))]
        guard.write_pte(self.idx, self.pte);

        self.node.put(Tracked(owner.guard_perm.borrow_mut()), guard)
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the level of the new child does not match the
    /// current node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner) : Tracked<&mut EntryOwner<'rcu, C>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>,
            Tracked(nr_children_perm) : Tracked<&mut vstd::cell::PointsTo<u16>>
    )]
    pub fn replace(&mut self, new_child: Child<C>) -> Child<C>
        requires
            old(self).wf(old(owner)),
            old(owner).inv(),
            !old(regions).slots.contains_key(frame_to_index(old(self).pte.paddr())),
            old(regions).dropped_slots.contains_key(frame_to_index(old(self).pte.paddr())),
            new_child is PageTable,
            FRAME_METADATA_RANGE().start <= frame_to_index(new_child.get_node().unwrap().ptr.addr())
                < FRAME_METADATA_RANGE().end,
    {
        /*        match &new_child {
            Child::PageTable(node) => {
                assert_eq!(node.level(), self.node.level() - 1);
            }
            Child::Frame(_, level, _) => {
                assert_eq!(*level, self.node.level());
            }
            Child::None => {}
        }*/
        let mut guard = self.node.take(Tracked(owner.guard_perm.borrow_mut()));

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(slot_own), Tracked(owner.slot_perm.borrow()), Tracked(owner.node_own.meta_perm.borrow()))]
        let level = guard.level();

        #[verus_spec(with Tracked(regions))]
        let old_child = Child::from_pte(self.pte, level);

        if old_child.is_none() && !new_child.is_none() {
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(nr_children_perm));
            nr_children.put(Tracked(nr_children_perm), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(nr_children_perm));
            nr_children.put(Tracked(nr_children_perm), _tmp - 1);
        }
        #[verus_spec(with Some(Tracked(slot_own)), Some(Tracked(owner.slot_perm.borrow())))]
        let new_pte = new_child.into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        guard.write_pte(self.idx, new_pte);

        self.node.put(Tracked(owner.guard_perm.borrow_mut()), guard);

        self.pte = new_pte;

        old_child
    }

    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    ///
    /// The owner of the new node is handed back through `child_own`; it is
    /// the caller's job to file it in its ownership map.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut EntryOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(child_own): Tracked<&mut Option<EntryOwner<'rcu, C>>>
    )]
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    #[verusfmt::skip]
    pub fn alloc_if_none<A: InAtomicMode>(&mut self, guard: &'rcu A)
        -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
        requires
            old(owner).inv(),
            old(self).wf(old(owner)),
            old(regions).inv(),
            *old(child_own) is None,
        ensures
            owner.inv(),
            owner.guard_perm@.pptr() == old(owner).guard_perm@.pptr(),
            owner.node_own.meta_perm@.value().level == old(owner).node_own.meta_perm@.value().level,
            regions.inv(),
            self.idx == old(self).idx,
            self.node == old(self).node,
            res is None ==> *child_own is None && *self == *old(self),
            res is Some ==> {
                &&& *child_own is Some
                &&& child_own.unwrap().inv()
                &&& child_own.unwrap().guard_perm@.pptr() == res.unwrap()
                &&& !child_own.unwrap().node_own.meta_own.stray@.value()
                &&& child_own.unwrap().node_own.meta_perm@.value().level + 1
                    == owner.node_own.meta_perm@.value().level
                &&& self.pte.is_present()
                &&& !self.pte.is_last(owner.node_own.meta_perm@.value().level)
                &&& self.pte.paddr() == meta_to_frame(child_own.unwrap().slot_perm@.pptr().addr())
            },
    {
        unimplemented!()/*
        if !(self.is_none() && self.node.level() > 1) {
            return None;
        }

        let level = self.node.level();
        let new_page = PageTableNode::<C>::alloc(level - 1);

        let paddr = new_page.start_paddr();
        let _ = ManuallyDrop::new(new_page.borrow().lock(guard));

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        unsafe {
            self.node.write_pte(
                self.idx,
                Child::PageTable(RcuDrop::new(new_page)).into_pte(),
            )
        };

        *self.node.nr_children_mut() += 1;

        // SAFETY: The page table won't be dropped before the RCU grace period
        // ends, so it outlives `'rcu`.
        let pt_ref = unsafe { PageTableNodeRef::borrow_paddr(paddr) };
        // SAFETY: The node is locked and there are no other guards.
        Some(unsafe { pt_ref.make_guard_unchecked(guard) })
        */

    }

    /// Splits the entry to smaller pages if it maps to a huge page.
    ///
    /// If the entry does map to a huge page, it is split into smaller pages
    /// mapped by a child page table node. The new child page table node
    /// is returned.
    ///
    /// If the entry does not map to a untracked huge page, the method returns
    /// `None`.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<EntryOwner<C>>
    )]
    #[verifier::external_body]
    #[verusfmt::skip]
    pub fn split_if_mapped_huge<A: InAtomicMode>(&mut self, guard: &'rcu A)
        -> Option<PPtr<PageTableGuard<'rcu, C>>> {
        unimplemented!()/*
        let guard = self.node.borrow(Tracked(owner.guard_perm.borrow()));

        let level = guard.level();

        if !(self.pte.is_last(level) && level > 1) {
            return None;
        }

        let pa = self.pte.paddr();
        let prop = self.pte.prop();

        let new_page = PageTableNode::<C>::alloc(level - 1);
        let mut pt_lock_guard = new_page.borrow().lock(guard);

        for i in 0..nr_subpage_per_huge::<C>() {
            let small_pa = pa + i * page_size::<C>(level - 1);
            let mut entry = pt_lock_guard.entry(i);
            let old = entry.replace(Child::Frame(small_pa, level - 1, prop));
            debug_assert!(old.is_none());
        }

        let paddr = new_page.start_paddr();
        let _ = ManuallyDrop::new(pt_lock_guard);

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        self.node.write_pte(self.idx, Child::PageTable(new_page.into_pte()));

        // SAFETY: The page table won't be dropped before the RCU grace period
        // ends, so it outlives `'rcu`.
        let pt_ref = unsafe { PageTableNodeRef::borrow_paddr(paddr) };
        // SAFETY: The node is locked and there are no other guards.
        Some(pt_ref.make_guard_unchecked(guard))
        */

    }

    /// Create a new entry at the node with guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&EntryOwner<'rcu, C>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>
    )]
    #[verifier::external_body]
    pub fn new_at(guard: PPtr<PageTableGuard<'rcu, C>>, idx: usize) -> (res: Self)
        requires
            owner.inv(),
            owner.guard_perm@.pptr() == guard,
        ensures
            res.idx == idx,
            res.node == guard,
    {
        // SAFETY: The index is within the bound.
        #[verus_spec(with Tracked(&owner.node_own), Tracked(slot_own), Tracked(owner.slot_perm.borrow()))]
        let pte = guard.borrow(Tracked(owner.guard_perm.borrow())).read_pte(idx);
        Self { pte, idx, node: guard }
    }
}

} // verus!
