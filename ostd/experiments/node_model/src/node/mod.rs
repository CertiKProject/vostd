//! Page table node abstractions and the handle.
//!
//! Model of `ostd::src::mm::page_table::node` and
//! `ostd::specs::mm::page_table::node`.
//!
//! A page table node is a frame holding `NR_ENTRIES` page table entries. There
//! are three handle types, and the distinction between them is the point of
//! the module:
//!
//! * [`PageTableNode`] — an *owning* handle. Creating and dropping one changes
//!   the frame's reference count.
//! * [`PageTableNodeRef`] — a *borrowed* handle, tied to a lifetime.
//! * [`PageTableGuard`] — a borrowed handle that additionally holds the node's
//!   lock, and is therefore the only one through which PTEs may be written.
//!
//! Note that `PageTableNode` is read-only: to modify a node you must go
//! through `PageTableNodeRef::lock`.
pub mod child;
pub mod entry;
pub mod entry_owners;
pub mod owners;

pub use child::*;
pub use entry::*;
pub use entry_owners::*;
pub use owners::*;

use core::marker::PhantomData;
use core::ops::Deref;
use core::sync::atomic::Ordering;

use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

use vstd_extra::array_ptr;
use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::frame::owners::*;
use crate::frame::{Frame, FrameRef};
use crate::pte::*;

verus! {

/// The metadata of a page table page.
///
/// The real type also carries a `lock: PAtomicU8` and a `PhantomData<C>` for
/// the page table configuration; the model has neither a lock implementation
/// (see [`Guards`]) nor a configuration parameter.
pub struct PageTablePageMeta {
    /// The number of present PTEs. Mutable only while the lock is held.
    pub nr_children: pcell_maybe_uninit::PCell<u16>,
    /// Whether the node has been detached from its parent.
    ///
    /// A node can be detached while still being read, because page tables are
    /// recycled under RCU. The flag says the parent is recycling this node.
    pub stray: pcell_maybe_uninit::PCell<bool>,
    /// The level of the node. A node cannot be referenced by page tables of
    /// different levels.
    pub level: PagingLevel,
}

/// The metadata region, specialised to page table nodes.
pub type Regions = MetaRegionOwners<PageTablePageMeta>;

/// An owning handle to a page table node.
///
/// Dropping the last one frees the node and its children — which is why the
/// real type is a `Frame`, so the reference count in the metadata slot does
/// the work. The model's `Frame` has no `Drop`, so this is a plain alias with
/// no teardown behaviour.
pub type PageTableNode = Frame<PageTablePageMeta>;

/// A borrowed handle to a page table node.
pub type PageTableNodeRef<'a> = FrameRef<'a, PageTablePageMeta>;

/// A guard that holds the lock of a page table node.
pub struct PageTableGuard<'rcu> {
    pub inner: PageTableNodeRef<'rcu>,
}

impl<'rcu> Deref for PageTableGuard<'rcu> {
    type Target = PageTableNodeRef<'rcu>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl PageTablePageMeta {
    /// Creates the metadata for a fresh, empty node at `level`.
    pub fn new(level: PagingLevel) -> (res: (Self, Tracked<PageMetaOwner>))
        ensures
            res.0.wf(res.1@),
            res.1@.inv(),
            res.1@.nr_children.value() == 0,
            res.1@.stray.value() == false,
            res.0.level == level,
    {
        let (nr_children, Tracked(nr_children_perm)) = pcell_maybe_uninit::PCell::new(0u16);
        let (stray, Tracked(stray_perm)) = pcell_maybe_uninit::PCell::new(false);
        let meta = PageTablePageMeta { nr_children, stray, level };
        let tracked owner = PageMetaOwner { nr_children: nr_children_perm, stray: stray_perm };
        (meta, Tracked(owner))
    }
}

// ─── The owning handle ─────────────────────────────────────────────────────
#[verus_verify]
impl PageTableNode {
    /// Gets the level of a page table node.
    ///
    /// Reading the level means reading the node's metadata slot, so the caller
    /// must hand over both the node's owner (to know *which* slot) and the
    /// region (which is where the slot's permission is parked).
    #[verus_spec(
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            regions.inv(),
            self.ptr.addr() == owner.meta_vaddr(),
            owner.meta_bridge(*regions),
        returns
            owner.level,
    )]
    pub fn level(&self) -> PagingLevel {
        let tracked slot = regions.tracked_borrow_slot(owner.slot_index);
        #[verus_spec(with Tracked(&slot.meta_perm))]
        let meta = self.meta();
        meta.level
    }

    /// Allocates a new empty page table node at `level`.
    ///
    /// Axiomatised. The real body calls the frame allocator, which is out of
    /// the model's scope; what matters to the node layer is the *shape* of the
    /// result, spelled out in the ensures:
    ///
    /// * a slot that was `Unused` becomes `PageTable` and live, and no other
    ///   slot is touched;
    /// * the fresh node is unlocked, at `level`, with all `NR_ENTRIES` PTEs
    ///   absent and `nr_children == 0`;
    /// * because the slot was previously `Unused`, its index differs from
    ///   every live node's — which is what gives `alloc_if_none` the
    ///   parent ≠ child distinctness it needs.
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut Regions>,
             Tracked(guards): Tracked<&Guards<'rcu>>,
                 -> owner: Tracked<NodeOwner>,
        requires
            1 <= level < NR_LEVELS,
            old(regions).inv(),
        ensures
            final(regions).inv(),
            owner@.inv(),
            owner@.level == level,
            owner@.metaregion_sound_node(*final(regions)),
            res.invariants(owner@),
            res.wf_addr(),
            res.ptr.addr() == owner@.meta_vaddr(),
            // The node starts empty.
            owner@.meta_own.nr_children.value() == 0,
            forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] owner@.children_perm.value()[i]
                == Pte::new_absent_spec(),
            // The node starts unlocked.
            guards.unlocked(owner@.meta_vaddr()),
            // The slot was free before, so it is nobody else's.
            old(regions).contains(owner@.slot_index),
            !old(regions).slots[owner@.slot_index].is_live(),
            // Nothing else in the region moved.
            forall|i: int| #[trigger] old(regions).slots.contains_key(i) && i != owner@.slot_index
                ==> final(regions).slots[i] == old(regions).slots[i],
    )]
    pub fn alloc<'rcu>(level: PagingLevel) -> Self {
        unimplemented!()
    }
}

// ─── The borrowed handle ───────────────────────────────────────────────────
#[verus_verify]
impl<'a> PageTableNodeRef<'a> {
    /// Every lock that was held stays held, every node that was unlocked stays
    /// unlocked except the one just locked.
    pub open spec fn locks_preserved_except<'rcu>(
        addr: Vaddr,
        guards0: Guards<'rcu>,
        guards1: Guards<'rcu>,
    ) -> bool {
        &&& forall|i: Vaddr| guards0.lock_held(i) ==> guards1.lock_held(i)
        &&& forall|i: Vaddr| guards0.unlocked(i) && i != addr ==> guards1.unlocked(i)
    }

    /// Locks the page table node.
    ///
    /// The `'rcu` guard is required to prevent deadlocks and to provide a
    /// lifetime that the node is guaranteed to outlive.
    ///
    /// Axiomatised: there is no spin lock implementation in the model (nor in
    /// the real development at the time it was verified), so acquiring the
    /// lock is modelled as inserting the node's address into [`Guards`].
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(guards): Tracked<&mut Guards<'rcu>>,
        requires
            self.inner.invariants(*owner),
            old(guards).unlocked(owner.meta_vaddr()),
        ensures
            final(guards).lock_held(owner.meta_vaddr()),
            Self::locks_preserved_except(owner.meta_vaddr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub fn lock<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        unimplemented!()
    }

    /// Creates a guard without checking whether the lock is held.
    ///
    /// # Safety
    ///
    /// The caller must logically hold the lock already, and must not have a
    /// live guard for the same node.
    ///
    /// Unlike [`Self::lock`] this one has a real body: the guard is just a
    /// wrapper, and the ghost ledger is updated in a `proof` block.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(guards): Tracked<&mut Guards<'rcu>>,
        requires
            self.inner.invariants(*owner),
            old(guards).unlocked(owner.meta_vaddr()),
        ensures
            final(guards).lock_held(owner.meta_vaddr()),
            Self::locks_preserved_except(owner.meta_vaddr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub unsafe fn make_guard_unchecked<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        let guard = PageTableGuard { inner: self };
        proof {
            guards.guards = guards.guards.insert(owner.meta_vaddr());
        }
        guard
    }
}

// ─── The guard ─────────────────────────────────────────────────────────────
#[verus_verify]
impl<'rcu> PageTableGuard<'rcu> {
    /// Borrows an entry in the node at a given index.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(child_owner): Tracked<&EntryOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            owner.inv(),
            child_owner.inv(),
            owner.relate_guard(*old(self)),
            owner.meta_bridge(*regions),
            child_owner.match_pte(owner.children_perm.value()[idx as int], owner.level),
            child_owner.parent_level == owner.level,
            regions.inv(),
            idx < NR_ENTRIES,
        ensures
            res.wf(*child_owner),
            res.idx == idx,
            res.pte == owner.children_perm.value()[idx as int],
            *res.node == *old(self),
            *final(self) == *final(res.node),
            owner.relate_guard(*res.node),
    )]
    pub fn entry<'a>(&'a mut self, idx: usize) -> Entry<'a, 'rcu> {
        // SAFETY: the index is within the bound.
        let pte = unsafe {
            #[verus_spec(with Tracked(owner), Tracked(regions))]
            self.read_pte(idx)
        };
        Entry::new(pte, idx, self)
    }

    /// Gets the number of present PTEs in the node.
    #[verus_spec(nr =>
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            regions.inv(),
            owner.inv(),
            self.inner.inner.ptr.addr() == owner.meta_vaddr(),
            owner.meta_bridge(*regions),
        returns
            owner.meta_own.nr_children.value(),
    )]
    pub fn nr_children(&self) -> u16 {
        let tracked slot = regions.tracked_borrow_slot(owner.slot_index);
        #[verus_spec(with Tracked(&slot.meta_perm))]
        let meta = self.inner.inner.meta();
        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Gets a handle to the `nr_children` cell so it can be written.
    ///
    /// Taking `&mut self` is what encodes "the lock is held, so we have
    /// exclusive access".
    #[verus_spec(res =>
        with Tracked(slot): Tracked<&'a MetaSlotOwner<PageTablePageMeta>>,
             Ghost(nr_children_id): Ghost<vstd::cell::CellId>,
        requires
            slot.inv(),
            old(self).inner.inner.ptr.addr() == slot.meta_perm.addr(),
            slot.meta_perm.value().nr_children.id() == nr_children_id,
        ensures
            res.id() == nr_children_id,
            *final(self) == *old(self),
    )]
    pub fn nr_children_mut<'a>(&'a mut self) -> &'a pcell_maybe_uninit::PCell<u16> {
        #[verus_spec(with Tracked(&slot.meta_perm))]
        let meta = self.inner.inner.meta();
        &meta.nr_children
    }

    /// Returns whether the node is detached from its parent.
    #[verus_spec(res =>
        with Tracked(slot): Tracked<&'a MetaSlotOwner<PageTablePageMeta>>,
             Ghost(stray_id): Ghost<vstd::cell::CellId>,
        requires
            slot.inv(),
            old(self).inner.inner.ptr.addr() == slot.meta_perm.addr(),
            slot.meta_perm.value().stray.id() == stray_id,
        ensures
            res.id() == stray_id,
            *final(self) == *old(self),
    )]
    pub fn stray_mut<'a>(&'a mut self) -> &'a pcell_maybe_uninit::PCell<bool> {
        #[verus_spec(with Tracked(&slot.meta_perm))]
        let meta = self.inner.inner.meta();
        &meta.stray
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// "Non-owning" means the returned value does not account for a reference
    /// count: the PTE still owns whatever it points at.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        with Tracked(owner): Tracked<&NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            regions.inv(),
            owner.inv(),
            self.inner.inner.ptr.addr() == owner.meta_vaddr(),
            owner.meta_bridge(*regions),
            idx < NR_ENTRIES,
        ensures
            pte == owner.children_perm.value()[idx as int],
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> Pte {
        let tracked slot = regions.tracked_borrow_slot(owner.slot_index);
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(owner.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(slot))]
                self.inner.inner.start_paddr(),
            ),
        );
        // SAFETY:
        // - The node is alive and the index is in bounds, so the PTE is valid.
        // - All PTEs are aligned and accessed only with atomic operations.
        unsafe {
            #[verus_spec(with Tracked(&owner.children_perm))]
            load_pte(ptr.add(idx), Ordering::Relaxed)
        }
    }

    /// Writes a page table entry at a given index.
    ///
    /// This operation will leak the old child if the old PTE was present.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  1. the index is within the bound;
    ///  2. the PTE represents a valid child whose level is compatible with
    ///     this node;
    ///  3. the node takes over ownership of that child.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut NodeOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            regions.inv(),
            old(owner).inv(),
            old(self).inner.inner.ptr.addr() == old(owner).meta_vaddr(),
            old(owner).meta_bridge(*regions),
            idx < NR_ENTRIES,
        ensures
            final(owner).inv(),
            final(owner).level == old(owner).level,
            final(owner).meta_own == old(owner).meta_own,
            final(owner).slot_index == old(owner).slot_index,
            final(owner).children_perm.addr() == old(owner).children_perm.addr(),
            final(owner).children_perm.value() == old(owner).children_perm.value().update(
                idx as int,
                pte,
            ),
            *final(self) == *old(self),
    )]
    pub unsafe fn write_pte(&mut self, idx: usize, pte: Pte) {
        let tracked slot = regions.tracked_borrow_slot(owner.slot_index);
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(owner.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(slot))]
                self.inner.inner.start_paddr(),
            ),
        );
        // SAFETY: as for `read_pte`, plus the caller's obligations above.
        unsafe {
            #[verus_spec(with Tracked(&mut owner.children_perm))]
            store_pte(ptr.add(idx), pte, Ordering::Release)
        }
    }
}

} // verus!
