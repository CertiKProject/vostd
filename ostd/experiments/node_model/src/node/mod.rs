//! Page table node abstractions and the handle.
//!
//! Model of `ostd::src::mm::page_table::node` and
//! `ostd::specs::mm::page_table::node`.
//!
//! A page table node is a frame holding `NR_ENTRIES` page table entries. There
//! are three handle types, and under fractional ownership the distinction
//! between them is carried *in the types*, not by a ghost lock-set:
//!
//! * [`PageTableNode`] — a bare owning handle: an address and nothing else.
//! * [`PageTableNodeRef`] — a borrowed handle that carries a [`NodeFrac`], one
//!   **fraction** of the node's ownership. Enough to read; never enough to
//!   write.
//! * [`PageTableGuard`] — carries the [`NodeOwner`] **outright**, which is
//!   only obtainable once every outstanding fraction has been returned to the
//!   [`NodeAuth`]. This is what makes "only the guard can write a PTE" a
//!   consequence of the ownership algebra rather than a convention.
pub mod child;
pub mod entry;
pub mod entry_owners;
pub mod frac;
pub mod owners;

pub use child::*;
pub use entry::*;
pub use entry_owners::*;
pub use frac::*;
pub use owners::*;

use core::marker::PhantomData;
use core::sync::atomic::Ordering;

use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;

use vstd_extra::array_ptr;
use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::Frame;
use crate::frame::mapping::*;
use crate::pte::*;

verus! {

/// The metadata of a page table page.
///
/// The real type also carries a `lock: PAtomicU8` and a `PhantomData<C>` for
/// the page table configuration; the model has no lock word (mutual exclusion
/// is expressed by the fractions) and no configuration parameter.
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

/// A bare owning handle to a page table node.
///
/// All authority has moved into [`NodeAuth`] / [`NodeFrac`], so this is now
/// just a typed address.
pub type PageTableNode = Frame<PageTablePageMeta>;

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
    /// Allocates a new empty page table node at `level`.
    ///
    /// Still axiomatised — the real body calls the frame allocator, which is
    /// out of scope. But the axiom is now considerably weaker than it was:
    /// because every permission lives inside the returned `NodeOwner`, it can
    /// say nothing at all about any *other* node. Under the old central
    /// region, allocation mutated a shared map, so the axiom had to promise
    /// that no existing slot moved and that the new slot was previously
    /// unused — and callers had to prove parent ≠ child from that. Linearity
    /// now delivers that for free: a freshly minted `NodeOwner` simply cannot
    /// be any live node, because that node's permissions are held elsewhere.
    #[verifier::external_body]
    pub fn alloc(level: PagingLevel) -> (res: (Self, Tracked<NodeOwner>))
        requires
            1 <= level < NR_LEVELS,
        ensures
            res.1@.inv(),
            res.1@.settled(),
            res.1@.level == level,
            res.0.invariants(res.1@),
            res.0.wf_addr(),
            res.0.ptr.addr() == res.1@.meta_vaddr(),
            // The node starts empty.
            res.1@.meta_own.nr_children.value() == 0,
            forall|i: int|
                0 <= i < NR_ENTRIES ==> #[trigger] res.1@.children_perm.value()[i]
                    == Pte::new_absent_spec(),
    {
        unimplemented!()
    }
}

// ─── The borrowed handle ───────────────────────────────────────────────────
/// A borrowed handle to a page table node, carrying one fraction of its
/// ownership.
///
/// The real type is `FrameRef<'a, PageTablePageMeta>`, a `ManuallyDrop<Frame>`
/// plus a lifetime. Here the lifetime is joined by the fraction, which is what
/// actually licenses reading through the handle.
pub struct PageTableNodeRef<'a> {
    pub inner: Frame<PageTablePageMeta>,
    pub frac: Tracked<NodeFrac>,
    pub _marker: PhantomData<&'a ()>,
}

impl<'a> PageTableNodeRef<'a> {
    /// The handle and the fraction name the same node.
    pub open spec fn wf(self) -> bool {
        &&& self.inner.ptr.addr() == self.frac@@.meta_vaddr()
        &&& self.inner.wf_addr()
        // One reference holds exactly one fraction. This is what makes
        // "return every outstanding fraction" a statement about the number of
        // live references.
        &&& self.frac@.frac() == 1
    }

    /// The node this reference names.
    pub open spec fn view(self) -> NodeOwner {
        self.frac@@
    }

    /// Which node's ownership this is a fraction of.
    pub open spec fn id(self) -> vstd::resource::Loc {
        self.frac@.id()
    }
}

#[verus_verify]
impl<'a> PageTableNodeRef<'a> {
    /// Builds a reference from a fraction.
    #[verus_spec(res =>
        with Tracked(frac): Tracked<NodeFrac>,
        requires
            frac@.inv(),
            frac.frac() == 1,
            paddr == frac@.paddr(),
        ensures
            res.wf(),
            res@ == frac@,
            res.id() == frac.id(),
            res.inner.ptr.addr() == frac@.meta_vaddr(),
    )]
    pub fn from_frac(paddr: Paddr) -> Self {
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(frac@.slot_index);
            lemma_index_to_meta_biinjective(frac@.slot_index);
        }
        // SAFETY: the fraction is the entitlement to name this frame.
        let inner = unsafe { Frame::from_raw(paddr) };
        PageTableNodeRef { inner, frac: Tracked(frac), _marker: PhantomData }
    }

    /// Gets the level of the node.
    ///
    /// Compare the old signature, which needed the node's owner *and* the
    /// global region just to read one `u8`. The fraction carried by the handle
    /// supplies both, and its type invariant supplies the well-formedness that
    /// used to be a `meta_bridge` precondition.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.level,
    )]
    pub fn level(&self) -> PagingLevel {
        let tracked owner = self.frac.borrow().borrow();
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.inner.meta();
        meta.level
    }

    /// The physical address of the node's frame.
    #[verus_spec(res =>
        requires
            self.wf(),
        ensures
            res == self@.paddr(),
            valid_frame_paddr(res),
    )]
    pub fn start_paddr(&self) -> Paddr {
        proof {
            broadcast use group_page_meta;

            self.frac.borrow().validate();
            lemma_index_to_meta_biinjective(self@.slot_index);
        }
        self.inner.start_paddr()
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// A *fraction is enough* — this is the read half of the split.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        requires
            self.wf(),
            idx < NR_ENTRIES,
        ensures
            pte == self@.children_perm.value()[idx as int],
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> Pte {
        let tracked owner = self.frac.borrow().borrow();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(owner.slot_index);
            lemma_index_to_meta_biinjective(owner.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        );
        // SAFETY:
        // - The node is alive (we hold a fraction) and the index is in bounds.
        // - All PTEs are aligned and accessed only with atomic operations.
        unsafe {
            #[verus_spec(with Tracked(&owner.children_perm))]
            load_pte(ptr.add(idx), Ordering::Relaxed)
        }
    }

    /// Locks the node, yielding exclusive ownership.
    ///
    /// Axiomatised, as in the real development, which had no verified spin
    /// lock either. But the axiom is now a statement about *ownership* rather
    /// than about a ghost set: it says the lock protocol has brought every
    /// outstanding fraction home, so the caller may take the `NodeOwner`. The
    /// returned guard's node is the one the fraction named.
    ///
    /// See [`Self::into_guard`] for the same step done without an axiom, when
    /// the caller actually holds the authority.
    #[verifier::external_body]
    #[verus_spec(res =>
        requires
            self.wf(),
        ensures
            res.wf(),
            res@ == self@,
            res@.settled(),
    )]
    pub fn lock<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        unimplemented!()
    }

    /// Turns a reference into a guard by returning its fraction to the
    /// authority and taking exclusive ownership once every fraction is home.
    ///
    /// **No axiom.** This is what fractional ownership actually buys: when the
    /// caller holds the authority — as a cursor holding the whole path does —
    /// mutual exclusion is *proved*, not assumed.
    #[verus_spec(res =>
        with Tracked(auth): Tracked<&mut NodeAuth>,
        requires
            self.wf(),
            old(auth).wf(),
            old(auth).id() == self.id(),
            old(auth).frac() > 0,
            // Every other fraction is already home.
            old(auth).frac() + 1 == MAX_REFS,
            old(auth)@ == self@,
            old(auth)@.settled(),
        ensures
            final(auth).wf(),
            final(auth).id() == old(auth).id(),
            final(auth).is_lent_out(),
            res.wf(),
            res@ == old(auth)@,
            res@.settled(),
    )]
    pub fn into_guard<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        let PageTableNodeRef { inner, frac: Tracked(f), .. } = self;
        proof {
            auth.reclaim(f);
            auth.lemma_full_from_frac();
        }
        let tracked owner = auth.into_exclusive();
        PageTableGuard { inner, owner: Tracked(owner), _marker: PhantomData }
    }
}

// ─── The guard ─────────────────────────────────────────────────────────────
/// A guard holding a node's ownership outright.
///
/// Holding a `NodeOwner` rather than a fraction is precisely what permits
/// [`Self::write_pte`]: writing needs `&mut children_perm`, and a fraction can
/// only ever yield `&`.
pub struct PageTableGuard<'rcu> {
    pub inner: Frame<PageTablePageMeta>,
    pub owner: Tracked<NodeOwner>,
    pub _marker: PhantomData<&'rcu ()>,
}

impl<'rcu> PageTableGuard<'rcu> {
    pub open spec fn wf(self) -> bool {
        &&& self.inner.ptr.addr() == self.owner@.meta_vaddr()
        &&& self.inner.wf_addr()
        &&& self.owner@.inv()
    }

    pub open spec fn view(self) -> NodeOwner {
        self.owner@
    }
}

#[verus_verify]
impl<'rcu> PageTableGuard<'rcu> {
    /// Releases the guard, returning ownership to the authority and taking
    /// back a fraction. The inverse of [`PageTableNodeRef::into_guard`].
    #[verus_spec(res =>
        with Tracked(auth): Tracked<&mut NodeAuth>,
        requires
            self.wf(),
            old(auth).wf(),
            old(auth).is_lent_out(),
            self@.slot_index == old(auth).slot_index(),
            self@.level == old(auth).level(),
        ensures
            final(auth).wf(),
            final(auth).id() == old(auth).id(),
            final(auth)@ == self@,
            res.wf(),
            res@ == self@,
            res.id() == final(auth).id(),
    )]
    pub fn unlock<'a>(self) -> PageTableNodeRef<'a> where 'rcu: 'a {
        let PageTableGuard { inner, owner: Tracked(o), .. } = self;
        proof {
            auth.restore(o);
            auth.lemma_full_frac();
        }
        let tracked f = auth.lend();
        PageTableNodeRef { inner, frac: Tracked(f), _marker: PhantomData }
    }

    /// Gets the level of the node.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.level,
    )]
    pub fn level(&self) -> PagingLevel {
        let tracked owner = self.owner.borrow();
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.inner.meta();
        meta.level
    }

    /// Borrows an entry in the node at a given index.
    #[verus_spec(res =>
        requires
            old(self).wf(),
            idx < NR_ENTRIES,
        ensures
            res.idx == idx,
            res.pte == old(self)@.children_perm.value()[idx as int],
            *res.node == *old(self),
            *final(self) == *final(res.node),
    )]
    pub fn entry<'a>(&'a mut self, idx: usize) -> Entry<'a, 'rcu> {
        // SAFETY: the index is within the bound.
        let pte = unsafe { self.read_pte(idx) };
        Entry::new(pte, idx, self)
    }

    /// Gets the number of present PTEs in the node.
    #[verus_spec(nr =>
        requires
            self.wf(),
        returns
            self@.meta_own.nr_children.value(),
    )]
    pub fn nr_children(&self) -> u16 {
        let tracked owner = self.owner.borrow();
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.inner.meta();
        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Sets the number of present PTEs in the node.
    ///
    /// The slot's storage permission and the `PCell` permission now live in
    /// the *same* `NodeOwner`, so this borrows two disjoint fields of one
    /// `&mut` rather than two separate ghost arguments.
    #[verus_spec(
        requires
            old(self).wf(),
            0 <= n <= NR_ENTRIES,
        ensures
            final(self).wf(),
            final(self)@.meta_own.nr_children.value() == n,
            final(self)@.meta_own.nr_children.id() == old(self)@.meta_own.nr_children.id(),
            final(self)@.meta_own.stray == old(self)@.meta_own.stray,
            final(self)@.meta_perm == old(self)@.meta_perm,
            final(self)@.children_perm == old(self)@.children_perm,
            final(self)@.level == old(self)@.level,
            final(self)@.slot_index == old(self)@.slot_index,
            final(self).inner == old(self).inner,
    )]
    pub fn set_nr_children(&mut self, n: u16) {
        let tracked owner = self.owner.borrow_mut();
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.inner.meta();
        meta.nr_children.write(Tracked(&mut owner.meta_own.nr_children), n);
    }

    /// Returns whether the node is detached from its parent.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.meta_own.stray.value(),
    )]
    pub fn stray(&self) -> bool {
        let tracked owner = self.owner.borrow();
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.inner.meta();
        *meta.stray.borrow(Tracked(&owner.meta_own.stray))
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        requires
            self.wf(),
            idx < NR_ENTRIES,
        ensures
            pte == self@.children_perm.value()[idx as int],
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> Pte {
        let tracked owner = self.owner.borrow();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(owner.slot_index);
            lemma_index_to_meta_biinjective(owner.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        );
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
        requires
            old(self).wf(),
            idx < NR_ENTRIES,
        ensures
            final(self).wf(),
            final(self)@.level == old(self)@.level,
            final(self)@.slot_index == old(self)@.slot_index,
            final(self)@.meta_own == old(self)@.meta_own,
            final(self)@.meta_perm == old(self)@.meta_perm,
            final(self)@.children_perm.addr() == old(self)@.children_perm.addr(),
            final(self)@.children_perm.value() == old(self)@.children_perm.value().update(
                idx as int,
                pte,
            ),
            final(self).inner == old(self).inner,
    )]
    pub unsafe fn write_pte(&mut self, idx: usize, pte: Pte) {
        let tracked owner = self.owner.borrow_mut();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(owner.slot_index);
            lemma_index_to_meta_biinjective(owner.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        );
        unsafe {
            #[verus_spec(with Tracked(&mut owner.children_perm))]
            store_pte(ptr.add(idx), pte, Ordering::Release)
        }
    }
}

} // verus!
