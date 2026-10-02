//! Page table node abstractions and the handle.
//!
//! Model of `ostd::src::mm::page_table::node` and
//! `ostd::specs::mm::page_table::node`.
//!
//! A page table node is a frame holding `NR_ENTRIES` page table entries. There
//! are three handle types, and the distinction between them is carried *in
//! the types*, not by a ghost lock-set:
//!
//! * [`PageTableNode`] — a bare owning handle: an address and nothing else.
//! * [`PageTableNodeRef`] — a borrowed handle that carries a [`NodeFrac`], a
//!   **reader**. Enough to read PTEs, but only up to the weak predicate
//!   [`pte_wf`]: a writer may be changing the node concurrently.
//! * [`PageTableGuard`] — a reader *plus* the node's unique [`NodeWriter`].
//!   It knows the node's exact contents and may write them. Readers coexist
//!   with it; another guard cannot.
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
use vstd::invariant::open_atomic_invariant;
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
/// All authority has moved into [`NodeAuth`] / [`NodeFrac`] / [`NodeWriter`],
/// so this is now just a typed address.
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
/// A borrowed handle to a page table node, carrying one reader fraction.
///
/// The real type is `FrameRef<'a, PageTablePageMeta>`, a `ManuallyDrop<Frame>`
/// plus a lifetime. Here the lifetime is joined by the fraction, which is what
/// actually licenses reading through the handle.
pub struct PageTableNodeRef<'a> {
    pub inner: Frame<PageTablePageMeta>,
    pub tracked_frac: Tracked<NodeFrac>,
    pub _marker: PhantomData<&'a ()>,
}

impl<'a> PageTableNodeRef<'a> {
    /// The handle and the fraction name the same node.
    pub open spec fn wf(self) -> bool {
        &&& self.inner.ptr.addr() == self.tracked_frac@@.meta_vaddr()
        &&& self.inner.wf_addr()
        // One reference holds exactly one fraction. This is what makes
        // "return every outstanding fraction" a statement about the number of
        // live references.
        &&& self.tracked_frac@.frac() == 1
    }

    /// The identity of the node this reference names.
    pub open spec fn view(self) -> NodeIdentity {
        self.tracked_frac@@
    }

    /// Which node's ownership this is a fraction of.
    pub open spec fn id(self) -> vstd::resource::Loc {
        self.tracked_frac@.id()
    }
}

#[verus_verify]
impl<'a> PageTableNodeRef<'a> {
    /// Builds a reference from a fraction.
    #[verus_spec(res =>
        with Tracked(frac): Tracked<NodeFrac>,
        requires
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

            frac.validate();
            lemma_index_to_frame_biinjective(frac@.slot_index);
            lemma_index_to_meta_biinjective(frac@.slot_index);
        }
        // SAFETY: the fraction is the entitlement to name this frame.
        let inner = unsafe { Frame::from_raw(paddr) };
        PageTableNodeRef { inner, tracked_frac: Tracked(frac), _marker: PhantomData }
    }

    /// Gets the level of the node.
    ///
    /// The level is part of the node's immutable identity, so a reader knows
    /// it exactly.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.level,
    )]
    pub fn level(&self) -> PagingLevel {
        let tracked ident = self.tracked_frac.borrow().borrow();
        #[verus_spec(with Tracked(&ident.meta_perm))]
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

            self.tracked_frac.borrow().validate();
            lemma_index_to_meta_biinjective(self@.slot_index);
        }
        self.inner.start_paddr()
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// A reader learns only that the PTE is well formed ([`pte_wf`]), not
    /// which PTE it is: a guard elsewhere may be writing the node right now.
    /// This is the guarantee a lock-free reader has in the real code.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        requires
            self.wf(),
            idx < NR_ENTRIES,
        ensures
            pte_wf(pte, self@.level),
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> Pte {
        let tracked ident = self.tracked_frac.borrow().borrow();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(ident.slot_index);
            lemma_index_to_meta_biinjective(ident.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        ).add(idx);
        let pte;
        // SAFETY:
        // - The node is alive (we hold a fraction) and the index is in bounds.
        // - All PTEs are aligned and accessed only with atomic operations.
        open_atomic_invariant!(&ident.ptes => arr => {
            pte = unsafe {
                #[verus_spec(with Tracked(&arr.perm))]
                load_pte(ptr, Ordering::Relaxed)
            };
        });
        pte
    }

    /// Locks the node, yielding its writer.
    ///
    /// Axiomatised, as in the real development, which had no verified spin
    /// lock either. The axiom says the lock protocol hands over the node's
    /// unique [`NodeWriter`]; the reader fraction stays with the handle. The
    /// guard learns the node's exact contents only through the writer, so
    /// all the axiom promises about them is that they are settled.
    ///
    /// Closing this gap means storing the writer in an atomic invariant on
    /// the lock word, as `rwlock.rs` does. See [`Self::into_guard`] for the
    /// same step done without an axiom, when the caller holds the core.
    #[verifier::external_body]
    #[verus_spec(res =>
        requires
            self.wf(),
        ensures
            res.wf(),
            res.id() == self.id(),
            res.identity() == self@,
            res@.settled(),
            res.inner == self.inner,
    )]
    pub fn lock<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        unimplemented!()
    }

    /// Turns a reference into a guard by taking the writer from the core.
    ///
    /// **No axiom**, and — unlike before the reader/writer split — no
    /// requirement that the other readers come home first.
    #[verus_spec(res =>
        with Tracked(auth): Tracked<&mut NodeAuth>,
        requires
            self.wf(),
            old(auth).wf(),
            old(auth).id() == self.id(),
            !old(auth).is_lent_out(),
        ensures
            final(auth).wf(),
            final(auth).id() == old(auth).id(),
            final(auth)@ == old(auth)@,
            final(auth).frac() == old(auth).frac(),
            final(auth).is_lent_out(),
            res.wf(),
            res.id() == self.id(),
            res.identity() == self@,
            res@.settled(),
            res.inner == self.inner,
    )]
    pub fn into_guard<'rcu>(self) -> PageTableGuard<'rcu> where 'a: 'rcu {
        let PageTableNodeRef { inner, tracked_frac: Tracked(f), .. } = self;
        proof {
            auth.agree(&f);
        }
        let tracked w = auth.take_writer();
        PageTableGuard {
            inner,
            tracked_frac: Tracked(f),
            tracked_writer: Tracked(w),
            _marker: PhantomData,
        }
    }
}

// ─── The guard ─────────────────────────────────────────────────────────────
/// A guard holding a reader fraction and the node's writer.
///
/// The writer is precisely what permits [`Self::write_pte`] and
/// [`Self::set_nr_children`], and what lets the guard know the node's exact
/// contents.
pub struct PageTableGuard<'rcu> {
    pub inner: Frame<PageTablePageMeta>,
    pub tracked_frac: Tracked<NodeFrac>,
    pub tracked_writer: Tracked<NodeWriter>,
    pub _marker: PhantomData<&'rcu ()>,
}

impl<'rcu> PageTableGuard<'rcu> {
    pub open spec fn wf(self) -> bool {
        &&& self.inner.ptr.addr() == self.tracked_frac@@.meta_vaddr()
        &&& self.inner.wf_addr()
        &&& self.tracked_frac@.frac() == 1
        &&& self.tracked_writer@.wf_for(self.tracked_frac@@)
    }

    /// Which node this guard holds.
    pub open spec fn id(self) -> vstd::resource::Loc {
        self.tracked_frac@.id()
    }

    /// The node's immutable identity.
    pub open spec fn identity(self) -> NodeIdentity {
        self.tracked_frac@@
    }

    /// Everything the guard knows about the node, exactly.
    pub open spec fn view(self) -> NodeView {
        NodeView {
            level: self.tracked_frac@@.level,
            slot_index: self.tracked_frac@@.slot_index,
            ptes: self.tracked_writer@.contents@,
            nr_children: self.tracked_writer@.meta_own.nr_children.value(),
            stray: self.tracked_writer@.meta_own.stray.value(),
        }
    }
}

#[verus_verify]
impl<'rcu> PageTableGuard<'rcu> {
    /// Releases the guard, returning the writer to the core. The reader
    /// fraction stays with the handle. The inverse of
    /// [`PageTableNodeRef::into_guard`].
    #[verus_spec(res =>
        with Tracked(auth): Tracked<&mut NodeAuth>,
        requires
            self.wf(),
            self@.settled(),
            old(auth).wf(),
            old(auth).id() == self.id(),
            old(auth).is_lent_out(),
        ensures
            final(auth).wf(),
            final(auth).id() == old(auth).id(),
            final(auth)@ == old(auth)@,
            final(auth).frac() == old(auth).frac(),
            !final(auth).is_lent_out(),
            res.wf(),
            res.id() == self.id(),
            res@ == self.identity(),
    )]
    pub fn unlock<'a>(self) -> PageTableNodeRef<'a> where 'rcu: 'a {
        let PageTableGuard { inner, tracked_frac: Tracked(f), tracked_writer: Tracked(w), .. } =
            self;
        proof {
            auth.agree(&f);
            auth.put_writer(w);
        }
        PageTableNodeRef { inner, tracked_frac: Tracked(f), _marker: PhantomData }
    }

    /// Gets the level of the node.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.level,
    )]
    pub fn level(&self) -> PagingLevel {
        let tracked ident = self.tracked_frac.borrow().borrow();
        #[verus_spec(with Tracked(&ident.meta_perm))]
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
            res.pte == old(self)@.ptes[idx as int],
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
            self@.nr_children,
    )]
    pub fn nr_children(&self) -> u16 {
        let tracked ident = self.tracked_frac.borrow().borrow();
        let tracked w = self.tracked_writer.borrow();
        #[verus_spec(with Tracked(&ident.meta_perm))]
        let meta = self.inner.meta();
        *meta.nr_children.borrow(Tracked(&w.meta_own.nr_children))
    }

    /// Sets the number of present PTEs in the node.
    ///
    /// The slot's storage permission comes from the reader fraction, the
    /// `PCell` permission from the writer.
    #[verus_spec(
        requires
            old(self).wf(),
            0 <= n <= NR_ENTRIES,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).identity() == old(self).identity(),
            final(self)@ == (NodeView { nr_children: n, ..old(self)@ }),
            final(self).inner == old(self).inner,
    )]
    pub fn set_nr_children(&mut self, n: u16) {
        let tracked ident = self.tracked_frac.borrow().borrow();
        let tracked w = self.tracked_writer.borrow_mut();
        #[verus_spec(with Tracked(&ident.meta_perm))]
        let meta = self.inner.meta();
        meta.nr_children.write(Tracked(&mut w.meta_own.nr_children), n);
    }

    /// Returns whether the node is detached from its parent.
    #[verus_spec(res =>
        requires
            self.wf(),
        returns
            self@.stray,
    )]
    pub fn stray(&self) -> bool {
        let tracked ident = self.tracked_frac.borrow().borrow();
        let tracked w = self.tracked_writer.borrow();
        #[verus_spec(with Tracked(&ident.meta_perm))]
        let meta = self.inner.meta();
        *meta.stray.borrow(Tracked(&w.meta_own.stray))
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// Unlike [`PageTableNodeRef::read_pte`], the result is *exact*: the
    /// writer's half of the ghost variable pins the array's contents.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        requires
            self.wf(),
            idx < NR_ENTRIES,
        ensures
            pte == self@.ptes[idx as int],
            pte_wf(pte, self@.level),
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> Pte {
        let tracked ident = self.tracked_frac.borrow().borrow();
        let tracked w = self.tracked_writer.borrow();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(ident.slot_index);
            lemma_index_to_meta_biinjective(ident.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        ).add(idx);
        let pte;
        open_atomic_invariant!(&ident.ptes => arr => {
            proof {
                w.contents.agree(&arr.contents);
            }
            pte = unsafe {
                #[verus_spec(with Tracked(&arr.perm))]
                load_pte(ptr, Ordering::Relaxed)
            };
        });
        pte
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
    ///
    /// Requirement 2 is partly checked: the new PTE must satisfy [`pte_wf`],
    /// because concurrent readers are promised it.
    #[verus_spec(
        requires
            old(self).wf(),
            idx < NR_ENTRIES,
            pte_wf(pte, old(self)@.level),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).identity() == old(self).identity(),
            final(self)@ == (NodeView { ptes: old(self)@.ptes.update(idx as int, pte), ..old(self)@ }),
            final(self).inner == old(self).inner,
    )]
    pub unsafe fn write_pte(&mut self, idx: usize, pte: Pte) {
        let tracked ident = self.tracked_frac.borrow().borrow();
        let tracked w = self.tracked_writer.borrow_mut();
        proof {
            broadcast use group_page_meta;

            lemma_index_to_frame_biinjective(ident.slot_index);
            lemma_index_to_meta_biinjective(ident.slot_index);
        }
        let ptr = array_ptr::ArrayPtr::<Pte, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.inner.start_paddr()),
        ).add(idx);
        open_atomic_invariant!(&ident.ptes => arr => {
            let ghost old_ptes = arr.perm.value();
            proof {
                w.contents.update(&mut arr.contents, old_ptes.update(idx as int, pte));
            }
            unsafe {
                #[verus_spec(with Tracked(&mut arr.perm))]
                store_pte(ptr, pte, Ordering::Release)
            };
            proof {
                assert forall|i: int| 0 <= i < NR_ENTRIES implies #[trigger] pte_wf(
                    arr.perm.value()[i],
                    ident.level,
                ) by {
                    if i != idx {
                        assert(arr.perm.value()[i] == old_ptes[i]);
                    }
                }
            }
        });
    }
}

} // verus!
