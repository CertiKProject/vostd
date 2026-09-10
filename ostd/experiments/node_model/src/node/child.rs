//! The children of a page table node.
//!
//! Model of `ostd::src::mm::page_table::node::child` and
//! `ostd::specs::mm::page_table::node::child`.
//!
//! [`Child`] and [`ChildRef`] are the *typed* views of a PTE: instead of a raw
//! word, a tagged union saying whether the entry holds a child node, a mapped
//! frame, or nothing. The two conversions are the interesting part:
//!
//! * [`Child::into_pte`] consumes a child and hands its ownership to the PTE;
//! * [`Child::from_pte`] takes ownership back out of a PTE.
//!
//! `ChildRef` is the borrowing counterpart: it looks at a PTE without taking
//! anything out of it, which is why its `from_pte` provably leaves the region
//! unchanged.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::Frame;
use crate::frame::mapping::*;
use crate::frame::owners::*;
use crate::node::entry_owners::*;
use crate::node::owners::*;
use crate::node::{PageTableNode, PageTableNodeRef, PageTablePageMeta, Regions};
use crate::page_prop::PageProperty;
use crate::pte::Pte;

verus! {

/// A page table entry that *owns* the child of a node, if present.
pub enum Child {
    /// A child page table node.
    PageTable(PageTableNode),
    /// The physical address of a mapped frame, with the level of the mapping
    /// node (which fixes the frame's size) and the mapping properties.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl OwnerOf for Child {
    type Owner = EntryOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node().meta_vaddr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame().mapped_pa == paddr
                &&& owner.frame().prop == prop
                &&& level == owner.parent_level
            },
            Self::None => owner.is_absent(),
        }
    }
}

impl Child {
    pub open spec fn invariants(self, owner: EntryOwner, regions: Regions) -> bool {
        &&& owner.inv_base()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }
}

#[verus_verify]
impl Child {
    /// Returns whether the child is not present.
    #[verus_spec(b =>
        returns
            self is None,
    )]
    pub fn is_none(&self) -> bool {
        matches!(self, Child::None)
    }

    /// Converts the child into a raw PTE value.
    ///
    /// Ownership of the child is transferred *into* the PTE: after this call
    /// the `Child` is gone and the page table node is the sole owner. In the
    /// real code this is where the reference-count bookkeeping happens (the
    /// node handle is `ManuallyDrop`ped so its `Drop` does not run); the model
    /// has no `Drop`, so the region is provably untouched.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&EntryOwner>,
             Tracked(regions): Tracked<&Regions>,
        requires
            self.invariants(*owner, *regions),
            owner.inv(),
        ensures
            owner.pte_invariants(res, *regions),
            owner.is_node() ==> res == Pte::new_pt_spec(owner.node().paddr()),
            owner.is_absent() ==> res == Pte::new_absent_spec(),
            res.is_present() <==> !owner.is_absent(),
    )]
    pub fn into_pte(self) -> Pte {
        proof {
            broadcast use Pte::group_pte_laws;
            broadcast use group_page_meta;

        }
        match self {
            Child::PageTable(node) => {
                let tracked slot = regions.tracked_borrow_slot(owner.node().slot_index);
                proof {
                    lemma_index_to_meta_biinjective(owner.node().slot_index);
                    lemma_index_to_frame_biinjective(owner.node().slot_index);
                }
                #[verus_spec(with Tracked(slot))]
                let paddr = node.start_paddr();
                Pte::new_pt(paddr)
            },
            Child::Frame(paddr, level, prop) => { Pte::new_page(paddr, level, prop) },
            Child::None => { Pte::new_absent() },
        }
    }

    /// Converts a PTE back into an owning `Child`.
    ///
    /// # Safety
    ///
    /// The PTE must have been produced by [`Self::into_pte`] (or an equivalent
    /// that forgot the original handle), and `level` must be the level of the
    /// node that holds it. Ownership moves out of the PTE into the result.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&Regions>,
             Tracked(entry_own): Tracked<&EntryOwner>,
        requires
            entry_own.pte_invariants(pte, *regions),
            level == entry_own.parent_level,
        ensures
            res.invariants(*entry_own, *regions),
            res is None <==> entry_own.is_absent(),
            res is PageTable <==> entry_own.is_node(),
    )]
    pub unsafe fn from_pte(pte: Pte, level: PagingLevel) -> Self {
        if !pte.is_present() {
            return Child::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use group_page_meta;

                regions.lemma_contains_valid_frame_paddr(paddr);
                lemma_index_to_meta_biinjective(entry_own.node().slot_index);
            }
            let node = unsafe {
                #[verus_spec(with Tracked(regions))]
                PageTableNode::from_raw(paddr)
            };
            return Child::PageTable(node);
        }
        Child::Frame(paddr, level, pte.prop())
    }
}

/// A *borrowed* reference to the child of a page table node.
///
/// A child node must be represented by a [`PageTableNodeRef`], because a
/// reference to it is potentially shared and needs a lifetime. A mapped frame,
/// by contrast, can be described by value, and an absent entry is just a tag.
pub enum ChildRef<'a> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a>),
    /// A mapped frame, as in [`Child::Frame`].
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a> OwnerOf for ChildRef<'a> {
    type Owner = EntryOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.inner.ptr.addr() == owner.node().meta_vaddr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame().mapped_pa == paddr
                &&& owner.frame().prop == prop
            },
            Self::None => owner.is_absent(),
        }
    }
}

impl ChildRef<'_> {
    pub open spec fn invariants(self, owner: EntryOwner, regions: Regions) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }
}

#[verus_verify]
impl ChildRef<'_> {
    /// Converts a PTE to a *reference* to its child.
    ///
    /// # Safety
    ///
    /// The PTE must outlive the reference (guaranteed here by taking `&Pte`),
    /// and `level` must match the containing node.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&Regions>,
             Tracked(entry_owner): Tracked<&EntryOwner>,
        requires
            entry_owner.pte_invariants(*pte, *regions),
            level == entry_owner.parent_level,
        ensures
            res.invariants(*entry_owner, *regions),
            res is None <==> entry_owner.is_absent(),
            res is PageTable <==> entry_owner.is_node(),
    )]
    pub unsafe fn from_pte(pte: &Pte, level: PagingLevel) -> Self {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use group_page_meta;

                regions.lemma_contains_valid_frame_paddr(paddr);
                lemma_index_to_meta_biinjective(entry_owner.node().slot_index);
            }
            let node = unsafe {
                #[verus_spec(with Tracked(regions))]
                PageTableNodeRef::borrow_paddr(paddr)
            };
            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
