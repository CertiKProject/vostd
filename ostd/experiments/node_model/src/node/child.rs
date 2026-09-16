//! The children of a page table node.
//!
//! Model of `ostd::src::mm::page_table::node::child` and
//! `ostd::specs::mm::page_table::node::child`.
//!
//! [`Child`] and [`ChildRef`] are the *typed* views of a PTE: instead of a raw
//! word, a tagged union saying whether the entry holds a child node, a mapped
//! frame, or nothing.
//!
//! The owning/borrowing distinction is now visible in what each conversion
//! needs from the entry's owner:
//!
//! * [`Child::from_pte`] rebuilds an *owning* handle, which under fractional
//!   ownership is a bare address — so a shared `&EntryOwner` suffices.
//! * [`ChildRef::from_pte`] rebuilds a *borrowing* handle, which must carry a
//!   fraction — so it takes `&mut EntryOwner` and lends one out of the child's
//!   authority.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::node::entry_owners::*;
use crate::node::frac::*;
use crate::node::{PageTableNode, PageTableNodeRef};
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
    pub open spec fn invariants(self, owner: EntryOwner) -> bool {
        &&& owner.inv_base()
        &&& self.wf(owner)
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
    /// Ownership of the child is transferred *into* the PTE. In the real code
    /// this is where reference-count bookkeeping happens; here the child's
    /// authority simply stays in the `EntryOwner`, which is why this needs
    /// only a shared borrow and can promise it disturbs nothing.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&EntryOwner>,
        requires
            self.invariants(*owner),
            owner.inv(),
        ensures
            owner.pte_invariants(res),
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
                proof {
                    owner.node().lemma_identity();
                    lemma_index_to_meta_biinjective(owner.node().slot_index());
                    lemma_index_to_frame_biinjective(owner.node().slot_index());
                }
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
    /// The PTE must have been produced by [`Self::into_pte`], and `level` must
    /// be the level of the node that holds it.
    #[verus_spec(res =>
        with Tracked(entry_own): Tracked<&EntryOwner>,
        requires
            entry_own.pte_invariants(pte),
            level == entry_own.parent_level,
        ensures
            res.invariants(*entry_own),
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

                entry_own.node().lemma_identity();
                lemma_index_to_frame_biinjective(entry_own.node().slot_index());
                lemma_index_to_meta_biinjective(entry_own.node().slot_index());
            }
            // SAFETY: the entry's authority is the entitlement to name this
            // frame; the handle itself carries none.
            let node = unsafe { PageTableNode::from_raw(paddr) };
            return Child::PageTable(node);
        }
        Child::Frame(paddr, level, pte.prop())
    }
}

/// A *borrowed* reference to the child of a page table node.
///
/// A child node must be represented by a [`PageTableNodeRef`], which carries a
/// fraction of that node's ownership. A mapped frame can be described by
/// value, and an absent entry is just a tag.
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
                &&& node.wf()
                &&& node.id() == owner.node().id()
                &&& node@.slot_index == owner.node().slot_index()
                &&& node@.level == owner.node().level()
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
    pub open spec fn invariants(self, owner: EntryOwner) -> bool {
        &&& owner.inv()
        &&& self.wf(owner)
    }
}

#[verus_verify]
impl ChildRef<'_> {
    /// Converts a PTE to a *reference* to its child.
    ///
    /// Takes `&mut EntryOwner` because producing a reference means lending a
    /// fraction out of the child's authority — a mutation. Under the central
    /// region this was a shared read of a global map; making it a mutation is
    /// the honest accounting, and it is what stops an unbounded number of
    /// references appearing from nowhere.
    ///
    /// # Safety
    ///
    /// The PTE must outlive the reference, and `level` must match the
    /// containing node.
    #[verus_spec(res =>
        with Tracked(entry_owner): Tracked<&mut EntryOwner>,
        requires
            old(entry_owner).pte_invariants(*pte),
            old(entry_owner).is_node() ==> {
                &&& !old(entry_owner).node().is_lent_out()
                &&& old(entry_owner).node().frac() > 1
            },
            level == old(entry_owner).parent_level,
        ensures
            res.invariants(*final(entry_owner)),
            final(entry_owner).parent_level == old(entry_owner).parent_level,
            final(entry_owner).is_node() == old(entry_owner).is_node(),
            final(entry_owner).is_absent() == old(entry_owner).is_absent(),
            final(entry_owner).is_frame() == old(entry_owner).is_frame(),
            final(entry_owner).match_pte(*pte, final(entry_owner).parent_level),
            res is None <==> final(entry_owner).is_absent(),
            res is PageTable <==> final(entry_owner).is_node(),
    )]
    pub unsafe fn from_pte(pte: &Pte, level: PagingLevel) -> Self {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use group_page_meta;

                entry_owner.node().lemma_identity();
                lemma_index_to_frame_biinjective(entry_owner.node().slot_index());
                lemma_index_to_meta_biinjective(entry_owner.node().slot_index());
            }
            // Take the child's authority out, lend a fraction, put it back.
            // Going through `take`/`put` rather than a `&mut` borrow keeps the
            // effect on the `EntryOwner` fully specified.
            proof_decl! {
                let tracked frac: NodeFrac;
            }
            proof {
                let tracked mut auth = entry_owner.tracked_take_node();
                frac = auth.lend();
                entry_owner.tracked_put_node(auth);
                frac.validate();
            }
            let node = {
                #[verus_spec(with Tracked(frac))]
                PageTableNodeRef::from_frac(paddr)
            };
            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
