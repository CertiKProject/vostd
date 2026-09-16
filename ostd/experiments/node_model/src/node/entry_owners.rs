//! Ghost ownership of a page table *entry*.
//!
//! Model of `ostd::specs::mm::page_table::node::entry_owners`.
//!
//! An [`EntryOwner`] is the proof-side counterpart of one PTE: it says what
//! the entry *is* (a child node, a mapped frame, or nothing) and owns whatever
//! that thing owns. [`EntryOwner::match_pte`] is the relation tying it to the
//! concrete PTE value, and is the single place where the PTE encoding meets
//! the ownership story.
//!
//! # Where the decentralisation happens
//!
//! For a child node the entry owns a [`NodeAuth`] — the child's *authority*.
//! That is the structural change: a node's ownership lives in its parent's
//! entry, so the page table tree carries the ownership, instead of every node
//! being registered in one flat `MetaRegionOwners`. Handing out a
//! [`PageTableNodeRef`](crate::node::PageTableNodeRef) is then literally
//! lending a fraction out of that authority.
//!
//! Relative to the real type, the model drops the `path: TreePath<NR_ENTRIES>`
//! field (there is no ghost tree here) and the `Borrowed` variant (used for a
//! user page table's kernel-half slots, which point at a sub-tree owned by a
//! *different* page table configuration — and the model has only one).
use vstd::modes::tracked_swap;
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::node::frac::*;
use crate::page_prop::PageProperty;
use crate::pte::Pte;

verus! {

/// The proof-side snapshot of a page table leaf: a frame mapped in a node.
/// Huge pages are supported, so this is not necessarily at level 1.
pub ghost struct FrameEntryState {
    pub mapped_pa: Paddr,
    pub prop: PageProperty,
}

pub tracked enum EntryOwnerKind {
    /// The child node's authority. Lending from it produces the fractions that
    /// `PageTableNodeRef`s carry.
    Node(NodeAuth),
    Frame(ghost FrameEntryState),
    Absent,
}

pub tracked struct EntryOwner {
    pub kind: EntryOwnerKind,
    /// The level of the node *containing* this entry.
    pub ghost parent_level: PagingLevel,
}

impl EntryOwner {
    #[verifier::inline]
    pub open spec fn is_node(self) -> bool {
        self.kind is Node
    }

    #[verifier::inline]
    pub open spec fn is_frame(self) -> bool {
        self.kind is Frame
    }

    #[verifier::inline]
    pub open spec fn is_absent(self) -> bool {
        self.kind is Absent
    }

    /// The child node's authority.
    pub open spec fn node(self) -> NodeAuth {
        self.kind->Node_0
    }

    pub open spec fn frame(self) -> FrameEntryState {
        self.kind->Frame_0
    }

    // ─── Constructors ──────────────────────────────────────────────────────
    pub open spec fn new_absent(parent_level: PagingLevel) -> Self {
        EntryOwner { kind: EntryOwnerKind::Absent, parent_level }
    }

    pub open spec fn new_frame(
        paddr: Paddr,
        parent_level: PagingLevel,
        prop: PageProperty,
    ) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Frame(FrameEntryState { mapped_pa: paddr, prop }),
            parent_level,
        }
    }

    pub open spec fn new_node(auth: NodeAuth) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Node(auth),
            parent_level: (auth.level() + 1) as PagingLevel,
        }
    }

    pub proof fn tracked_new_absent(parent_level: PagingLevel) -> (tracked res: Self)
        returns
            Self::new_absent(parent_level),
    {
        Self { kind: EntryOwnerKind::Absent, parent_level }
    }

    pub proof fn tracked_new_node(tracked auth: NodeAuth) -> (tracked res: Self)
        returns
            Self::new_node(auth),
    {
        Self { kind: EntryOwnerKind::Node(auth), parent_level: (auth.level() + 1) as PagingLevel }
    }

    // ─── Moving the authority in and out ───────────────────────────────────
    //
    // A `NodeAuth` is tracked, so it cannot be copied: descending into a child
    // means *taking* the authority out of the entry, and coming back up means
    // putting it back.
    pub proof fn tracked_take_node(tracked &mut self) -> (tracked res: NodeAuth)
        requires
            old(self).kind is Node,
        ensures
            res == old(self).node(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Absent, ..*old(self) }),
    {
        let tracked mut tmp = EntryOwnerKind::Absent;
        tracked_swap(&mut self.kind, &mut tmp);
        match tmp {
            EntryOwnerKind::Node(auth) => auth,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_put_node(tracked &mut self, tracked auth: NodeAuth)
        ensures
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Node(auth), ..*old(self) }),
    {
        self.kind = EntryOwnerKind::Node(auth);
    }

    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeAuth)
        requires
            self.kind is Node,
        ensures
            *res == self.node(),
    {
        match self.kind {
            EntryOwnerKind::Node(ref auth) => auth,
            _ => { proof_from_false() },
        }
    }

    /// Mutable access to the child's authority, which is what lending a
    /// fraction requires. This is why `to_ref` and `ChildRef::from_pte` take
    /// `&mut EntryOwner` where they used to take `&EntryOwner`: handing out a
    /// reference is a mutation of the authority, not a read of a global map.
    pub proof fn tracked_borrow_mut_node(tracked &mut self) -> (tracked res: &mut NodeAuth)
        requires
            old(self).kind is Node,
        ensures
            *res == old(self).node(),
            final(self).parent_level == old(self).parent_level,
            final(self).kind is Node,
    {
        match self.kind {
            EntryOwnerKind::Node(ref mut auth) => auth,
            _ => { proof_from_false() },
        }
    }

    // ─── The PTE relation ──────────────────────────────────────────────────
    /// Ties the owner to the concrete PTE stored in the parent node.
    ///
    /// This is where the PTE encoding meets ownership. Read it as a case split
    /// on what the hardware would do at this entry:
    ///
    /// * absent PTE → the entry owns nothing;
    /// * present, walk continues → the entry owns a child node, and the PTE
    ///   points at that node's frame;
    /// * present, walk terminates → the entry owns a mapped frame, and the PTE
    ///   carries its address and properties.
    pub open spec fn match_pte(self, pte: Pte, parent_level: PagingLevel) -> bool {
        &&& valid_frame_paddr(pte.paddr())
        &&& !pte.is_present() ==> {
            &&& self.is_absent()
            &&& parent_level > 1 ==> !pte.is_last(parent_level)
        }
        &&& pte.is_present() && !pte.is_last(parent_level) ==> {
            &&& self.is_node()
            &&& self.node().paddr() == pte.paddr()
        }
        &&& pte.is_present() && pte.is_last(parent_level) ==> {
            &&& self.is_frame()
            &&& self.frame().mapped_pa == pte.paddr()
            &&& self.frame().prop == pte.prop()
        }
    }

    /// An absent owner matches the absent PTE.
    pub proof fn absent_match_pte(owner: Self, pte: Pte, parent_level: PagingLevel)
        requires
            owner.is_absent(),
            pte == Pte::new_absent_spec(),
        ensures
            owner.match_pte(pte, parent_level),
    {
        assert(valid_frame_paddr(0)) by (compute_only);
    }

    /// A terminating PTE above level 1 forces the owner to be a mapped frame.
    pub proof fn last_pte_implies_frame_match(self, pte: Pte, parent_level: PagingLevel)
        requires
            self.inv(),
            self.match_pte(pte, parent_level),
            1 < parent_level,
            pte.is_present(),
            pte.is_last(parent_level),
        ensures
            self.is_frame(),
            self.frame().mapped_pa == pte.paddr(),
            self.frame().prop == pte.prop(),
    {
    }

    // ─── Invariants ────────────────────────────────────────────────────────
    /// The structural invariant.
    ///
    /// Note what is *absent* compared with the central-region design: there is
    /// no `metaregion_sound` companion predicate threading a `Regions`
    /// argument. For a child node, `NodeAuth::wf()` is the whole story, and it
    /// is self-contained.
    pub open spec fn inv_base(self) -> bool {
        &&& self.is_node() ==> {
            &&& self.node().wf()
            // A child node is exactly one level below its parent. Stated
            // against `NodeAuth::level()`, which survives the node being lent
            // out to a guard.
            &&& self.parent_level == self.node().level() + 1
        }
        &&& self.is_frame() ==> {
            // Frames only exist at levels the ISA supports as leaves. A frame
            // at `parent_level == NR_LEVELS` would be a 512 GiB huge page,
            // which no current architecture permits.
            &&& 1 <= self.parent_level < NR_LEVELS
            &&& valid_frame_paddr(self.frame().mapped_pa)
        }
    }

    /// The physical address of whatever this entry owns, if anything.
    pub open spec fn meta_slot_paddr(self) -> Option<Paddr> {
        if self.is_node() {
            Some(self.node().paddr())
        } else if self.is_frame() {
            Some(self.frame().mapped_pa)
        } else {
            None
        }
    }

    /// Everything an owner and its PTE must jointly satisfy.
    ///
    /// Compare the old signature, `pte_invariants(self, pte, regions)`: the
    /// region argument is gone because nothing outside this entry is needed to
    /// know the entry is sound.
    pub open spec fn pte_invariants(self, pte: Pte) -> bool {
        &&& self.inv()
        &&& self.match_pte(pte, self.parent_level)
    }
}

impl Inv for EntryOwner {
    open spec fn inv(self) -> bool {
        self.inv_base()
    }
}

pub ghost struct EntryModel {
    pub parent_level: PagingLevel,
}

impl Inv for EntryModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for EntryOwner {
    type V = EntryModel;

    open spec fn view(&self) -> <Self as View>::V {
        EntryModel { parent_level: self.parent_level }
    }
}

impl InvView for EntryOwner {
    proof fn view_preserves_inv(self) {
    }
}

} // verus!
