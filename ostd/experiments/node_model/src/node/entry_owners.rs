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
//! Relative to the real type, the model drops the `path: TreePath<NR_ENTRIES>`
//! field (there is no ghost tree here, so there are no paths and no
//! `paths_in_pt` bookkeeping) and the `Borrowed` variant (used for a user page
//! table's kernel-half slots, which point at a sub-tree owned by a *different*
//! page table configuration — and the model has only one configuration).
use vstd::modes::tracked_swap;
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::frame::owners::*;
use crate::node::Regions;
use crate::node::owners::*;
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
    Node(NodeOwner),
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

    pub open spec fn node(self) -> NodeOwner {
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

    pub open spec fn new_node(node: NodeOwner) -> Self {
        EntryOwner {
            kind: EntryOwnerKind::Node(node),
            parent_level: (node.level + 1) as PagingLevel,
        }
    }

    pub proof fn tracked_new_absent(parent_level: PagingLevel) -> (tracked res: Self)
        returns
            Self::new_absent(parent_level),
    {
        Self { kind: EntryOwnerKind::Absent, parent_level }
    }

    pub proof fn tracked_new_node(tracked node: NodeOwner) -> (tracked res: Self)
        returns
            Self::new_node(node),
    {
        Self { kind: EntryOwnerKind::Node(node), parent_level: (node.level + 1) as PagingLevel }
    }

    // ─── Moving the node owner in and out ──────────────────────────────────
    //
    // A `NodeOwner` is tracked, so it cannot be copied: descending into a
    // child means *taking* the owner out of the entry, and coming back up
    // means putting it back.
    pub proof fn tracked_take_node(tracked &mut self) -> (tracked res: NodeOwner)
        requires
            old(self).kind is Node,
        ensures
            res == old(self).node(),
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Absent, ..*old(self) }),
    {
        let tracked mut tmp = EntryOwnerKind::Absent;
        tracked_swap(&mut self.kind, &mut tmp);
        match tmp {
            EntryOwnerKind::Node(node) => node,
            _ => { proof_from_false() },
        }
    }

    pub proof fn tracked_put_node(tracked &mut self, tracked node: NodeOwner)
        ensures
            *final(self) == (EntryOwner { kind: EntryOwnerKind::Node(node), ..*old(self) }),
    {
        self.kind = EntryOwnerKind::Node(node);
    }

    pub proof fn tracked_borrow_node(tracked &self) -> (tracked res: &NodeOwner)
        requires
            self.kind is Node,
        ensures
            *res == self.node(),
    {
        match self.kind {
            EntryOwnerKind::Node(ref node) => node,
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
    /// The structural invariant, independent of the region.
    pub open spec fn inv_base(self) -> bool {
        &&& self.is_node() ==> {
            &&& self.node().inv()
            // A child node is exactly one level below its parent.
            &&& self.parent_level == self.node().level + 1
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

    /// The region-dependent invariant: whatever this entry owns has a live
    /// metadata slot, tagged consistently with what the entry claims it is.
    pub open spec fn metaregion_sound(self, regions: Regions) -> bool {
        if self.is_node() {
            self.node().metaregion_sound_node(regions)
        } else if self.is_frame() {
            let idx = frame_to_index(self.frame().mapped_pa);
            &&& regions.contains(idx)
            &&& regions.slots[idx].inv()
            &&& regions.slots[idx].index == idx
            &&& regions.slots[idx].is_live()
            // A mapped data frame is *not* tagged `PageTable`. This is the
            // discriminator that keeps node slots and frame slots apart.
            &&& !(regions.slots[idx].usage is PageTable)
        } else {
            true
        }
    }

    /// Everything an owner and its PTE must jointly satisfy.
    pub open spec fn pte_invariants(self, pte: Pte, regions: Regions) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.match_pte(pte, self.parent_level)
        &&& self.metaregion_sound(regions)
    }

    /// An entry that owns a live node cannot sit in a slot that is still free.
    ///
    /// This is what rules out "the newly allocated node collides with an
    /// existing entry" in `alloc_if_none`.
    pub proof fn lemma_active_entry_not_in_free_pool(entry: Self, regions: Regions, free_idx: int)
        requires
            regions.inv(),
            entry.inv(),
            entry.is_node(),
            entry.metaregion_sound(regions),
            regions.contains(free_idx),
            !regions.slots[free_idx].is_live(),
        ensures
            entry.node().slot_index != free_idx,
    {
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
