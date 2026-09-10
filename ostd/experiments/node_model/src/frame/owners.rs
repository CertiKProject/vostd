//! Ghost ownership of the frame metadata region.
//!
//! Model of `ostd::specs::mm::frame::{meta_owners, meta_region_owners}`.
//!
//! The real `MetaRegionOwners` carries two parallel maps — `slots:
//! Map<int, PointsTo<MetaSlot>>` and `slot_owners: Map<int, MetaSlotOwner>` —
//! plus a `Multiset<int>` ledger of pending drop obligations. The model merges
//! the two maps into one and drops the ledger, keeping the part the node layer
//! actually reads: *for each frame index, a permission for its metadata and a
//! reference count*.
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;

verus! {

/// Reference count sentinel: the slot is free.
pub const REF_COUNT_UNUSED: u64 = u64::MAX;

/// The largest legal live reference count.
pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

/// What a frame is being used for.
///
/// The discriminator matters to the node layer: `metaregion_sound` uses it to
/// tell a slot holding a page table node apart from one holding a mapped data
/// frame, which is how a freshly allocated node is known not to collide with a
/// live one.
#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub enum PageUsage {
    /// Not allocated.
    Unused,
    /// A page table node.
    PageTable,
    /// A data frame mapped by some leaf PTE.
    Frame,
}

/// Ghost ownership of one metadata slot.
pub tracked struct MetaSlotOwner<M> {
    /// Permission for the slot's contents, i.e. the frame's metadata.
    pub meta_perm: PointsTo<M>,
    /// This slot's index in the metadata region.
    pub ghost index: int,
    /// The frame's reference count. `REF_COUNT_UNUSED` means free.
    pub ghost ref_count: u64,
    /// What the frame is used for.
    pub ghost usage: PageUsage,
}

impl<M> Inv for MetaSlotOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.index < max_meta_slots()
        &&& self.meta_perm.addr() == index_to_meta(self.index)
        &&& self.meta_perm.is_init()
        &&& self.ref_count == REF_COUNT_UNUSED <==> self.usage is Unused
        &&& self.ref_count != REF_COUNT_UNUSED ==> 0 < self.ref_count <= REF_COUNT_MAX
    }
}

impl<M> MetaSlotOwner<M> {
    /// The metadata slot address this owner covers.
    pub open spec fn slot_vaddr(self) -> Vaddr {
        index_to_meta(self.index)
    }

    /// The physical address of the frame this owner covers.
    pub open spec fn paddr(self) -> Paddr {
        index_to_frame(self.index)
    }

    /// The frame is live (allocated).
    pub open spec fn is_live(self) -> bool {
        self.ref_count != REF_COUNT_UNUSED
    }
}

/// Ghost ownership of the whole metadata region: one owner per frame.
pub tracked struct MetaRegionOwners<M> {
    /// Keyed by metadata-slot index.
    pub tracked slots: Map<int, MetaSlotOwner<M>>,
}

impl<M> Inv for MetaRegionOwners<M> {
    open spec fn inv(self) -> bool {
        // The metadata region describes *every* frame, which is what makes
        // `lemma_contains_valid_frame_paddr` true: from a valid physical
        // address alone the node layer can conclude a slot exists.
        &&& forall|i: int| 0 <= i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: int| #[trigger]
            self.slots.contains_key(i) ==> self.slots[i].inv() && self.slots[i].index == i
    }
}

impl<M> MetaRegionOwners<M> {
    pub open spec fn contains(self, index: int) -> bool {
        self.slots.contains_key(index)
    }

    /// The owner of the slot describing the frame at `paddr`.
    pub open spec fn slot_of(self, paddr: Paddr) -> MetaSlotOwner<M> {
        self.slots[frame_to_index(paddr)]
    }

    /// A valid physical address always has a metadata slot.
    pub proof fn lemma_contains_valid_frame_paddr(self, paddr: Paddr)
        requires
            self.inv(),
            valid_frame_paddr(paddr),
        ensures
            self.contains(frame_to_index(paddr)),
            self.slot_of(paddr).inv(),
            self.slot_of(paddr).index == frame_to_index(paddr),
            self.slot_of(paddr).paddr() == paddr,
            self.slot_of(paddr).slot_vaddr() == frame_to_meta_spec(paddr),
    {
        broadcast use group_page_meta;

        lemma_frame_index_in_range(paddr);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(paddr as int, PAGE_SIZE as int);
    }

    /// Borrows one slot owner out of the region.
    pub proof fn tracked_borrow_slot(tracked &self, index: int) -> (tracked res: &MetaSlotOwner<M>)
        requires
            self.contains(index),
        ensures
            *res == self.slots[index],
    {
        self.slots.tracked_borrow(index)
    }
}

} // verus!
