use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, *};

use core::ops::Range;

use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use super::meta_owners::{Metadata, MetaPerm, MetaSlotModel, MetaSlotOwner, MetaSlotStorage};
use super::*;
use crate::mm::frame::meta::{
    mapping::{frame_to_index_spec, frame_to_meta, max_meta_slots, meta_addr, META_SLOT_SIZE},
    AnyFrameMeta, MetaSlot,
};
use crate::mm::Paddr;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_PADDR, NR_ENTRIES, PAGE_SIZE};

verus! {

/// Represents the meta-frame memory region. Can be viewed as a collection of
/// Cell<MetaSlot> at a fixed address range.
pub struct MetaRegion;

/// Represents the ownership of the meta-frame memory region.
/// # Verification Design
/// ## Slot owners
/// Every metadata slot has its owner ([`MetaSlotOwner`]) tracked by the `slot_owners` map at all times.
/// This makes the `MetaRegionOwners` the one place that tracks every frame, whether or not it is
/// in use.
/// ## Slot permissions
/// We treat the slot permissions differently depending on how they are used. The permissions of unused slots
/// are tracked in `slots`, as are those of frames that do not otherwise belong to any other data structure.
/// This is necessary because those frames can have a new reference taken at any time via `Frame::from_in_use`.
/// Unique frames and frames that are forgotten with `into_raw` have their permissions tracked by the owner of
/// whatever object they belong to. Their permissions will be returned to `slots` when the object is dropped.
/// Whether or not the frame has a permission in `slots`, it will always have an owner in `slot_owners`,
/// which tracks information that needs to be globally visible.
/// ## Safety
/// Forgetting a slot with `into_raw` or `ManuallyDrop::new` will leak the frame.
/// Forgetting it multiple times without restoring it will likely result in a memory leak, but not double-free.
/// Double-free happens when `from_raw` is called on a frame that is not forgotten, or that has been
/// dropped with `ManuallyDrop::drop` instead of `into_raw`. All functions in
/// the verified code that call `from_raw` have a precondition that the frame's index is not a key in `slots`.
pub tracked struct MetaRegionOwners {
    pub slots: Map<usize, simple_pptr::PointsTo<MetaSlot>>,
    pub slot_owners: Map<usize, MetaSlotOwner>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<usize, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(self) -> bool {
        &&& self.slots.dom().finite()
        &&& {
            // All accessible slots are within the valid address range.
            forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
        }
        &&& { forall|i: usize| #[trigger] self.slots.contains_key(i) ==> i < max_meta_slots() }
        &&& {
            forall|i: usize| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slot_owners.contains_key(i)
                    &&& self.slot_owners[i].inv()
                    &&& self.slots[i].is_init()
                    &&& self.slots[i].addr() == meta_addr(i)
                    &&& self.slots[i].value().wf(self.slot_owners[i])
                    &&& self.slot_owners.contains_key(i)
                    &&& self.slot_owners[i].self_addr == self.slots[i].addr()
                }
        }
        &&& {
            forall|i: usize| #[trigger]
                self.slot_owners.contains_key(i) ==> {
                    &&& self.slot_owners[i].inv()
                }
        }
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(self) -> bool {
        &&& self.slots.dom().finite()
        &&& forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: usize| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
    }
}

impl View for MetaRegionOwners {
    type V = MetaRegionModel;

    open spec fn view(&self) -> <Self as View>::V {
        let slots = self.slot_owners.map_values(|s: MetaSlotOwner| s@);
        MetaRegionModel { slots }
    }
}

impl InvView for MetaRegionOwners {
    // XXX: verus `map_values` does not preserves the `finite()` attribute.
    axiom fn view_preserves_inv(self);
}

impl OwnerOf for MetaRegion {
    type Owner = MetaRegionOwners;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        true
    }
}

impl ModelOf for MetaRegion {

}

impl MetaRegionOwners {
    pub open spec fn ref_count(self, i: usize) -> (res: u64)
        recommends
            self.inv(),
            i < max_meta_slots() as usize,
    {
        self.slot_owners[i].inner_perms.ref_count.value()
    }

    pub open spec fn paddr_range_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index_spec(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slots.contains_key(frame_to_index_spec(paddr))
    }

    pub open spec fn paddr_range_not_mapped(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index_spec(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slot_owners[frame_to_index_spec(paddr)].paths_in_pt.is_empty()
    }

    pub open spec fn paddr_range_not_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index_spec(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> !self.slots.contains_key(frame_to_index_spec(paddr))
    }

    /// Instantiates `paddr_range_not_mapped` at a specific paddr in the range.
    pub proof fn paddr_not_mapped_at(self, range: Range<Paddr>, paddr: Paddr)
        requires
            self.paddr_range_not_mapped(range),
            range.start <= paddr,
            paddr < range.end,
            paddr % PAGE_SIZE == 0,
        ensures
            self.slot_owners[frame_to_index_spec(paddr)].paths_in_pt.is_empty(),
    {
        // The trigger frame_to_index_spec(paddr) fires from the ensures clause,
        // instantiating the forall in paddr_range_not_mapped at this paddr.
    }

    pub proof fn inv_implies_correct_addr(self, paddr: usize)
        requires
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            self.inv(),
        ensures
            self.slot_owners.contains_key(frame_to_index_spec(paddr) as usize),
    {
        assert((frame_to_index_spec(paddr)) < max_meta_slots() as usize);
    }

    pub axiom fn copy_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        tracked &mut self,
        index: usize,
    ) -> (tracked perm: MetaPerm<M>)
        requires
            old(self).slots.contains_key(index),
        ensures
            perm.points_to == old(self).slots[index],
            final(self).slots == old(self).slots.remove(index),
            final(self).slot_owners == old(self).slot_owners;

    /// Park an externally-held slot pointer permission into `regions.slots`.
    /// Callers that hold the slot perm via an owner object (e.g. `NodeOwner.meta_perm`)
    /// invoke this immediately before `Frame::from_raw` so the perm is canonical in
    /// `regions.slots[index]` at the from_raw call.
    pub axiom fn sync_slot_perm(
        tracked &mut self,
        index: usize,
        perm: &simple_pptr::PointsTo<MetaSlot>,
    )
        ensures
            final(self).slots == old(self).slots.insert(index, *perm),
            final(self).slot_owners == old(self).slot_owners;

    /// Borrow the untyped slot perm canonically parked in `regions.slots[index]`.
    /// Pre-extracts the `inv()`-derived facts (`is_init`, `addr`, value-wf against
    /// the owner) so callers don't have to re-prove them at each borrow site.
    /// Zero new trust: thin wrapper over `slots.tracked_borrow`.
    pub proof fn borrow_slot_perm<'a>(tracked &'a self, index: usize)
        -> (tracked perm: &'a simple_pptr::PointsTo<MetaSlot>)
        requires
            self.inv(),
            self.slots.contains_key(index),
        ensures
            *perm == self.slots[index],
            perm.is_init(),
            perm.addr() == meta_addr(index),
            perm.value().wf(self.slot_owners[index]),
            self.slot_owners.contains_key(index),
            self.slot_owners[index].inv(),
            self.slot_owners[index].self_addr == meta_addr(index),
    {
        self.slots.tracked_borrow(index)
    }

    /// Borrow a typed `MetaPerm<M>` view synthesised from `(slots[index],
    /// slot_owners[index].inner_perms)`. The two pieces are the very fields of
    /// `cast_ptr::PointsTo<MetaSlot, Metadata<M>>`, so this is a structural
    /// re-bundling — but expressing it as an axiom is unavoidable because
    /// `PointsTo::new` consumes ownership while we only hold a shared borrow.
    ///
    /// Precondition is the typed-Repr witness `Metadata::<M>::wf(...)`, i.e.
    /// the ID-equality check that `MetaSlot::wf` already gives us under
    /// `regions.inv() + slots.contains_key(index)`. Callers establish it via
    /// `regions.inv()` and a `slot_owners[index].inner_perms` matching the
    /// canonical slot — exactly what `metaregion_sound`-style predicates carry.
    pub axiom fn borrow_meta_perm<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        tracked &'a self,
        index: usize,
    ) -> (tracked perm: &'a MetaPerm<M>)
        requires
            self.slots.contains_key(index),
            <Metadata<M> as Repr<MetaSlot>>::wf(
                self.slots[index].value(),
                self.slot_owners[index].inner_perms,
            ),
        ensures
            perm.points_to == self.slots[index],
            perm.inner_perms == self.slot_owners[index].inner_perms;
}

} // verus!
