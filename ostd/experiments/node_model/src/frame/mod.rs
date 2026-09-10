//! The stubbed frame layer.
//!
//! This is the boundary of the model: everything above it (`crate::node`) is
//! modelled faithfully, everything here is the smallest thing the node layer
//! can be built on.
//!
//! What survives from the real `ostd::mm::frame`:
//!
//! * a `Frame<M>` is an owning handle that stores the **metadata slot
//!   address**, not the frame address (`Frame::start_paddr` converts);
//! * a `FrameRef<'a, M>` is a borrow of one, with a lifetime but no refcount
//!   change;
//! * the metadata for every frame lives in a global region, whose permissions
//!   are held in one tracked `MetaRegionOwners` that callers thread through;
//! * a slot has a reference count with the `UNUSED` sentinel, and a `usage`
//!   tag that discriminates page-table frames from data frames.
//!
//! What is dropped: `MetaSlot`'s type erasure (`MetaSlotStorage` + the `Repr`
//! cast, so `MetaRegionOwners` here is generic in `M` instead), the atomic
//! refcount and its `PermissionU64`, `UniqueFrame`, segments, linked lists, the
//! allocator, and all of `vstd_extra::drop_tracking` (`Frame` has no `Drop`
//! here, so there is no obligation ledger).
pub mod mapping;
pub mod owners;

use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::mapping::*;
use crate::frame::owners::*;

verus! {

/// An owning handle to a frame, addressed by its metadata slot.
///
/// Unlike the real `Frame`, this one does not implement `Drop`: modelling the
/// recursive teardown of a page table is out of scope, so nothing in the model
/// ever decrements a reference count.
pub struct Frame<M> {
    /// Points at the frame's metadata slot, i.e. `frame_to_meta(paddr)`.
    pub ptr: PPtr<M>,
}

impl<M> Frame<M> {
    /// The metadata-slot index of this frame.
    pub open spec fn index(self) -> int {
        meta_to_index(self.ptr.addr())
    }

    /// The handle is addressed by a well-formed metadata slot.
    pub open spec fn wf_addr(self) -> bool {
        valid_meta_vaddr(self.ptr.addr())
    }

    /// The physical address of the frame this handle owns.
    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame_spec(self.ptr.addr())
    }
}

#[verus_verify]
impl<M> Frame<M> {
    /// Returns the physical address of the frame.
    ///
    /// The real signature takes the slot permission to witness that the handle
    /// addresses a live slot; the model takes the slot owner for the same
    /// reason.
    #[verus_spec(res =>
        with Tracked(slot): Tracked<&MetaSlotOwner<M>>,
        requires
            slot.inv(),
            slot.meta_perm.addr() == self.ptr.addr(),
        ensures
            res == self.start_paddr_spec(),
            valid_frame_paddr(res),
    )]
    pub fn start_paddr(&self) -> Paddr {
        proof {
            broadcast use group_page_meta;

            lemma_index_to_meta_biinjective(slot.index);
        }
        meta_to_frame(self.ptr.addr())
    }

    /// Borrows the frame's metadata.
    #[verus_spec(res =>
        with Tracked(perm): Tracked<&'a PointsTo<M>>,
        requires
            perm.addr() == self.ptr.addr(),
            perm.is_init(),
        ensures
            *res == perm.value(),
    )]
    pub fn meta<'a>(&'a self) -> &'a M {
        self.ptr.borrow(Tracked(perm))
    }

    /// Restores an owning handle from a raw physical address.
    ///
    /// # Safety
    ///
    /// The caller must ensure the address names a live frame whose ownership
    /// is being transferred into the returned handle.
    ///
    /// Axiomatised: the real body manipulates the atomic reference count. The
    /// model has no `Drop`, so the handle is pure address arithmetic and the
    /// region is untouched.
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&MetaRegionOwners<M>>,
        requires
            regions.inv(),
            valid_frame_paddr(paddr),
            regions.slot_of(paddr).ref_count != REF_COUNT_UNUSED,
        ensures
            res.ptr.addr() == frame_to_meta_spec(paddr),
            res.wf_addr(),
            res.index() == frame_to_index(paddr),
    )]
    pub unsafe fn from_raw(paddr: Paddr) -> Self {
        unimplemented!()
    }
}

/// A struct that can work as `&'a Frame<M>`.
///
/// The real type wraps `ManuallyDrop<Frame<M>>` to suppress the owning
/// handle's `Drop`; the model's `Frame` has no `Drop`, so it holds the handle
/// directly.
pub struct FrameRef<'a, M> {
    pub inner: Frame<M>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

#[verus_verify]
impl<'a, M> FrameRef<'a, M> {
    /// Borrows the frame at the physical address.
    ///
    /// # Safety
    ///
    /// The caller must ensure the borrow does not outlive an owning handle to
    /// the same frame.
    ///
    /// Axiomatised for the same reason as [`Frame::from_raw`]; note the region
    /// is provably unchanged, which is what lets `ChildRef::from_pte` promise
    /// its caller that no other entry was disturbed.
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&MetaRegionOwners<M>>,
        requires
            regions.inv(),
            valid_frame_paddr(paddr),
            regions.slot_of(paddr).ref_count != REF_COUNT_UNUSED,
        ensures
            res.inner.ptr.addr() == frame_to_meta_spec(paddr),
            res.inner.wf_addr(),
            res.inner.index() == frame_to_index(paddr),
    )]
    pub unsafe fn borrow_paddr(paddr: Paddr) -> Self {
        unimplemented!()
    }
}

impl<M> core::ops::Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

} // verus!
