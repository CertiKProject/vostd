//! The stubbed frame layer.
//!
//! This is the boundary of the model: everything above it (`crate::node`) is
//! modelled faithfully, everything here is the smallest thing the node layer
//! can be built on.
//!
//! Under fractional ownership this layer is *much* thinner than it used to be.
//! A `Frame<M>` is now nothing but a typed address: all of the ownership that
//! used to be parked in a central `MetaRegionOwners` has moved into the node's
//! own resources (`crate::node::NodeIdentity`, shared as
//! `crate::node::NodeFrac`, and `crate::node::NodeWriter`). Consequently:
//!
//! * `Frame::start_paddr` needs no permission at all, only a well-formed
//!   address;
//! * `Frame::from_raw` is no longer an axiom — reconstructing a *handle* from
//!   a physical address is pure arithmetic once the handle carries no
//!   authority of its own;
//! * `MetaSlotOwner` / `MetaRegionOwners` / `PageUsage` / `REF_COUNT_*` are
//!   gone entirely.
pub mod mapping;

use vstd::prelude::*;
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::arch::*;
use crate::frame::mapping::*;

verus! {

/// A handle to a frame, addressed by its metadata slot.
///
/// The real `Frame` is a reference-counted owning pointer whose `Drop`
/// decrements the count. Here it is a bare address; whether the holder may
/// *do* anything with the frame is decided by the resource they hold
/// alongside it, not by the handle.
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

    /// The physical address of the frame this handle names.
    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame_spec(self.ptr.addr())
    }
}

#[verus_verify]
impl<M> Frame<M> {
    /// Returns the physical address of the frame.
    ///
    /// Previously this took the slot's permission as a witness that the handle
    /// named a live slot. It no longer needs one: the address alone determines
    /// the answer, and liveness is the business of whoever holds the fraction.
    #[verus_spec(res =>
        requires
            self.wf_addr(),
        ensures
            res == self.start_paddr_spec(),
            valid_frame_paddr(res),
    )]
    pub fn start_paddr(&self) -> Paddr {
        proof {
            broadcast use group_page_meta;

        }
        meta_to_frame(self.ptr.addr())
    }

    /// Borrows the frame's metadata.
    ///
    /// The permission comes from the caller's `NodeFrac` (via its
    /// `NodeIdentity`), which is where the slot's `PointsTo` now lives.
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

    /// Reconstructs a handle from a raw physical address.
    ///
    /// # Safety
    ///
    /// The caller must ensure the address names a frame they are entitled to
    /// refer to. That entitlement is the fraction they hold, not this call.
    ///
    /// No longer axiomatised: with the authority moved out of the handle, this
    /// is just `frame_to_meta` plus a pointer construction.
    #[verus_spec(res =>
        requires
            valid_frame_paddr(paddr),
        ensures
            res.ptr.addr() == frame_to_meta_spec(paddr),
            res.wf_addr(),
            res.index() == frame_to_index(paddr),
            res.start_paddr_spec() == paddr,
    )]
    pub unsafe fn from_raw(paddr: Paddr) -> Self {
        proof {
            broadcast use group_page_meta;

        }
        Frame { ptr: PPtr::from_addr(frame_to_meta(paddr)) }
    }
}

} // verus!
