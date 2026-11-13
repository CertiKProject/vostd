//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::prelude::*;

use vstd::{
    atomic::*,
    atomic_ghost::{AtomicInvariantPredicate, AtomicU8},
    cell::{CellId, pcell_maybe_uninit},
    resource::{Loc, ghost_var::GhostVarAuth},
    simple_pptr::*,
};
use vstd_extra::{
    cast_ptr::{self, Repr},
    ghost_tree::TreePath,
    ownership::*,
    resource::flat_tree::{LockConst, LockedValue, NodeCell},
};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS},
    mm::{frame::linked_list::linked_list_owners::StoredLink, page_table::node::PageMetaOwner},
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        AnyFrameMeta,
        meta::{
            META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::meta_to_frame,
        },
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::*;

verus! {

#[allow(non_camel_case_types)]
pub ghost enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}

pub ghost enum PageUsage {
    // The zero variant is reserved for the unused type. Only an unused page
    // can be designated for one of the other purposes.
    Unused,
    /// The page is reserved or unusable. The kernel should not touch it.
    Reserved,
    /// The page is used as a frame, i.e., a page of untyped memory.
    Frame,
    /// The page is used by a page table.
    PageTable,
    /// The page stores metadata of other pages.
    Meta,
    /// The page stores the kernel such as kernel code, data, etc.
    Kernel,
    /// The page maps memory-mapped I/O (MMIO). Untracked: no refcount, slot
    /// stays in the free pool, but distinguishable from `Unused` so the
    /// kernel allocator never collides with an MMIO mapping.
    MMIO,
}

/// Whether `pa` falls in an MMIO physical-address range. Uninterpreted at the
/// spec level — concrete arch- and machine-specific MMIO range layouts are
/// outside the verification surface, but the kernel allocator (which picks
/// slots with `PageUsage::Unused`) is guaranteed disjoint from MMIO mappings.
pub uninterp spec fn is_mmio_paddr(pa: Paddr) -> bool;

/// Connects a slot's `PageUsage::MMIO` discriminant to its paddr's range
/// membership. Used to derive disjointness between MMIO mappings and the
/// regular allocator pool: a slot can be `MMIO` iff its paddr is in MMIO
/// range, so a slot with `usage != MMIO` (e.g. `Unused`) cannot share an idx
/// with any MMIO mapping.
pub broadcast axiom fn axiom_mmio_usage_iff_mmio_paddr(slot: MetaSlotOwner)
    ensures
        (#[trigger] slot.usage == PageUsage::MMIO) <==> is_mmio_paddr(
            meta_to_frame(slot.slot_vaddr),
        ),
;

/// MMIO ranges are aligned to (and closed under) huge-page granularities:
/// every sub-paddr within a huge frame inherits the huge frame's MMIO-ness.
/// This is a hardware-layout convention — MMIO BARs are mapped at huge-page
/// boundaries, and the verified `split_if_mapped_huge` relies on it to
/// transfer MMIO-ness from a huge frame to its 4KB sub-pages. Non-broadcast:
/// callers invoke this explicitly with the relevant `page_size`.
pub axiom fn axiom_mmio_paddr_huge_page_closed(pa: Paddr, page_size: usize, offset: usize)
    requires
        pa % page_size == 0,
        offset < page_size,
    ensures
        is_mmio_paddr((pa + offset) as Paddr) == is_mmio_paddr(pa),
;

/// The raw byte representation of a node's PTEs, as recorded by the PTE-model
/// ghost variable. One `Seq<u8>` per entry, so that it does not depend on the
/// `PageTableConfig`.
pub type PteBytes = Seq<Seq<u8>>;

/// Number of entries among the first `n` of `s` that satisfy `f`.
pub open spec fn count_where_upto(f: spec_fn(Seq<u8>) -> bool, s: PteBytes, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_where_upto(f, s, n - 1) + if f(s[n - 1]) {
            1int
        } else {
            0int
        }
    }
}

/// Number of entries of `s` that satisfy `f`.
pub open spec fn count_where(f: spec_fn(Seq<u8>) -> bool, s: PteBytes) -> int {
    count_where_upto(f, s, s.len() as int)
}

/// The part of a page table node lock's constant that the node's parent does
/// not see. Fixed when the node is created.
///
/// The predicate cannot mention the `PageTableConfig` (the stored metadata is
/// not generic), so the config-specific interpretation of PTEs is carried here
/// as ghost functions. [`PageTablePageMeta::lock_wf`] pins them down.
///
/// [`PageTablePageMeta::lock_wf`]: crate::mm::page_table::PageTablePageMeta::lock_wf
pub ghost struct PtLockConsts {
    /// The id of the node's `nr_children` cell.
    pub nr_children_id: CellId,
    /// The id of the node's `stray` cell.
    pub stray_id: CellId,
    /// The id of the node's PTE-model ghost variable.
    pub pte_model_id: Loc,
    /// The paging level of the node.
    pub pt_level: PagingLevel,
    /// Whether a PTE, given by its bytes, is present.
    pub is_present: spec_fn(Seq<u8>) -> bool,
    /// The child page table node a PTE at the given level points to, if any.
    pub child_of: spec_fn(Seq<u8>, PagingLevel) -> Option<Paddr>,
}

/// The constant of a page table node lock: a [`flat_tree`] lock constant, keyed
/// by the node's physical address.
///
/// The notion of a Constant comes from the ghost Atomics,  AtomicU8<K, G, Pred>,  the K is the part 
/// that does not change. Here, it refers to the identities of everything inside the cell, as opposed to the contents. 
/// The identities are fixed for the node's whole lifetime. The contents change whenever the lock holder writes.
/// 
/// [`flat_tree`]: vstd_extra::resource::flat_tree
pub type PtLockConst = LockConst<Paddr, PtLockConsts>;

/// What a page table node lock holds while it is free, inside a
/// [`PtLockCell`]. It is handed to whoever acquires the lock.
pub tracked struct PtLockPayload {
    /// The physical address of the node.
    pub ghost paddr: Paddr,
    /// See [`PtLockConsts::pt_level`].
    pub ghost pt_level: PagingLevel,
    /// See [`PtLockConsts::is_present`].
    pub ghost is_present: spec_fn(Seq<u8>) -> bool,
    /// See [`PtLockConsts::child_of`].
    pub ghost child_of: spec_fn(Seq<u8>, PagingLevel) -> Option<Paddr>,
    /// The permissions for the `nr_children` and `stray` cells.
    pub meta: PageMetaOwner,
    /// The authoritative half of the PTE model. The other half
    /// (`NodeOwner::pte_view`) stays with the page table tree.
    pub pte_auth: GhostVarAuth<PteBytes>,
}

impl LockedValue for PtLockPayload {
    type Key = Paddr;

    type Consts = PtLockConsts;

    open spec fn key(self) -> Paddr {
        self.paddr
    }

    open spec fn consts(self) -> PtLockConsts {
        PtLockConsts {
            nr_children_id: self.meta.nr_children.id(),
            stray_id: self.meta.stray.id(),
            pte_model_id: self.pte_auth.id(),
            pt_level: self.pt_level,
            is_present: self.is_present,
            child_of: self.child_of,
        }
    }

    /// The child page table node that PTE `i` points to, according to the PTE
    /// model. Level-1 nodes have none.
    open spec fn child_key(self, i: int) -> Option<Paddr> {
        if self.pt_level <= 1 || !(0 <= i < self.pte_auth@.len()) {
            None
        } else {
            (self.child_of)(self.pte_auth@[i], self.pt_level)
        }
    }

    /// The flat-tree depth `level` is `NR_LEVELS - pt_level`, and
    /// `nr_children` counts the present PTEs in the PTE model.
    open spec fn inv(self, level: nat) -> bool {
        &&& self.meta.inv()
        &&& self.pt_level + level == NR_LEVELS
        &&& self.meta.nr_children.value() == count_where(self.is_present, self.pte_auth@)
    }
}

/// The cell a page table node lock holds while free. The root of a page table
/// is at flat-tree depth `0` and level-1 nodes at depth `NR_LEVELS - 1`.
pub type PtLockCell = NodeCell<PtLockPayload, NR_ENTRIES, NR_LEVELS>;

/// The invariant of the page table node lock (see [`PageTableLock`]).
pub struct PtLockPred;

impl AtomicInvariantPredicate<PtLockConst, u8, Option<PtLockCell>> for PtLockPred {
    /// When the lock is free (`0`), it stores the [`PtLockCell`] whose identity
    /// is the constant, and which can be unlocked. When it is held (`1`), the
    /// cell is with the lock holder. This is [`flat_tree::CellPred`] on a `u8`.
    ///
    /// [`flat_tree::CellPred`]: vstd_extra::resource::flat_tree::CellPred
    open spec fn atomic_inv(k: PtLockConst, v: u8, g: Option<PtLockCell>) -> bool {
        match g {
            None => v == 1,
            Some(c) => {
                &&& v == 0
                &&& c.lock_const() == k
                &&& c.inv_cell()
            },
        }
    }
}

/// The lock of a page table node. It carries the [`PtLockCell`] of the node
/// while unlocked.
pub type PageTableLock = AtomicU8<PtLockConst, Option<PtLockCell>, PtLockPred>;

pub struct StoredPageTablePageMeta {
    pub nr_children: pcell_maybe_uninit::PCell<u16>,
    pub stray: pcell_maybe_uninit::PCell<bool>,
    pub level: PagingLevel,
    pub lock: PageTableLock,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    Untyped,
    FrameLink(StoredLink),
    PTNode(StoredPageTablePageMeta),
}

/// `MetaSlotStorage` is an inductive tagged union of all of the frame meta types that
/// we work with in this development. So, it should itself implement `AnyFrameMeta`, and
/// it can then be used to stand in for `dyn AnyFrameMeta`.
unsafe impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlotStorage> for MetaSlotStorage {
    type ReprPerm = ();

    open spec fn wf(slot: MetaSlotStorage, perm: ()) -> bool {
        true
    }

    open spec fn to_repr_spec(self, perm: ()) -> (MetaSlotStorage, ()) {
        (self, ())
    }

    fn to_repr(self, Tracked(perm): Tracked<&mut ()>) -> MetaSlotStorage {
        self
    }

    open spec fn from_repr_spec(slot: MetaSlotStorage, perm: ()) -> Self {
        slot
    }

    fn from_repr(slot: MetaSlotStorage, Tracked(perm): Tracked<&()>) -> Self {
        slot
    }

    fn from_borrowed<'a>(slot: &'a MetaSlotStorage, Tracked(perm): Tracked<&'a ()>) -> &'a Self {
        slot
    }

    fn from_borrowed_mut<'a>(
        slot: &'a mut MetaSlotStorage,
        Tracked(perm): Tracked<&'a mut ()>,
    ) -> &'a mut Self {
        slot
    }

    proof fn from_to_repr(self, perm: ()) {
    }

    proof fn to_from_repr(slot: MetaSlotStorage, perm: ()) {
    }

    proof fn to_repr_wf(self, perm: ()) {
    }
}

impl MetaSlotStorage {
    pub open spec fn get_link_spec(self) -> Option<StoredLink> {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_link_spec)]
    pub fn get_link(self) -> (res: Option<StoredLink>)
        ensures
            res == self.get_link_spec(),
    {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None,
        }
    }

    pub open spec fn get_node_spec(self) -> Option<StoredPageTablePageMeta> {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_node_spec)]
    pub fn get_node(self) -> (res: Option<StoredPageTablePageMeta>)
        ensures
            res == self.get_node_spec(),
    {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
        }
    }
}

/// Permissions whose initialized contents belong to one installed metadata
/// value.
pub tracked struct MetadataPerms {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
}

/// Well-formedness of a concrete metadata representation. The outer slot
/// permission remains permanently in `MetaRegionOwners`; the metadata bundle
/// describes the permissions tied to the currently installed metadata.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
    metadata_perms: MetadataPerms,
    repr_perm: M::ReprPerm,
) -> bool {
    &&& points_to.is_init()
    &&& metadata_perms.storage_perm.is_init()
    &&& metadata_perms.storage_perm.id() == points_to.value().storage.id()
    &&& M::wf(metadata_perms.storage_perm.value(), repr_perm)
}

pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata_perms: MetadataPerms,
    repr_perm: M::ReprPerm,
) -> M {
    M::from_repr_spec(metadata_perms.storage_perm.value(), repr_perm)
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a MetadataPerms>,
    Tracked(repr_perm): Tracked<&'a M::ReprPerm>,
) -> (res: &'a M)
    requires
        typed_meta_wf::<M>(*points_to, *metadata_perms, *repr_perm),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(*metadata_perms, *repr_perm),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perms.storage_perm)), Tracked(repr_perm))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(slot_owner): Tracked<&'a mut MetaSlotOwner>,
    Tracked(repr_perm): Tracked<&'a mut M::ReprPerm>,
) -> (res: &'a mut M)
    requires
        old(slot_owner).inv(),
        points_to.value().wf(*old(slot_owner)),
        typed_meta_wf::<M>(*points_to, old(slot_owner).metadata_perm, *old(repr_perm)),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(old(slot_owner).metadata_perm, *old(repr_perm)),
        final(slot_owner).inv(),
        points_to.value().wf(*final(slot_owner)),
        final(slot_owner).slot_vaddr == old(slot_owner).slot_vaddr,
        final(slot_owner).usage == old(slot_owner).usage,
        final(slot_owner).paths_in_pt == old(slot_owner).paths_in_pt,
        final(slot_owner).ref_count_perm == old(slot_owner).ref_count_perm,
        final(slot_owner).vtable_ptr_perm() == old(slot_owner).vtable_ptr_perm(),
        final(slot_owner).in_list_perm == old(slot_owner).in_list_perm,
        typed_meta_wf::<M>(*points_to, final(slot_owner).metadata_perm, *final(repr_perm)),
        *final(res) == typed_meta_value::<M>(final(slot_owner).metadata_perm, *final(repr_perm)),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    let tracked metadata_perms = slot_owner.tracked_borrow_mut_metadata_perms();
    M::from_borrowed_mut(
        slot.storage.borrow_mut(Tracked(&mut metadata_perms.storage_perm)),
        Tracked(repr_perm),
    )
}

/// Permissions that remain under the authority of `MetaRegionOwners`.
///
/// `ref_count` and `in_list` exist for the complete lifetime of the
/// corresponding `MetaSlot` (i.e., `'static`).
pub tracked struct MetaSlotOwner {
    pub metadata_perm: MetadataPerms,
    pub ref_count_perm: PermissionU64,
    pub in_list_perm: PermissionU64,
    pub ghost slot_vaddr: Vaddr,
    pub ghost usage: PageUsage,
    /// The set of tree paths at which this slot is referenced. For PT-node
    /// slots this is a singleton. For data-frame slots this tracks every
    /// location the frame is currently mapped — allowing a single frame to be
    /// mapped at multiple addresses.
    pub ghost paths_in_pt: Set<TreePath<NR_ENTRIES>>,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        // A managed slot at `REF_COUNT_UNUSED` is free — it has no live
        // PTE mapping, since a mapping is itself a reference that would
        // keep the count above the unused sentinel. Hence `paths_in_pt`
        // is empty. Maintained by the teardown path: the sole transition
        // *into* `UNUSED` is `drop_last_in_place`, whose
        // `drop_last_in_place_safety_cond` requires an empty
        // `paths_in_pt`. MMIO slots are excluded — they are not
        // ref-counted as ordinary frames (an MMIO region may sit at the
        // `UNUSED` sentinel while still mapped), exactly as the embedding
        // accounting and the huge-page split loop invariant scope out
        // `usage == MMIO`.
        &&& self.ref_count() == REF_COUNT_UNUSED ==> {
            &&& self.storage_perm().is_uninit()
            &&& self.vtable_ptr_perm().is_uninit()
            &&& self.in_list_perm.value() == 0
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
            // A UNIQUE non-MMIO slot has no live PTE mapping (same rationale as
            // the UNUSED branch): a mapping would be a reference keeping the
            // count above the unique sentinel. Lets the list-store embedding
            // discharge `paths_in_pt.is_empty()` for linked-list frames.
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        // A SHARED slot (`0 < rc <= REF_COUNT_MAX`) is genuinely in use:
        // metadata storage is written, `vtable_ptr` resolves the
        // dynamic type, and the slot is *not* on the allocator's free
        // list. `storage.is_init()` and `in_list.value() == 0` were
        // previously asserted only in the `UNIQUE` branch and via the
        // `rc == 1 ⟹ ...` guard on `Frame::drop_requires`; they are
        // universally true of any in-use slot, so they live here. Once
        // these are invariants, the embedding's `op_pre[FrameDrop]` can
        // drop its `rc == 1 ⟹ storage.is_init ∧ in_list == 0` residual
        // (it follows from `regions.inv() ⟹ slot_owners[idx].inv()`).
        &&& 0 < self.ref_count() <= REF_COUNT_MAX ==> {
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
            &&& self.in_list_perm.value() == 0
        }
        &&& REF_COUNT_MAX < self.ref_count() < REF_COUNT_UNIQUE ==> { false }
        &&& self.ref_count() == 0 ==> {
            &&& self.in_list_perm.value() == 0
        }
        &&& FRAME_METADATA_RANGE.start <= self.slot_vaddr < FRAME_METADATA_RANGE.end
        &&& self.slot_vaddr % META_SLOT_SIZE == 0
    }
}

pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
    pub slot_vaddr: Vaddr,
    pub usage: PageUsage,
}

impl Inv for MetaSlotModel {
    open spec fn inv(self) -> bool {
        match self.ref_count {
            REF_COUNT_UNUSED => {
                &&& self.vtable_ptr.is_uninit()
                &&& self.in_list == 0
            },
            REF_COUNT_UNIQUE => { &&& self.vtable_ptr.is_init() },
            0 => { &&& self.in_list == 0 },
            _ if self.ref_count <= REF_COUNT_MAX => { &&& self.vtable_ptr.is_init() },
            _ => { false },
        }
    }
}

impl View for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(&self) -> Self::V {
        let storage = self.storage_perm().mem_contents();
        let ref_count = self.ref_count();
        let vtable_ptr = self.vtable_ptr_perm().mem_contents();
        let in_list = self.in_list_perm.value();
        let slot_vaddr = self.slot_vaddr;
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count <= REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel { status, storage, ref_count, vtable_ptr, in_list, slot_vaddr, usage }
    }
}

impl InvView for MetaSlotOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.storage.id() == owner.storage_perm().id()
        &&& self.ref_count.id() == owner.ref_count_perm.id()
        &&& self.vtable_ptr == owner.vtable_ptr_perm().pptr()
        &&& self.in_list.id() == owner.in_list_perm.id()
    }
}

impl MetaSlotOwner {
    pub open spec fn same_permissions(self, other: Self) -> bool {
        &&& self.metadata_perm == other.metadata_perm
        &&& self.ref_count_perm == other.ref_count_perm
        &&& self.in_list_perm == other.in_list_perm
    }

    pub open spec fn ref_count(self) -> u64 {
        self.ref_count_perm.value()
    }

    pub open spec fn storage_perm(self) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage> {
        self.metadata_perm.storage_perm
    }

    pub open spec fn vtable_ptr_perm(self) -> vstd::simple_pptr::PointsTo<usize> {
        self.metadata_perm.vtable_ptr_perm
    }

    pub proof fn tracked_borrow_mut_metadata_perms(tracked &mut self) -> (tracked res:
        &mut MetadataPerms)
        ensures
            *res == old(self).metadata_perm,
            *final(self) == (Self { metadata_perm: *final(res), ..*old(self) }),
    {
        &mut self.metadata_perm
    }
}

/// Writes `metadata` into the byte storage and establishes its direct
/// `Repr<MetaSlotStorage>` interpretation.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(storage): Tracked<&mut pcell_maybe_uninit::PointsTo<MetaSlotStorage>>,
    Tracked(repr_perm): Tracked<&mut M::ReprPerm>,
    metadata: M,
)
    requires
        cell.id() == old(storage).id(),
    ensures
        final(storage).id() == old(storage).id(),
        final(storage).is_init(),
        M::wf(final(storage).value(), *final(repr_perm)),
        M::from_repr_spec(final(storage).value(), *final(repr_perm)) == metadata,
{
    proof {
        M::from_to_repr(metadata, *repr_perm);
        M::to_repr_wf(metadata, *repr_perm);
    }
    let repr = metadata.to_repr(Tracked(repr_perm));
    cell.write(Tracked(storage), repr);
}

} // verus!
