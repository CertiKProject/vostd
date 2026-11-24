use vstd::{
    atomic::*,
    atomic_ghost::{AtomicInvariantPredicate, AtomicU8},
    cell::{CellId, pcell_maybe_uninit},
    prelude::*,
    resource::{Loc, ghost_var::GhostVarAuth},
};
use vstd_extra::{
    array_ptr,
    cast_ptr::{self, Repr},
    ghost_tree::TreePath,
    ownership::*,
    raw_ptr::{ExposedPointsTo, ptr_from_addr, ptr_ref},
    resource::flat_tree::{LockConst, LockedValue, NodeCell},
    resource::ghost_resource::count_auth::{Count, CountResource},
};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS},
    mm::{frame::linked_list::linked_list_owners::StoredLink, page_table::node::PageMetaOwner},
};

use super::*;
use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::meta::{
        AnyFrameMeta, META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
        mapping::meta_to_frame,
    },
    kspace::FRAME_METADATA_RANGE,
};

use crate::specs::mm::frame::frame_specs::FrameRawPerms;

verus! {

pub ghost enum PageUsage {
    /// Initial purpose before metadata is installed. Reuse is governed by refcount.
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
}

/// The raw representation of a node's PTEs, as recorded by the PTE-model
/// ghost variable: one raw `usize` per entry (`PageTableEntryTrait::as_usize`),
/// so that it does not depend on the `PageTableConfig`.
pub type PteRaws = Seq<usize>;

/// What one slot of a node owns, as a ghost snapshot: the counted metadata
/// token of the child node its PTE points to, or the permission of the frame
/// it maps (neither, for an absent or untracked entry). The node's lock cell
/// holds the authoritative half of a ghost variable recording one snapshot
/// per slot ([`PtLockPayload::slot_auth`]); the page table tree holds the
/// other half (`NodeOwner::slot_view`), so whoever holds the cell can prove
/// that the tree's view of the slots is current.
pub ghost struct SlotSnapshot {
    pub node: Option<FracMetadataPerm>,
    pub frame: Option<FrameRawPerms>,
}

/// One [`SlotSnapshot`] per entry of a node.
pub type SlotSnapshots = Seq<SlotSnapshot>;

/// `perms` holds exactly the frame item permissions that `snaps` records.
pub open spec fn frame_perms_match(snaps: SlotSnapshots, perms: Map<int, FrameRawPerms>) -> bool {
    &&& forall|i: int| #[trigger]
        perms.contains_key(i) ==> 0 <= i < snaps.len() && snaps[i].frame == Some(perms[i])
    &&& forall|i: int|
        0 <= i < snaps.len() && (#[trigger] snaps[i]).frame is Some ==> perms.contains_key(i)
}

/// `tokens` holds exactly the child-node tokens that `snaps` records: one per
/// slot whose snapshot has a `node`, and equal to it.
pub open spec fn node_tokens_match(
    snaps: SlotSnapshots,
    tokens: Map<int, FracMetadataPerm>,
) -> bool {
    &&& forall|i: int| #[trigger]
        tokens.contains_key(i) ==> 0 <= i < snaps.len() && snaps[i].node == Some(tokens[i])
    &&& forall|i: int|
        0 <= i < snaps.len() && (#[trigger] snaps[i]).node is Some ==> tokens.contains_key(i)
}

/// Number of entries among the first `n` of `s` that satisfy `f`.
pub open spec fn count_where_upto(f: spec_fn(usize) -> bool, s: PteRaws, n: int) -> int
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
pub open spec fn count_where(f: spec_fn(usize) -> bool, s: PteRaws) -> int {
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
    /// The id of the node's slot-snapshot ghost variable.
    pub slot_model_id: Loc,
    /// The paging level of the node.
    pub pt_level: PagingLevel,
    /// Whether a PTE, given by its bytes, is present.
    pub is_present: spec_fn(usize) -> bool,
    /// The child page table node a PTE at the given level points to, if any.
    pub child_of: spec_fn(usize, PagingLevel) -> Option<Paddr>,
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
    pub ghost is_present: spec_fn(usize) -> bool,
    /// See [`PtLockConsts::child_of`].
    pub ghost child_of: spec_fn(usize, PagingLevel) -> Option<Paddr>,
    /// The permissions for the `nr_children` and `stray` cells.
    pub meta: PageMetaOwner,
    /// The authoritative half of the PTE model. The other half
    /// (`NodeOwner::pte_view`) stays with the page table tree.
    pub pte_auth: GhostVarAuth<PteRaws>,
    /// The authoritative half of the slot snapshots. The other half
    /// (`NodeOwner::slot_view`) stays with the page table tree.
    pub slot_auth: GhostVarAuth<SlotSnapshots>,
    /// The counted metadata tokens of the child nodes this node's PTEs point
    /// to, by slot. Replacing a PTE moves its token, so only the lock holder
    /// can.
    pub node_tokens: Map<int, FracMetadataPerm>,
    /// The item permissions of the tracked frames this node's PTEs map, by
    /// slot. Mapping and unmapping move them, so only the lock holder can.
    pub frame_perms: Map<int, FrameRawPerms>,
    /// The permission for the node's PTE array, as raw values. Whoever holds
    /// the lock may read and write the PTEs.
    pub ptes: array_ptr::PointsTo<usize, NR_ENTRIES>,
}

impl LockedValue<Paddr, PtLockConsts> for PtLockPayload {
    open spec fn key(self) -> Paddr {
        self.paddr
    }

    open spec fn consts(self) -> PtLockConsts {
        PtLockConsts {
            nr_children_id: self.meta.nr_children.id(),
            stray_id: self.meta.stray.id(),
            pte_model_id: self.pte_auth.id(),
            slot_model_id: self.slot_auth.id(),
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
        &&& self.ptes.wf()
        &&& self.ptes.is_init_all()
        &&& self.ptes.value() == self.pte_auth@
        &&& self.slot_auth@.len() == NR_ENTRIES
        &&& node_tokens_match(self.slot_auth@, self.node_tokens)
        &&& frame_perms_match(self.slot_auth@, self.frame_perms)
        &&& self.ptes.addr() == crate::mm::paddr_to_vaddr(self.paddr)
    }
}

/// The cell a page table node lock holds while free. The root of a page table
/// is at flat-tree depth `0` and level-1 nodes at depth `NR_LEVELS - 1`.
pub type PtLockCell = NodeCell<PtLockPayload, Paddr, PtLockConsts, NR_ENTRIES, NR_LEVELS>;

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

impl MetaSlotStorage {
    /// The purpose established by the installed metadata representation.
    pub open spec fn usage(self) -> PageUsage {
        if self is PTNode {
            PageUsage::PageTable
        } else {
            PageUsage::Frame
        }
    }
}

/// `MetaSlotStorage` is an inductive tagged union of all of the frame meta types that
/// we work with in this development. So, it should itself implement `AnyFrameMeta`, and
/// it can then be used to stand in for `dyn AnyFrameMeta`.
unsafe impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlotStorage> for MetaSlotStorage {
    open spec fn wf(slot: MetaSlotStorage) -> bool {
        true
    }

    open spec fn from_repr_spec(slot: MetaSlotStorage) -> Self {
        slot
    }

    fn to_repr(self) -> MetaSlotStorage {
        self
    }

    fn from_borrowed<'a>(slot: &'a MetaSlotStorage) -> &'a Self {
        slot
    }

    fn from_borrowed_mut<'a>(slot: &'a mut MetaSlotStorage) -> &'a mut Self {
        slot
    }
}

/// Permissions to access metadata.
pub tracked struct MetadataPerm {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
}

impl MetadataPerm {
    /// The purpose of the metadata described by this permission.
    pub open spec fn usage(self) -> PageUsage {
        self.storage_perm.value().usage()
    }
}

pub const REF_COUNT_MAX_USIZE: usize = REF_COUNT_MAX as usize;

/// Fractional metadata permission.
pub type FracMetadataPerm = Count<MetadataPerm, REF_COUNT_MAX_USIZE>;

/// The undistributed part of a metadata permission.
pub type FracMetadataPermResource = CountResource<MetadataPerm, REF_COUNT_MAX_USIZE>;

/// Permissions that remain under the authority of `MetaRegionOwners`.
///
/// `ref_count_perm` and `in_list_perm` exist for the complete lifetime of the
/// corresponding `MetaSlot` (i.e., `'static`).
pub tracked struct MetaSlotOwner {
    pub metadata_perm: FracMetadataPermResource,
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

impl MetaSlotOwner {
    pub open spec fn same_permissions(self, other: Self) -> bool {
        &&& self.metadata_perm == other.metadata_perm
        &&& self.ref_count_perm == other.ref_count_perm
        &&& self.in_list_perm == other.in_list_perm
    }

    pub open spec fn ref_count(self) -> u64 {
        self.ref_count_perm.value()
    }

    pub open spec fn metadata_perm(self) -> MetadataPerm {
        self.metadata_perm.resource()
    }

    pub open spec fn storage_perm(self) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage> {
        self.metadata_perm().storage_perm
    }

    pub open spec fn vtable_ptr_perm(self) -> vstd::simple_pptr::PointsTo<usize> {
        self.metadata_perm().vtable_ptr_perm
    }
}

/// Well-formedness of a concrete metadata representation.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    slot_perm: ExposedPointsTo<MetaSlot>,
    metadata_perm: MetadataPerm,
) -> bool {
    &&& slot_perm.is_init()
    &&& MetaSlot::perms_related(slot_perm, metadata_perm)
    &&& M::wf(metadata_perm.storage_perm.value())
}

/// The value of a concrete metadata.
pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata_perm: MetadataPerm,
) -> M {
    M::from_repr_spec(metadata_perm.storage_perm.value())
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a ExposedPointsTo<MetaSlot>>,
    Tracked(metadata_perm): Tracked<&'a MetadataPerm>,
) -> &'a M
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *metadata_perm),
    returns
        typed_meta_value::<M>(*metadata_perm),
{
    let slot = ptr_ref(
        ptr_from_addr::<MetaSlot>(ptr.addr(), Tracked(slot_perm)),
        Tracked(slot_perm),
    );
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perm.storage_perm)))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a ExposedPointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a mut MetadataPerm>,
) -> (res: &'a mut M)
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *old(metadata_perms)),
    ensures
        *res == typed_meta_value::<M>(*old(metadata_perms)),
        *final(res) == typed_meta_value::<M>(*final(metadata_perms)),
        typed_meta_wf::<M>(*slot_perm, *final(metadata_perms)),
{
    let slot = ptr_ref(
        ptr_from_addr::<MetaSlot>(ptr.addr(), Tracked(slot_perm)),
        Tracked(slot_perm),
    );
    M::from_borrowed_mut(slot.storage.borrow_mut(Tracked(&mut metadata_perms.storage_perm)))
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.ref_count() == REF_COUNT_UNUSED ==> {
            &&& self.metadata_perm.is_full()
            &&& self.storage_perm().is_uninit()
            &&& self.vtable_ptr_perm().is_uninit()
            &&& self.in_list_perm.value() == 0
            &&& self.paths_in_pt.is_empty()
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.metadata_perm.is_resource_vacant()
            &&& self.paths_in_pt.is_empty()
        }
        &&& 0 < self.ref_count() <= REF_COUNT_MAX ==> {
            &&& !self.metadata_perm.is_resource_vacant()
            &&& self.metadata_perm.frac() + self.ref_count() == REF_COUNT_MAX
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
            &&& self.in_list_perm.value() == 0
        }
        &&& REF_COUNT_MAX < self.ref_count() < REF_COUNT_UNIQUE ==> { false }
        &&& self.ref_count() == 0 ==> {
            &&& self.metadata_perm.is_full()
            &&& self.in_list_perm.value() == 0
        }
        &&& FRAME_METADATA_RANGE.start <= self.slot_vaddr < FRAME_METADATA_RANGE.end
        &&& self.slot_vaddr % META_SLOT_SIZE == 0
    }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ref_count.id() == owner.ref_count_perm.id()
        &&& self.in_list.id() == owner.in_list_perm.id()
        &&& owner.metadata_perm.not_empty() ==> {
            &&& self.storage.id() == owner.storage_perm().id()
            &&& self.vtable_ptr == owner.vtable_ptr_perm().pptr()
        }
    }
}

/// Writes `metadata` into the byte storage and establishes its direct
/// `Repr<MetaSlotStorage>` interpretation.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(metadata_perms): Tracked<&mut MetadataPerm>,
    metadata: M,
)
    requires
        cell.id() == old(metadata_perms).storage_perm.id(),
    ensures
        final(metadata_perms).storage_perm.id() == old(metadata_perms).storage_perm.id(),
        final(metadata_perms).storage_perm.is_init(),
        final(metadata_perms).vtable_ptr_perm == old(metadata_perms).vtable_ptr_perm,
        M::wf(final(metadata_perms).storage_perm.value()),
        M::from_repr_spec(final(metadata_perms).storage_perm.value()) == metadata,
{
    let repr = metadata.to_repr();
    cell.write(Tracked(&mut metadata_perms.storage_perm), repr);
}

} // verus!
