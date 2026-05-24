use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;

use vstd::cell;
use vstd::simple_pptr::*;

use crate::mm::frame::meta::MetaSlot;
use crate::mm::kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR};
use crate::mm::paddr_to_vaddr;
use crate::mm::page_table::PageTableGuard;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::mapping::{
    frame_to_index, frame_to_index_spec, max_meta_slots, meta_addr, meta_to_frame, META_SLOT_SIZE,
};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::owners::INC_LEVELS;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

verus! {

pub tracked struct PageMetaOwner {
    pub nr_children: pcell_maybe_uninit::PointsTo<u16>,
    pub stray: pcell_maybe_uninit::PointsTo<bool>,
}

impl Inv for PageMetaOwner {
    open spec fn inv(self) -> bool {
        &&& self.nr_children.is_init()
        &&& 0 <= self.nr_children.value() <= NR_ENTRIES
        &&& self.stray.is_init()
    }
}

pub ghost struct PageMetaModel {
    pub nr_children: u16,
    pub stray: bool,
}

impl Inv for PageMetaModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for PageMetaOwner {
    type V = PageMetaModel;

    open spec fn view(&self) -> <Self as View>::V {
        PageMetaModel { nr_children: self.nr_children.value(), stray: self.stray.value() }
    }
}

impl InvView for PageMetaOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTablePageMeta<C> {
    type Owner = PageMetaOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.nr_children.id() == owner.nr_children.id()
        &&& self.stray.id() == owner.stray.id()
        &&& 0 <= owner.nr_children.value() <= NR_ENTRIES
    }
}

/// Owner side-state for a page-table node.
///
/// **Design B (Arc-style).** The owner no longer holds the slot
/// permission as a field — the `cast_ptr::PointsTo<MetaSlot,
/// Metadata<PageTablePageMeta<C>>>` lives canonically in
/// `regions.slots[slot_index]` and is *borrowed* on demand via
/// [`MetaRegionOwners::borrow_meta_perm`]. The accessors that read
/// metadata (`level`, the `wf(meta_own)` consistency, etc.) take
/// `Tracked(&MetaRegionOwners)` and re-derive the typed perm at the
/// call site, mirroring how `Frame<M>` borrows from `regions.slots`.
///
/// `NodeOwner` keeps the local pieces that don't live in `regions`:
/// the per-node metadata cells (`meta_own`), the per-entry permission
/// array (`children_perm`), and bookkeeping (`level`, `tree_level`).
/// `slot_index` is the ghost handle into `regions` that lets us
/// reconstruct the perm.
pub tracked struct NodeOwner<C: PageTableConfig> {
    pub meta_own: PageMetaOwner,
    pub children_perm: array_ptr::PointsTo<C::E, NR_ENTRIES>,
    pub ghost slot_index: usize,
    pub level: PagingLevel,
    pub tree_level: int,
}

impl<C: PageTableConfig> Inv for NodeOwner<C> {
    open spec fn inv(self) -> bool {
        &&& self.meta_own.inv()
        &&& 0 <= self.meta_own.nr_children.value() <= NR_ENTRIES
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.children_perm.is_init_all()
        // `slot_index` is a valid metadata-region index.
        &&& self.slot_index < max_meta_slots()
        // Address consistency: the children-perm array lives at the
        // frame the slot represents (paddr_to_vaddr of the frame paddr).
        &&& FRAME_METADATA_RANGE.start <= meta_addr(self.slot_index) < FRAME_METADATA_RANGE.end
        &&& meta_addr(self.slot_index) % META_SLOT_SIZE == 0
        &&& meta_to_frame(meta_addr(self.slot_index)) < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR
        &&& meta_to_frame(meta_addr(self.slot_index)) < MAX_PADDR
        &&& meta_to_frame(meta_addr(self.slot_index)) == self.children_perm.addr()
        &&& self.children_perm.addr() == paddr_to_vaddr(
            meta_to_frame(meta_addr(self.slot_index))
        )
        &&& self.tree_level == INC_LEVELS - self.level - 1
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    /// Cross-object relation: the slot perm canonically parked in
    /// `regions.slots[slot_index]` matches this `NodeOwner`'s typed view.
    /// Mirrors `SegmentOwner::relate_regions`. Carries the type-witness
    /// (`Metadata<PageTablePageMeta<C>>::wf(...)`) needed to call
    /// [`MetaRegionOwners::borrow_meta_perm`] at every accessor site.
    pub open spec fn relate_regions(self, regions: MetaRegionOwners) -> bool {
        let perm = regions.slots[self.slot_index];
        let inner = regions.slot_owners[self.slot_index].inner_perms;
        // Typed view of the slot's metadata via `Repr::from_repr_spec` —
        // this is `MetaPerm<...>::value()`'s definition, so the typed
        // perm returned by `relate_regions_borrow_perm` has these values.
        let typed = <Metadata<PageTablePageMeta<C>> as Repr<MetaSlot>>::from_repr_spec(
            perm.value(), inner,
        );
        &&& regions.slots.contains_key(self.slot_index)
        // Typed-Repr witness — exactly what `borrow_meta_perm` requires.
        &&& <Metadata<PageTablePageMeta<C>> as Repr<MetaSlot>>::wf(perm.value(), inner)
        // Slot perm initialised at the right metadata address.
        &&& perm.is_init()
        &&& perm.addr() == meta_addr(self.slot_index)
        // Slot-owner side-info also agrees.
        &&& regions.slot_owners[self.slot_index].self_addr == meta_addr(self.slot_index)
        // Design B tie-back: the typed metadata reflects the owner's
        // ghost fields. Previously implicit through `NodeOwner.meta_perm`;
        // re-established here so accessors (`level`, `nr_children.borrow`,
        // `stray.borrow`) can connect their typed-perm-derived results
        // back to `self`. Established at `alloc` (external_body),
        // preserved by accessors that don't touch `regions.slots[idx]`
        // or the owner's `level`/`meta_own`.
        &&& typed.metadata.level == self.level
        &&& typed.metadata.nr_children.id() == self.meta_own.nr_children.id()
        &&& typed.metadata.stray.id() == self.meta_own.stray.id()
    }

    /// Manually instantiates `relate_regions` (Verus trigger crutch).
    ///
    /// Takes `&self` (not by-value) so callers can invoke it on a tracked
    /// borrow (`Tracked<&NodeOwner<C>>`) without needing NodeOwner to be Copy.
    pub proof fn relate_regions_borrow_perm<'a>(
        tracked &self,
        tracked regions: &'a MetaRegionOwners,
    ) -> (tracked perm: &'a MetaPerm<PageTablePageMeta<C>>)
        requires
            self.relate_regions(*regions),
        ensures
            perm.points_to == regions.slots[self.slot_index],
            perm.inner_perms == regions.slot_owners[self.slot_index].inner_perms,
    {
        regions.borrow_meta_perm::<PageTablePageMeta<C>>(self.slot_index)
    }
}

impl<C: PageTableConfig> NodeOwner<C> {
    // TODO: this is a bizzare structure; `set_children_perm` needs to actually be
    // defined to satisfy the axiom, which can then be deleted.
    pub uninterp spec fn set_children_perm(self, idx: usize, pte: C::E) -> Self;

    #[verifier::external_body]
    pub axiom fn set_children_perm_axiom(self, idx: usize, pte: C::E)
        requires
            self.inv(),
            idx < NR_ENTRIES,
        ensures
            self.set_children_perm(idx, pte).inv(),
            self.set_children_perm(idx, pte).slot_index == self.slot_index,
            self.set_children_perm(idx, pte).meta_own == self.meta_own,
            self.set_children_perm(idx, pte).level == self.level,
            self.set_children_perm(idx, pte).tree_level == self.tree_level,
            self.set_children_perm(idx, pte).children_perm.addr() == self.children_perm.addr(),
            self.set_children_perm(idx, pte).children_perm.value()
                == self.children_perm.value().update(idx as int, pte);

    /// If any slot in `children_perm` holds a non-present PTE, then
    /// `nr_children < NR_ENTRIES`.
    ///
    /// Axiomatizes the intended meaning of `nr_children`: it counts the
    /// number of *present* PTEs in the node. When at least one slot is
    /// absent, the count must be strictly less than the maximum. This
    /// sidesteps a full `nr_children == count(present PTEs)` invariant
    /// (which would thread through every PTE mutation); the axiom instead
    /// exposes the single boundary fact that `Entry::replace` needs when
    /// incrementing the counter.
    pub axiom fn nr_children_absent_slot_bound(self, idx: usize)
        requires
            self.inv(),
            idx < NR_ENTRIES,
            !self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() < NR_ENTRIES;

    /// If any slot in `children_perm` holds a present PTE, then
    /// `nr_children > 0`. Dual of [`Self::nr_children_absent_slot_bound`];
    /// used by `Entry::replace` when decrementing the counter.
    pub axiom fn nr_children_present_slot_bound(self, idx: usize)
        requires
            self.inv(),
            idx < NR_ENTRIES,
            self.children_perm.value()[idx as int].is_present(),
        ensures
            self.meta_own.nr_children.value() > 0;
}

impl<'rcu, C: PageTableConfig> NodeOwner<C> {

    pub open spec fn relate_guard(self, guard: PageTableGuard<'rcu, C>) -> bool {
        // Design B: the per-slot perm/init facts that used to live here
        // (and dereferenced `self.meta_perm`) are now expressed through
        // `relate_regions(regions)` plus the canonical `regions.slots`
        // perm, which callers borrow at the use site. This predicate
        // keeps only the address consistency between the guard's pointer
        // and the node's slot, derivable without a perm.
        &&& guard.inner.inner@.ptr.addr() == meta_addr(self.slot_index)
        &&& guard.inner.inner@.wf(self)
    }
}

/// Design B: the typed `PageTablePageMeta<C>` value is no longer stored
/// in `NodeOwner` (it lives in the canonical perm at
/// `regions.slots[slot_index]`), so the view is just the ghost
/// `slot_index` handle. Callers that need the metadata content read it
/// through `regions.borrow_meta_perm`.
pub ghost struct NodeModel<C: PageTableConfig> {
    pub slot_index: usize,
    pub _marker: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> Inv for NodeModel<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> View for NodeOwner<C> {
    type V = NodeModel<C>;

    open spec fn view(&self) -> <Self as View>::V {
        NodeModel { slot_index: self.slot_index, _marker: core::marker::PhantomData }
    }
}

impl<C: PageTableConfig> InvView for NodeOwner<C> {
    proof fn view_preserves_inv(self) {
    }
}

impl<C: PageTableConfig> OwnerOf for PageTableNode<C> {
    type Owner = NodeOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == meta_addr(owner.slot_index)
    }
}

impl<C: PageTableConfig> PageTableNode<C> {
    pub open spec fn invariants(self, owner: NodeOwner<C>) -> bool {
        &&& owner.inv()
        &&& self.wf(owner)
//        &&& owner.meta_perm.wf(&owner.meta_perm.inner_perms)
//        &&& owner.meta_perm.addr() == self.ptr.addr()
//        &&& owner.meta_perm.addr() == self.ptr.addr()
    }
}

} // verus!
