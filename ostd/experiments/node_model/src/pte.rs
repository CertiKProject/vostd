//! Page table entries.
//!
//! Model of `PageTableEntryTrait` (and of `C::E` for a single concrete
//! configuration `C`).
//!
//! In the real code a PTE is a `u64` with an architecture-specific bit layout,
//! and `PageTableEntryTrait` exposes only the four observations the node layer
//! needs (`is_present`, `is_last`, `paddr`, `prop`) plus three constructors,
//! with the laws relating them supplied by `lemma_page_table_entry_properties`.
//! The node layer never looks at the bits.
//!
//! The model therefore replaces the bit layout with a transparent struct. Every
//! law that the real code must axiomatise about the encoding here holds by
//! definition, which is why this file contains no axioms.
use vstd::prelude::*;

use crate::arch::*;
use crate::page_prop::PageProperty;

verus! {

/// A page table entry.
#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub struct Pte {
    /// Whether the entry maps anything at all.
    pub present: bool,
    /// The huge-page bit. A present PTE terminates the walk if it is set, or
    /// if the containing node is at level 1.
    pub huge: bool,
    /// The physical address the entry points at: a child node's frame for a
    /// non-leaf PTE, the mapped page for a leaf PTE.
    pub paddr: Paddr,
    /// The mapping properties, meaningful only for a leaf PTE.
    pub prop: PageProperty,
}

impl Pte {
    // ─── Observations ──────────────────────────────────────────────────────
    //
    // Each comes as a `spec` definition plus an executable version tied to it
    // by `when_used_as_spec`, so that `pte.is_present()` means the same thing
    // in a proof and at run time.
    pub open spec fn is_present_spec(self) -> bool {
        self.present
    }

    /// Whether the entry maps anything.
    #[verifier::when_used_as_spec(is_present_spec)]
    pub fn is_present(self) -> (res: bool)
        returns
            self.is_present_spec(),
    {
        self.present
    }

    pub open spec fn is_last_spec(self, level: PagingLevel) -> bool {
        level == 1 || self.huge
    }

    /// Whether the walk terminates at this entry, given the level of the node
    /// that contains it.
    #[verifier::when_used_as_spec(is_last_spec)]
    pub fn is_last(self, level: PagingLevel) -> (res: bool)
        returns
            self.is_last_spec(level),
    {
        level == 1 || self.huge
    }

    pub open spec fn paddr_spec(self) -> Paddr {
        self.paddr
    }

    /// The physical address the entry points at.
    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(self) -> (res: Paddr)
        returns
            self.paddr_spec(),
    {
        self.paddr
    }

    pub open spec fn prop_spec(self) -> PageProperty {
        self.prop
    }

    /// The mapping properties carried by the entry.
    #[verifier::when_used_as_spec(prop_spec)]
    pub fn prop(self) -> (res: PageProperty)
        returns
            self.prop_spec(),
    {
        self.prop
    }

    // ─── Constructors ──────────────────────────────────────────────────────
    pub open spec fn new_absent_spec() -> Self {
        Pte { present: false, huge: false, paddr: 0, prop: PageProperty { flags: 0 } }
    }

    /// The absent PTE.
    #[verifier::when_used_as_spec(new_absent_spec)]
    pub fn new_absent() -> (res: Self)
        returns
            Self::new_absent_spec(),
    {
        Pte { present: false, huge: false, paddr: 0, prop: PageProperty { flags: 0 } }
    }

    pub open spec fn new_pt_spec(paddr: Paddr) -> Self {
        Pte { present: true, huge: false, paddr, prop: PageProperty { flags: 0 } }
    }

    /// A PTE pointing at a child page table node at `paddr`.
    #[verifier::when_used_as_spec(new_pt_spec)]
    pub fn new_pt(paddr: Paddr) -> (res: Self)
        returns
            Self::new_pt_spec(paddr),
    {
        Pte { present: true, huge: false, paddr, prop: PageProperty { flags: 0 } }
    }

    /// The precondition of `new_page`, mirroring `E::new_page_req`.
    pub open spec fn new_page_req(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> bool {
        &&& valid_frame_paddr(paddr)
        &&& 1 <= level < NR_LEVELS
    }

    pub open spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self {
        Pte { present: true, huge: level > 1, paddr, prop }
    }

    /// A leaf PTE mapping `paddr` at `level` with `prop`.
    #[verifier::when_used_as_spec(new_page_spec)]
    pub fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        requires
            Self::new_page_req(paddr, level, prop),
        returns
            Self::new_page_spec(paddr, level, prop),
    {
        Pte { present: true, huge: level > 1, paddr, prop }
    }

    // ─── The laws ──────────────────────────────────────────────────────────
    //
    // The real code gets these from `E::lemma_page_table_entry_properties()`,
    // an axiom over the opaque bit encoding. Here they are consequences of the
    // definitions above, so the proofs are empty.
    /// The absent PTE is absent, and does not terminate a walk above level 1.
    pub broadcast proof fn lemma_new_absent()
        ensures
            !(#[trigger] Self::new_absent_spec()).is_present(),
            Self::new_absent_spec().paddr() == 0,
    {
    }

    /// A node PTE is present and points at the node.
    pub broadcast proof fn lemma_new_pt(paddr: Paddr)
        ensures
            (#[trigger] Self::new_pt_spec(paddr)).is_present(),
            Self::new_pt_spec(paddr).paddr() == paddr,
    {
    }

    /// A node PTE does not terminate a walk above level 1.
    pub broadcast proof fn lemma_pt_not_last(paddr: Paddr, level: PagingLevel)
        requires
            level > 1,
        ensures
            !(#[trigger] Self::new_pt_spec(paddr).is_last(level)),
    {
    }

    /// The absent PTE does not terminate a walk above level 1.
    pub broadcast proof fn lemma_absent_not_last(level: PagingLevel)
        requires
            level > 1,
        ensures
            !(#[trigger] Self::new_absent_spec().is_last(level)),
    {
    }

    /// A leaf PTE is present, terminates the walk at its own level, and
    /// carries back the address and properties it was built from.
    pub broadcast proof fn lemma_new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty)
        requires
            1 <= level,
        ensures
            (#[trigger] Self::new_page_spec(paddr, level, prop)).is_present(),
            Self::new_page_spec(paddr, level, prop).is_last(level),
            Self::new_page_spec(paddr, level, prop).paddr() == paddr,
            Self::new_page_spec(paddr, level, prop).prop() == prop,
    {
    }

    pub broadcast group group_pte_laws {
        Pte::lemma_new_absent,
        Pte::lemma_new_pt,
        Pte::lemma_pt_not_last,
        Pte::lemma_absent_not_last,
        Pte::lemma_new_page,
    }
}

// ─── Atomic PTE access ─────────────────────────────────────────────────────
//
// Identical in shape to `ostd::mm::page_table::{load_pte, store_pte}`: the
// real ones compile to relaxed/release atomics, which Verus cannot see
// through, so both are axiomatised as an indexed read/write against the
// node's array permission.
//
// Both are `#[verifier::atomic]`: the array permission lives in an
// `AtomicInvariant` (see `node::owners::PteArray`), and a single atomic
// instruction is exactly what may run while that invariant is open.
/// Loads a page table entry with an atomic instruction.
#[verifier::external_body]
#[verifier::atomic]
#[verus_spec(pte =>
    with Tracked(perm): Tracked<&vstd_extra::array_ptr::PointsTo<Pte, NR_ENTRIES>>
    requires
        perm.addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
        perm.is_init_all(),
    ensures
        pte == perm.value()[ptr.index as int],
    opens_invariants none
    no_unwind
)]
pub unsafe fn load_pte(
    ptr: vstd_extra::array_ptr::ArrayPtr<Pte, NR_ENTRIES>,
    ordering: core::sync::atomic::Ordering,
) -> Pte {
    unimplemented!()
}

/// Stores a page table entry with an atomic instruction.
#[verifier::external_body]
#[verifier::atomic]
#[verus_spec(
    with Tracked(perm): Tracked<&mut vstd_extra::array_ptr::PointsTo<Pte, NR_ENTRIES>>
    requires
        old(perm).addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
        old(perm).is_init_all(),
    ensures
        final(perm).wf(),
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init_all(),
        final(perm).value() == old(perm).value().update(ptr.index as int, new_val),
    opens_invariants none
    no_unwind
)]
pub unsafe fn store_pte(
    ptr: vstd_extra::array_ptr::ArrayPtr<Pte, NR_ENTRIES>,
    new_val: Pte,
    ordering: core::sync::atomic::Ordering,
) {
    unimplemented!()
}

} // verus!
