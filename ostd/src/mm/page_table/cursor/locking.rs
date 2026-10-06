// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
//!
//! # The ghost model used by the specifications
//!
//! A page-table node may only be touched by whoever holds its lock. In this
//! verified port the lock guard of a node lives behind a [`PPtr`], and the
//! permission for that pointer, together with the permissions for the node's
//! metadata slot, is bundled in an [`EntryOwner`]. The owners of every node a
//! cursor may reach are threaded through the protocol as a tracked map keyed
//! by the physical address of the node (`owners`). Holding the owners of a
//! sub-tree is the ghost counterpart of holding the sub-tree's locks: because
//! owners are linear, two cursors can never both hold the owner of one node.
//! The frame metadata region (`regions`) is threaded alongside, as the frame
//! code requires.
//!
//! The only admitted facts are the four `axiom_*` lemmas below, which state
//! what the protocol needs from the page-table memory and frame-handle models
//! that this port does not have yet.
use core::{marker::PhantomData, ops::Range, sync::atomic::Ordering};

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::pow;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::array_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::lemma_usize_ilog2_to32;

use aster_common::prelude::frame::*;
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use crate::mm::{
    nr_subpage_per_huge, paddr_to_vaddr,
    page_table::{
        load_pte, pte_index, pte_index_spec, same_canonical_half, ChildRef, PageTable,
        PageTableConfig, PageTableEntryTrait, PageTableGuard, PageTableNodeRef, PagingConstsTrait,
        PagingLevel,
    },
    Paddr, Vaddr,
};

verus! {

// ---------------------------------------------------------------------------
// External specifications for library functions used below.
// ---------------------------------------------------------------------------
pub assume_specification<Idx: Clone>[ Range::<Idx>::clone ](range: &Range<Idx>) -> (res: Range<Idx>)
    ensures
        res == *range,
;

pub assume_specification[ <usize>::div_ceil ](x: usize, y: usize) -> (res: usize)
    requires
        y > 0,
    ensures
        res == (x + y - 1) / (y as int),
;

// ---------------------------------------------------------------------------
// Specification vocabulary.
// ---------------------------------------------------------------------------
/// The configuration uses the x86-64 paging constants. The generic code is
/// written against `C`; every caller instantiates `C` concretely and can
/// discharge this, so it is a precondition rather than an axiom.
pub open spec fn config_is_x86_64<C: PageTableConfig>() -> bool {
    &&& C::NR_LEVELS() == 4
    &&& C::BASE_PAGE_SIZE() == 4096
    &&& C::PTE_SIZE() == 8
}

/// The concrete constants that follow from `config_is_x86_64`.
pub proof fn lemma_config_is_x86_64<C: PageTableConfig>()
    requires
        config_is_x86_64::<C>(),
    ensures
        C::NR_LEVELS() == NR_LEVELS() as PagingLevel,
        C::BASE_PAGE_SIZE() == PAGE_SIZE(),
        nr_subpage_per_huge::<C>() == nr_subpage_per_huge::<PagingConsts>(),
        nr_subpage_per_huge::<C>() == NR_ENTRIES(),
        nr_subpage_per_huge::<C>() == 512,
        NR_LEVELS() == 4,
        NR_ENTRIES() == 512,
        PAGE_SIZE() == 4096,
        PagingConsts::NR_LEVELS() == 4,
        PagingConsts::BASE_PAGE_SIZE() == 4096,
{
    assert(PagingConsts::BASE_PAGE_SIZE_spec() == 4096);
    assert(PagingConsts::PTE_SIZE_spec() == 8);
    assert(PagingConsts::NR_LEVELS_spec() == 4);
    assert(nr_subpage_per_huge::<PagingConsts>() == 512);
}

/// `pte_index` under the x86-64 constants: nine index bits per level above
/// the twelve page-offset bits.
pub proof fn lemma_pte_index_x86_64<C: PageTableConfig>(va: Vaddr, level: PagingLevel)
    requires
        config_is_x86_64::<C>(),
        1 <= level <= 4,
    ensures
        pte_index_spec::<C>(va, level) == (va >> ((12 + 9 * (level - 1)) as usize)) & 0x1ff,
{
    lemma_usize_ilog2_to32();
    assert(C::BASE_PAGE_SIZE().ilog2() == 12);
    assert(nr_subpage_per_huge::<C>() == 512);
    assert(nr_pte_index_bits::<C>() == 9);
}

/// A range that a cursor may lock: non-empty, page aligned, and inside one
/// canonical half of the address space.
pub open spec fn lockable_range(va: Range<Vaddr>) -> bool {
    &&& va.start < va.end
    &&& va.start % PAGE_SIZE() == 0
    &&& va.end % PAGE_SIZE() == 0
    &&& same_canonical_half(va.start, (va.end - 1) as Vaddr)
}

/// Both ends of `va` fall into the same slot at every level above `level`,
/// so the node at `level` that contains `va.start` contains all of `va`.
/// This is what makes a node the "covering node" of the lock protocol.
pub open spec fn node_covers_range<C: PageTableConfig>(
    level: PagingLevel,
    va: Range<Vaddr>,
) -> bool {
    forall|l: PagingLevel|
        level < l && l <= C::NR_LEVELS() ==> #[trigger] pte_index_spec::<C>(va.start, l)
            == pte_index_spec::<C>((va.end - 1) as Vaddr, l)
}

/// The virtual address at which the node at `level` that contains `va` begins.
pub open spec fn node_start_va(va: Vaddr, level: PagingLevel) -> int {
    let node_size = page_size((level + 1) as PagingLevel) as int;
    (va as int / node_size) * node_size
}

/// Going one level down keeps the covering property when both ends of the
/// range share the slot at the level just left.
pub proof fn lemma_covers_descend<C: PageTableConfig>(level: PagingLevel, va: Range<Vaddr>)
    requires
        node_covers_range::<C>(level, va),
        pte_index_spec::<C>(va.start, level) == pte_index_spec::<C>((va.end - 1) as Vaddr, level),
    ensures
        node_covers_range::<C>((level - 1) as PagingLevel, va),
{
    assert forall|l: PagingLevel|
        level - 1 < l && l <= C::NR_LEVELS() implies #[trigger] pte_index_spec::<C>(va.start, l)
        == pte_index_spec::<C>((va.end - 1) as Vaddr, l) by {
        if l != level {
            assert(level < l);
        }
    }
}

/// `align_down` to the span of a node computes `node_start_va`.
pub proof fn lemma_align_down_is_node_start(x: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        (x & !((page_size((level + 1) as PagingLevel) - 1) as usize)) == node_start_va(x, level),
{
    lemma_page_size_values();
    if level == 1 {
        assert((x & !0x1f_ffffusize) == (x / 0x20_0000usize) * 0x20_0000usize) by (bit_vector);
    } else if level == 2 {
        assert((x & !0x3fff_ffffusize) == (x / 0x4000_0000usize) * 0x4000_0000usize)
            by (bit_vector);
    } else if level == 3 {
        assert((x & !0x7f_ffff_ffffusize) == (x / 0x80_0000_0000usize) * 0x80_0000_0000usize)
            by (bit_vector);
    } else {
        assert((x & !0xffff_ffff_ffffusize) == (x / 0x1_0000_0000_0000usize)
            * 0x1_0000_0000_0000usize) by (bit_vector);
    }
}

/// The node at `level` that contains `va.start` contains the whole range:
/// the index bits above `level` agree, and so do the bits above the address
/// width, hence the two ends are in the same node.
pub proof fn lemma_covering_node_contains_range<C: PageTableConfig>(
    level: PagingLevel,
    va: Range<Vaddr>,
)
    requires
        config_is_x86_64::<C>(),
        1 <= level <= 4,
        lockable_range(va),
        node_covers_range::<C>(level, va),
    ensures
        node_start_va(va.start, level) <= va.start,
        va.end <= node_start_va(va.start, level) + page_size((level + 1) as PagingLevel),
{
    lemma_page_size_values();
    let s = va.start;
    let e = (va.end - 1) as Vaddr;
    if level < 4 {
        lemma_pte_index_x86_64::<C>(s, 4);
        lemma_pte_index_x86_64::<C>(e, 4);
        assert(pte_index_spec::<C>(s, 4) == pte_index_spec::<C>(e, 4));
    }
    if level < 3 {
        lemma_pte_index_x86_64::<C>(s, 3);
        lemma_pte_index_x86_64::<C>(e, 3);
        assert(pte_index_spec::<C>(s, 3) == pte_index_spec::<C>(e, 3));
    }
    if level < 2 {
        lemma_pte_index_x86_64::<C>(s, 2);
        lemma_pte_index_x86_64::<C>(e, 2);
        assert(pte_index_spec::<C>(s, 2) == pte_index_spec::<C>(e, 2));
    }
    let n = page_size((level + 1) as PagingLevel) as int;
    if level == 4 {
        assert(s / 0x1_0000_0000_0000usize == e / 0x1_0000_0000_0000usize) by (bit_vector)
            requires
                s >> 48usize == e >> 48usize,
        ;
    } else if level == 3 {
        assert(s / 0x80_0000_0000usize == e / 0x80_0000_0000usize) by (bit_vector)
            requires
                s >> 48usize == e >> 48usize,
                (s >> 39usize) & 0x1ff == (e >> 39usize) & 0x1ff,
        ;
    } else if level == 2 {
        assert(s / 0x4000_0000usize == e / 0x4000_0000usize) by (bit_vector)
            requires
                s >> 48usize == e >> 48usize,
                (s >> 39usize) & 0x1ff == (e >> 39usize) & 0x1ff,
                (s >> 30usize) & 0x1ff == (e >> 30usize) & 0x1ff,
        ;
    } else {
        assert(s / 0x20_0000usize == e / 0x20_0000usize) by (bit_vector)
            requires
                s >> 48usize == e >> 48usize,
                (s >> 39usize) & 0x1ff == (e >> 39usize) & 0x1ff,
                (s >> 30usize) & 0x1ff == (e >> 30usize) & 0x1ff,
                (s >> 21usize) & 0x1ff == (e >> 21usize) & 0x1ff,
        ;
    }
    assert(e as int / n == s as int / n);
    lemma_fundamental_div_mod(e as int, n);
    lemma_fundamental_div_mod(s as int, n);
}

/// `i < ceil(x / s)` implies `i * s < x`.
pub proof fn lemma_lt_ceil_div(i: int, x: int, s: int)
    requires
        s > 0,
        x > 0,
        0 <= i,
        i < (x + s - 1) / s,
    ensures
        i * s < x,
{
    let q = (x + s - 1) / s;
    lemma_fundamental_div_mod(x + s - 1, s);
    lemma_mul_inequality(i, q - 1, s);
    lemma_mul_is_distributive_sub(s, q, 1);
}

/// `i >= floor(y / s)` implies `(i + 1) * s > y`.
pub proof fn lemma_ge_floor_div(i: int, y: int, s: int)
    requires
        s > 0,
        y >= 0,
        i >= y / s,
    ensures
        (i + 1) * s > y,
{
    lemma_fundamental_div_mod(y, s);
    lemma_mul_inequality(y / s, i, s);
    lemma_mul_is_distributive_add(s, i, 1);
}

/// The `i`-th child of the node at `cur_level` starting at `cur_node_va`
/// starts at `cur_node_va + i * size` and is the node at `cur_level - 1`
/// that contains every address in its span.
pub proof fn lemma_child_node_start(cur_node_va: Vaddr, cur_level: PagingLevel, i: int, v: int)
    requires
        2 <= cur_level <= 4,
        cur_node_va % page_size((cur_level + 1) as PagingLevel) == 0,
        0 <= i < 512,
        0 <= v <= usize::MAX,
        cur_node_va + i * page_size(cur_level) <= v,
        v < cur_node_va + i * page_size(cur_level) + page_size(cur_level),
    ensures
        node_start_va(v as Vaddr, (cur_level - 1) as PagingLevel) == cur_node_va + i * page_size(
            cur_level,
        ),
{
    lemma_page_size_next_level(cur_level);
    let child_level = (cur_level - 1) as PagingLevel;
    assert((child_level + 1) as PagingLevel == cur_level);
    let s = page_size(cur_level) as int;
    let big = page_size((cur_level + 1) as PagingLevel) as int;
    assert(big == s * 512);
    lemma_fundamental_div_mod(cur_node_va as int, big);
    let k = cur_node_va as int / big;
    assert(cur_node_va == big * k);
    assert(cur_node_va == (k * 512) * s) by (nonlinear_arith)
        requires
            cur_node_va == big * k,
            big == s * 512,
    ;
    let q = k * 512 + i;
    let r = v - (cur_node_va + i * s);
    assert(v == q * s + r) by (nonlinear_arith)
        requires
            cur_node_va == (k * 512) * s,
            q == k * 512 + i,
            r == v - (cur_node_va + i * s),
    ;
    lemma_fundamental_div_mod_converse(v, s, q, r);
    assert((v / s) * s == cur_node_va + i * s) by (nonlinear_arith)
        requires
            v / s == q,
            q == k * 512 + i,
            cur_node_va == (k * 512) * s,
    ;
    assert(node_start_va(v as Vaddr, child_level) == (v / s) * s);
}

/// The owner is live, has the given level, and `guard` is its lock guard.
pub open spec fn owns_guard<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    pa: Paddr,
    guard: PPtr<PageTableGuard<'rcu, C>>,
) -> bool {
    &&& owners.contains_key(pa)
    &&& owners[pa].guard_perm@.pptr() == guard
}

/// `owners` is a consistent ownership map: every owner is well formed, filed
/// under the physical address of the node it owns, and agrees with the
/// metadata region about the node's slot.
pub open spec fn owners_wf<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    regions: MetaRegionOwners,
) -> bool {
    forall|pa: Paddr| #[trigger]
        owners.contains_key(pa) ==> owners[pa].inv() && owners[pa].paddr() == pa
            && owners[pa].in_region(regions)
}

/// `owners_wf` only looks at the slot owners of the region.
pub proof fn lemma_owners_wf_same_slot_owners<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    r1: MetaRegionOwners,
    r2: MetaRegionOwners,
)
    requires
        owners_wf(owners, r1),
        r1.slot_owners == r2.slot_owners,
    ensures
        owners_wf(owners, r2),
{
    assert forall|pa: Paddr| #[trigger] owners.contains_key(pa) implies owners[pa].inv()
        && owners[pa].paddr() == pa && owners[pa].in_region(r2) by {
        assert(owners[pa].in_region(r1));
    }
}

/// Filing a well-formed owner keeps the map well formed.
pub proof fn lemma_owners_wf_insert<'rcu, C: PageTableConfig>(
    before: Map<Paddr, EntryOwner<'rcu, C>>,
    regions: MetaRegionOwners,
    pa: Paddr,
    own: EntryOwner<'rcu, C>,
)
    requires
        owners_wf(before, regions),
        own.inv(),
        own.paddr() == pa,
        own.in_region(regions),
    ensures
        owners_wf(before.insert(pa, own), regions),
{
    let after = before.insert(pa, own);
    assert forall|q: Paddr| #[trigger] after.contains_key(q) implies after[q].inv()
        && after[q].paddr() == q && after[q].in_region(regions) by {
        if q != pa {
            assert(before.contains_key(q));
        }
    }
}

/// Taking an owner out keeps the map well formed.
pub proof fn lemma_owners_wf_remove<'rcu, C: PageTableConfig>(
    before: Map<Paddr, EntryOwner<'rcu, C>>,
    regions: MetaRegionOwners,
    pa: Paddr,
)
    requires
        owners_wf(before, regions),
    ensures
        owners_wf(before.remove(pa), regions),
{
    let after = before.remove(pa);
    assert forall|q: Paddr| #[trigger] after.contains_key(q) implies after[q].inv()
        && after[q].paddr() == q && after[q].in_region(regions) by {
        assert(before.contains_key(q));
    }
}

/// An owner filed in a well-formed map relates to the region's slot owner
/// for its frame, and its frame is a valid physical page.
pub proof fn lemma_owner_slot<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    regions: MetaRegionOwners,
    pa: Paddr,
)
    requires
        owners_wf(owners, regions),
        regions.inv(),
        owners.contains_key(pa),
    ensures
        regions.slot_owners.contains_key(frame_to_index(pa)),
        owners[pa].relate_slot_owner(&regions.slot_owners[frame_to_index(pa)]),
        pa % PAGE_SIZE() == 0,
        pa < MAX_PADDR(),
        pa < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR(),
        frame_to_meta(pa) == owners[pa].slot_perm@.pptr().addr(),
{
    owners[pa].lemma_in_region_relates(regions);
    lemma_max_paddr_range();
    lemma_meta_to_paddr_biinjective(owners[pa].slot_perm@.pptr().addr());
}

/// The owner filed under `pa` is a live (non-stray) node whose range covers
/// `va`, and `guard` is its lock guard. This is what the traversal phase of
/// the protocol establishes about the sub-tree root.
pub open spec fn covering_node_locked<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    pa: Paddr,
    guard: PPtr<PageTableGuard<'rcu, C>>,
    va: Range<Vaddr>,
) -> bool {
    &&& owns_guard(owners, pa, guard)
    &&& !owners[pa].is_stray()
    &&& 1 <= owners[pa].level() <= C::NR_LEVELS()
    &&& node_covers_range::<C>(owners[pa].level(), va)
}

/// What `lock_range` establishes about the cursor it returns.
pub open spec fn cursor_locked_at<'rcu, C: PageTableConfig, A: InAtomicMode>(
    cursor: Cursor<'rcu, C, A>,
    guard: &'rcu A,
    va: Range<Vaddr>,
) -> bool {
    &&& 1 <= cursor.guard_level <= C::NR_LEVELS()
    &&& cursor.level == cursor.guard_level
    &&& cursor.va == va.start
    &&& cursor.barrier_va == va
    &&& cursor.rcu_guard == guard
    &&& node_covers_range::<C>(cursor.guard_level, va)
    &&& cursor.path[cursor.guard_level - 1] is Some
    &&& forall|i: int|
        0 <= i < MAX_NR_LEVELS() && i != cursor.guard_level - 1 ==> cursor.path[i] is None
}

/// The cursor's guard node is owned: a live node at the guard level whose
/// lock guard sits in the cursor's path.
pub open spec fn cursor_guard_owned<'rcu, C: PageTableConfig, A: InAtomicMode>(
    cursor: Cursor<'rcu, C, A>,
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
) -> bool {
    exists|pa: Paddr| #[trigger]
        owns_guard(owners, pa, cursor.path[cursor.guard_level - 1].unwrap()) && owners[pa].level()
            == cursor.guard_level && !owners[pa].is_stray()
}

/// An upper bound on the number of frames mapped under a node at `level`:
/// at most `u16::MAX` leaves per last-level node, 512 children per level.
pub open spec fn max_frames(level: PagingLevel) -> int {
    0xffff * pow(512, (level - 1) as nat)
}

pub proof fn lemma_max_frames_bounded(level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        max_frames(1) == 0xffff,
        0 < max_frames(level) < 0x1_0000_0000_0000,
        level > 1 ==> 0 < max_frames((level - 1) as PagingLevel),
        level > 1 ==> 512 * max_frames((level - 1) as PagingLevel) == max_frames(level),
{
    reveal_with_fuel(pow, 5);
    assert(pow(512, 0) == 1);
    assert(pow(512, 1) == 512);
    assert(pow(512, 2) == 0x40000);
    assert(pow(512, 3) == 0x8000000);
}

// ---------------------------------------------------------------------------
// Assumptions about the page-table memory model.
//
// These are the facts the protocol needs from the contents of page-table
// pages. `load_pte` reads a PTE through a raw pointer with no permission,
// and `EntryOwner` does not yet carry a view of its node's entries, so the
// link between a PTE read from memory and the owner of the node it points
// to cannot be proven here. They are collected as named lemmas so that the
// gap is explicit and localised.
// ---------------------------------------------------------------------------
/// A present, non-leaf entry of an owned node points to a node that is also
/// owned, one level below the parent.
pub proof fn axiom_pte_child_owned<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    parent: EntryOwner<'rcu, C>,
    child_pa: Paddr,
)
    requires
        parent.inv(),
    ensures
        owners.contains_key(child_pa),
        owners[child_pa].level() + 1 == parent.level(),
        child_pa != parent.paddr(),
{
    admit();
}

/// A child of a locked, live node is live: recycling marks a sub-tree stray
/// only while holding every lock in it.
pub proof fn axiom_locked_child_live<'rcu, C: PageTableConfig>(
    parent: EntryOwner<'rcu, C>,
    child: EntryOwner<'rcu, C>,
)
    requires
        !parent.is_stray(),
    ensures
        !child.is_stray(),
{
    admit();
}

/// The physical address in any entry is a valid, page-aligned frame address.
pub proof fn axiom_pte_paddr_wf<E: PageTableEntryTrait>(pte: E)
    ensures
        pte.paddr() % PAGE_SIZE() == 0,
        pte.paddr() < MAX_PADDR(),
{
    admit();
}

/// The frame handle of a page-table node is a forgotten (raw) handle, so
/// `borrow_paddr` may re-create a reference to it. The frame model moves the
/// slot permission into `slots` on every borrow and never back, so this has
/// to be assumed each time.
pub proof fn axiom_node_handle_raw(regions: MetaRegionOwners, pa: Paddr)
    ensures
        !regions.slots.contains_key(frame_to_index(pa)),
        regions.dropped_slots.contains_key(frame_to_index(pa)),
{
    admit();
}

// ---------------------------------------------------------------------------
// The protocol.
// ---------------------------------------------------------------------------
/// The page table's root node is owned: filed under its address, at the top
/// level, live, and the owner's slot permission is the root frame's slot.
pub open spec fn root_owned<'rcu, C: PageTableConfig>(
    pt: &PageTable<C>,
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
) -> bool {
    &&& owners.contains_key(pt.root.paddr())
    &&& owners[pt.root.paddr()].slot_perm@.pptr() == pt.root.ptr
    &&& owners[pt.root.paddr()].level() == C::NR_LEVELS()
    &&& !owners[pt.root.paddr()].is_stray()
}

/// Locks the sub-tree covering `va` and returns a cursor positioned at its
/// start.
///
/// This is `AddrSpace::lock` of the protocol: find and lock the covering node
/// (retrying if the node turned out to be stray because of a race with page
/// table recycling), then lock every node beneath it that intersects `va`,
/// in pre-order DFS.
#[verus_spec(
    with Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'rcu, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
#[verifier::exec_allows_no_decreases_clause]
pub fn lock_range<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &'rcu PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> (cursor: Cursor<'rcu, C, A>)
    requires
        config_is_x86_64::<C>(),
        lockable_range(*va),
        old(regions).inv(),
        owners_wf(*old(owners), *old(regions)),
        root_owned(pt, *old(owners)),
    ensures
        cursor_locked_at(cursor, guard, *va),
        cursor_guard_owned(cursor, *owners),
        owners_wf(*owners, *regions),
        root_owned(pt, *owners),
        regions.inv(),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    // The re-try loop of finding the sub-tree root.
    //
    // If we locked a stray node, we need to re-try. Otherwise, although
    // there are no safety concerns, the operations of a cursor on an stray
    // sub-tree will not see the current state and will not change the current
    // state, breaking serializability.
    let mut subtree_root_opt: Option<PPtr<PageTableGuard<'rcu, C>>> = None;
    loop
        invariant_except_break
            subtree_root_opt is None,
            config_is_x86_64::<C>(),
            lockable_range(*va),
            regions.inv(),
            owners_wf(*owners, *regions),
            root_owned(pt, *owners),
        ensures
            subtree_root_opt is Some,
            subtree_root_opt matches Some(subtree_root) ==> exists|pa: Paddr| #[trigger]
                covering_node_locked(*owners, pa, subtree_root, *va),
            regions.inv(),
            owners_wf(*owners, *regions),
            root_owned(pt, *owners),
    {
        #[verus_spec(with Tracked(owners), Tracked(regions))]
        let found = try_traverse_and_lock_subtree_root(pt, guard, va);
        match found {
            Some(subtree_root) => {
                subtree_root_opt = Some(subtree_root);
                break;
            },
            None => {},
        }
    }
    let subtree_root = match subtree_root_opt {
        Some(subtree_root) => subtree_root,
        None => unreached(),
    };

    // Once we have locked the sub-tree that is not stray, we won't read any
    // stray nodes in the following traversal since we must lock before reading.
    let ghost root_pa = choose|pa: Paddr| covering_node_locked(*owners, pa, subtree_root, *va);
    let ghost owners0 = *owners;
    proof {
        lemma_owner_slot(*owners, *regions, root_pa);
        lemma_owners_wf_remove(*owners, *regions, root_pa);
    }
    let tracked root_own = owners.tracked_remove(root_pa);
    let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(root_pa));

    let subtree_guard = subtree_root.borrow(Tracked(root_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(slot_own), Tracked(root_own.slot_perm.borrow()), Tracked(root_own.node_own.meta_perm.borrow()))]
    let guard_level = subtree_guard.level();

    proof {
        lemma_page_size_next_level(guard_level);
        lemma_align_down_is_node_start(va.start, guard_level);
        lemma_covering_node_contains_range::<C>(guard_level, *va);
    }
    let cur_node_va = align_down(va.start, page_size((guard_level + 1) as PagingLevel));

    #[verus_spec(with Tracked(&root_own), Tracked(owners), Tracked(regions))]
    dfs_acquire_lock(guard, subtree_root, cur_node_va, va.clone());

    proof {
        lemma_owners_wf_insert(*owners, *regions, root_pa, root_own);
        owners.tracked_insert(root_pa, root_own);
        assert(*owners =~= owners0);
    }

    let mut path: [Option<PPtr<PageTableGuard<'rcu, C>>>; 4] = [None, None, None, None];
    path.set(guard_level as usize - 1, Some(subtree_root));

    let cursor = Cursor::<'rcu, C, A> {
        path,
        rcu_guard: guard,
        level: guard_level,
        guard_level,
        va: va.start,
        barrier_va: va.clone(),
        _phantom: PhantomData,
    };
    assert(owns_guard(*owners, root_pa, subtree_root));
    cursor
}

/// Releases every lock held by `cursor`, in the reverse order of acquisition.
///
/// This is `AddrSpace::unlock` of the protocol. Guards below the guard level
/// are merely forgotten (the cursor already left those nodes); the sub-tree
/// under the guard node is unlocked by a reverse-order DFS, and the guard
/// node itself is unlocked last.
#[verus_spec(
    with Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'rcu, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
pub fn unlock_range<'rcu, C: PageTableConfig, A: InAtomicMode>(cursor: &mut Cursor<'rcu, C, A>)
    requires
        config_is_x86_64::<C>(),
        1 <= old(cursor).level <= old(cursor).guard_level <= C::NR_LEVELS(),
        old(cursor).path[old(cursor).guard_level - 1] is Some,
        forall|i: int|
            0 <= i < MAX_NR_LEVELS() && i != old(cursor).guard_level - 1 ==> old(
                cursor,
            ).path[i] is None,
        lockable_range(old(cursor).barrier_va),
        node_covers_range::<C>(old(cursor).guard_level, old(cursor).barrier_va),
        cursor_guard_owned(*old(cursor), *old(owners)),
        owners_wf(*old(owners), *old(regions)),
        old(regions).inv(),
    ensures
        forall|i: int| 0 <= i < MAX_NR_LEVELS() ==> cursor.path[i] is None,
        cursor.guard_level == old(cursor).guard_level,
        cursor.barrier_va == old(cursor).barrier_va,
        owners_wf(*owners, *regions),
        regions.inv(),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    // Forget the guards below the guard level. In the `PPtr` model there is
    // nothing to drop: the locks they stand for are released by the DFS below.
    let end = cursor.guard_level as usize - 1;
    let mut i: usize = 0;
    while i < end
        invariant
            i <= end,
            end == cursor.guard_level - 1,
            cursor.guard_level == old(cursor).guard_level,
            cursor.barrier_va == old(cursor).barrier_va,
            cursor.rcu_guard == old(cursor).rcu_guard,
            cursor.path[end as int] == old(cursor).path[end as int],
            1 <= cursor.guard_level <= 4,
            forall|j: int| 0 <= j < i ==> cursor.path[j] is None,
            forall|j: int| end < j < MAX_NR_LEVELS() ==> cursor.path[j] is None,
            *owners == *old(owners),
            *regions == *old(regions),
        decreases end - i,
    {
        cursor.path.set(i, None);
        i = i + 1;
    }
    let guard_node = match cursor.path[end] {
        Some(guard_node) => guard_node,
        None => unreached(),
    };
    cursor.path.set(end, None);

    let ghost root_pa = choose|pa: Paddr| #[trigger]
        owns_guard(*owners, pa, guard_node) && owners[pa].level() == cursor.guard_level
            && !owners[pa].is_stray();
    proof {
        lemma_owner_slot(*owners, *regions, root_pa);
        lemma_owners_wf_remove(*owners, *regions, root_pa);
        lemma_page_size_next_level(cursor.guard_level);
        lemma_align_down_is_node_start(cursor.barrier_va.start, cursor.guard_level);
        lemma_covering_node_contains_range::<C>(cursor.guard_level, cursor.barrier_va);
    }
    let cur_node_va = align_down(
        cursor.barrier_va.start,
        page_size((cursor.guard_level + 1) as PagingLevel),
    );
    let tracked root_own = owners.tracked_remove(root_pa);

    // A cursor maintains that its corresponding sub-tree is locked.
    #[verus_spec(with Tracked(&root_own), Tracked(owners), Tracked(regions))]
    dfs_release_lock(cursor.rcu_guard, guard_node, cur_node_va, cursor.barrier_va.clone());

    // Dropping the guard node's guard releases its lock.
    #[verus_spec(with Tracked(&root_own))]
    PageTableGuard::<'rcu, C>::unlock(guard_node);

    proof {
        lemma_owners_wf_insert(*owners, *regions, root_pa, root_own);
        owners.tracked_insert(root_pa, root_own);
    }
}

/// Finds and locks an intermediate page table node that covers the range.
///
/// If that node (or any of its ancestors) does not exist, we need to lock
/// the parent and create it. After the creation the lock of the parent will
/// be released and the new node will be locked.
///
/// If this function founds that a locked node is stray (because of racing with
/// page table recycling), it will return `None`. The caller should retry in
/// this case to lock the proper node.
///
/// This is the lock-free traversal phase of the protocol: no lock is taken
/// while walking down, so the node reached may already have been detached,
/// which the stray flag detects after locking.
#[verus_spec(
    with Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'rcu, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
fn try_traverse_and_lock_subtree_root<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
    requires
        config_is_x86_64::<C>(),
        lockable_range(*va),
        old(regions).inv(),
        owners_wf(*old(owners), *old(regions)),
        root_owned(pt, *old(owners)),
    ensures
        regions.inv(),
        owners_wf(*owners, *regions),
        root_owned(pt, *owners),
        res matches Some(subtree_root) ==> exists|pa: Paddr| #[trigger]
            covering_node_locked(*owners, pa, subtree_root, *va),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    let mut cur_node_guard: Option<PPtr<PageTableGuard<'rcu, C>>> = None;

    // The root's address is read through the root owner's slot permission.
    let ghost root_pa = pt.root.paddr();
    let mut cur_pt_addr: Paddr = {
        proof {
            lemma_owner_slot(*owners, *regions, root_pa);
        }
        let tracked root_own = owners.tracked_borrow(root_pa);
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(root_pa));
        #[verus_spec(with Tracked(slot_own), Tracked(root_own.slot_perm.borrow()))]
        let root_paddr = pt.root.start_paddr();
        root_paddr
    };

    // Walk from the top level down to level 1 (`(1..=NR_LEVELS).rev()`).
    // `level` is the level of the node at `cur_pt_addr`.
    let mut level: PagingLevel = C::NR_LEVELS();
    loop
        invariant_except_break
            config_is_x86_64::<C>(),
            lockable_range(*va),
            1 <= level <= 4,
            regions.inv(),
            owners_wf(*owners, *regions),
            root_owned(pt, *owners),
            node_covers_range::<C>(level, *va),
            owners.contains_key(cur_pt_addr),
            owners[cur_pt_addr].level() == level,
            cur_node_guard matches Some(g) ==> owns_guard(*owners, cur_pt_addr, g)
                && !owners[cur_pt_addr].is_stray(),
        ensures
            1 <= level <= 4,
            regions.inv(),
            owners_wf(*owners, *regions),
            root_owned(pt, *owners),
            node_covers_range::<C>(level, *va),
            owners.contains_key(cur_pt_addr),
            owners[cur_pt_addr].level() == level,
            cur_node_guard matches Some(g) ==> owns_guard(*owners, cur_pt_addr, g)
                && !owners[cur_pt_addr].is_stray(),
        decreases level,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }

        let start_idx = pte_index::<C>(va.start, level);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, level);
            level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            break;
        }
        proof {
            lemma_owner_slot(*owners, *regions, cur_pt_addr);
        }
        let cur_pt_ptr = ArrayPtr::<C::E, CONST_NR_ENTRIES>::from_addr(paddr_to_vaddr(cur_pt_addr));
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = load_pte(cur_pt_ptr.add(start_idx), Ordering::Acquire);

        if cur_pte.is_present() {
            if cur_pte.is_last(level) {
                break;
            }
            let ghost parent_pa = cur_pt_addr;
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            proof {
                axiom_pte_child_owned(*owners, owners[parent_pa], cur_pt_addr);
                lemma_covers_descend::<C>(level, *va);
            }
            level = level - 1;
            continue;
        }
        // In case the child is absent, we should lock and allocate a new page table node.

        let node_pa = cur_pt_addr;
        let pt_guard = match cur_node_guard {
            Some(pt_guard) => pt_guard,
            None => {
                let ghost r0 = *regions;
                proof {
                    lemma_owner_slot(*owners, *regions, node_pa);
                    axiom_node_handle_raw(*regions, node_pa);
                }
                // SAFETY: The node must be alive for at least `'rcu` since the
                // address is read from the page table node.
                #[verus_spec(with Tracked(regions))]
                let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(node_pa);
                proof {
                    lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
                }
                let tracked node_own = owners.tracked_borrow(node_pa);
                assert(node_ref.inner.ptr == node_own.slot_perm@.pptr());
                #[verus_spec(with Tracked(node_own))]
                let locked = node_ref.lock(guard);
                locked
            },
        };

        let ghost owners0 = *owners;
        proof {
            lemma_owner_slot(*owners, *regions, node_pa);
            lemma_owners_wf_remove(*owners, *regions, node_pa);
        }
        let tracked mut cur_own = owners.tracked_remove(node_pa);
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(node_pa));

        let guard_val = pt_guard.borrow(Tracked(cur_own.guard_perm.borrow()));
        #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
        let stray_cell = guard_val.stray_mut();
        let is_stray = *stray_cell.borrow(Tracked(cur_own.node_own.meta_own.stray.borrow()));
        if is_stray {
            // Raced with the recycling of this node: unlock it, give the owner
            // back, and let the caller retry.
            #[verus_spec(with Tracked(&cur_own))]
            PageTableGuard::<'rcu, C>::unlock(pt_guard);
            proof {
                lemma_owners_wf_insert(*owners, *regions, node_pa, cur_own);
                owners.tracked_insert(node_pa, cur_own);
                assert(*owners == owners0);
            }
            return None;
        }
        #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
        let mut cur_entry = PageTableGuard::<'rcu, C>::entry(pt_guard, start_idx);
        proof {
            axiom_pte_paddr_wf(cur_entry.pte);
        }
        if cur_entry.is_none() {
            let tracked mut new_child_own: Option<EntryOwner<'rcu, C>> = None;
            let ghost r0 = *regions;
            #[verus_spec(with Tracked(&mut cur_own), Tracked(regions), Tracked(&*owners), Tracked(&mut new_child_own))]
            let allocated = cur_entry.alloc_if_none(guard);
            proof {
                lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
            }
            match allocated {
                Some(allocated_guard) => {
                    let tracked child_own = new_child_own.tracked_unwrap();
                    let ghost child_pa = child_own.paddr();
                    proof {
                        child_own.lemma_in_region_relates(*regions);
                    }
                    let tracked child_slot_own = regions.slot_owners.tracked_borrow(
                        frame_to_index(child_pa),
                    );
                    let child_guard = allocated_guard.borrow(
                        Tracked(child_own.guard_perm.borrow()),
                    );
                    #[verus_spec(with Tracked(child_slot_own), Tracked(child_own.slot_perm.borrow()))]
                    let child_paddr = child_guard.start_paddr();
                    cur_pt_addr = child_paddr;
                    cur_node_guard = Some(allocated_guard);
                    proof {
                        lemma_owners_wf_insert(*owners, *regions, child_pa, child_own);
                        owners.tracked_insert(child_pa, child_own);
                        lemma_covers_descend::<C>(level, *va);
                        assert(child_pa != node_pa);
                        assert(child_pa != pt.root.paddr());
                    }
                    level = level - 1;
                },
                None => {
                    // `alloc_if_none` only fails if the entry is present or the
                    // node is a leaf; neither holds here (`is_none` and `level > 1`).
                    unreached()
                },
            }
        } else {
            #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
            let is_node = cur_entry.is_node();
            if is_node {
                let ghost r0 = *regions;
                proof {
                    axiom_node_handle_raw(*regions, cur_entry.pte.paddr());
                }
                #[verus_spec(with Tracked(&cur_own), Tracked(regions))]
                let child_ref = cur_entry.to_ref();
                proof {
                    lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
                }
                match child_ref {
                    ChildRef::PageTable(pt_ref) => {
                        let ghost child_pa = pt_ref.inner.paddr();
                        proof {
                            axiom_pte_child_owned(*owners, cur_own, child_pa);
                            lemma_owner_slot(*owners, *regions, child_pa);
                        }
                        let tracked child_own = owners.tracked_borrow(child_pa);
                        let tracked child_slot_own = regions.slot_owners.tracked_borrow(
                            frame_to_index(child_pa),
                        );
                        assert(pt_ref.inner.ptr == child_own.slot_perm@.pptr());
                        #[verus_spec(with Tracked(child_slot_own), Tracked(child_own.slot_perm.borrow()))]
                        let child_paddr = pt_ref.start_paddr();
                        cur_pt_addr = child_paddr;
                        cur_node_guard = None;
                        proof {
                            lemma_covers_descend::<C>(level, *va);
                        }
                        level = level - 1;
                    },
                    ChildRef::Frame(_, _, _) | ChildRef::None => {
                        // `is_node` guarantees a page-table child.
                        unreached()
                    },
                }
            } else {
                // A (huge) page is mapped here: this node is the covering node.
                // Its guard is dropped (unlocked) now and re-acquired below.
                #[verus_spec(with Tracked(&cur_own))]
                PageTableGuard::<'rcu, C>::unlock(pt_guard);
                proof {
                    lemma_owners_wf_insert(*owners, *regions, node_pa, cur_own);
                    owners.tracked_insert(node_pa, cur_own);
                    assert(*owners == owners0);
                }
                break;
            }
        }
        // The guard of the node we came from goes out of scope here, which
        // releases its lock. Only the newly allocated child (if any) stays
        // locked through `cur_node_guard`.
        #[verus_spec(with Tracked(&cur_own))]
        PageTableGuard::<'rcu, C>::unlock(pt_guard);
        proof {
            lemma_owners_wf_insert(*owners, *regions, node_pa, cur_own);
            owners.tracked_insert(node_pa, cur_own);
            assert(owners[node_pa] == cur_own);
            assert(cur_pt_addr != node_pa);
            if node_pa != pt.root.paddr() {
                assert(owners[pt.root.paddr()] == owners0[pt.root.paddr()]);
            }
            assert(root_owned(pt, *owners));
        }
    }

    let node_pa = cur_pt_addr;
    let pt_guard = match cur_node_guard {
        Some(pt_guard) => pt_guard,
        None => {
            let ghost r0 = *regions;
            proof {
                lemma_owner_slot(*owners, *regions, node_pa);
                axiom_node_handle_raw(*regions, node_pa);
            }
            // SAFETY: The node must be alive for at least `'rcu` since the
            // address is read from the page table node.
            #[verus_spec(with Tracked(regions))]
            let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(node_pa);
            proof {
                lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
            }
            let tracked node_own = owners.tracked_borrow(node_pa);
            assert(node_ref.inner.ptr == node_own.slot_perm@.pptr());
            #[verus_spec(with Tracked(node_own))]
            let locked = node_ref.lock(guard);
            locked
        },
    };

    let ghost owners0 = *owners;
    proof {
        lemma_owner_slot(*owners, *regions, node_pa);
        lemma_owners_wf_remove(*owners, *regions, node_pa);
    }
    let tracked cur_own = owners.tracked_remove(node_pa);
    let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(node_pa));

    let guard_val = pt_guard.borrow(Tracked(cur_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
    let stray_cell = guard_val.stray_mut();
    let is_stray = *stray_cell.borrow(Tracked(cur_own.node_own.meta_own.stray.borrow()));
    if is_stray {
        #[verus_spec(with Tracked(&cur_own))]
        PageTableGuard::<'rcu, C>::unlock(pt_guard);
        proof {
            lemma_owners_wf_insert(*owners, *regions, node_pa, cur_own);
            owners.tracked_insert(node_pa, cur_own);
            assert(*owners == owners0);
        }
        return None;
    }
    proof {
        lemma_owners_wf_insert(*owners, *regions, node_pa, cur_own);
        owners.tracked_insert(node_pa, cur_own);
        assert(*owners == owners0);
    }
    assert(covering_node_locked(*owners, node_pa, pt_guard, *va));
    Some(pt_guard)
}

/// The arithmetic facts about the `i`-th child of the node at `cur_level`
/// (starting at `cur_node_va`) that both DFS passes rely on, for a child
/// index inside the range computed by `dfs_get_idx_range`.
pub proof fn lemma_dfs_child_range(
    cur_level: PagingLevel,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
    i: int,
)
    requires
        2 <= cur_level <= 4,
        cur_node_va == node_start_va(va_range.start, cur_level),
        cur_node_va <= va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_level + 1) as PagingLevel),
        (va_range.start - cur_node_va) / page_size(cur_level) as int <= i,
        i < (va_range.end - cur_node_va + page_size(cur_level) - 1) / page_size(cur_level) as int,
    ensures
        0 <= i < 512,
        cur_node_va + i * page_size(cur_level) < va_range.end,
        va_range.start < cur_node_va + i * page_size(cur_level) + page_size(cur_level),
        cur_node_va % page_size((cur_level + 1) as PagingLevel) == 0,
{
    lemma_page_size_next_level(cur_level);
    let s = page_size(cur_level) as int;
    let big = page_size((cur_level + 1) as PagingLevel) as int;
    lemma_lt_ceil_div(i, va_range.end - cur_node_va, s);
    lemma_ge_floor_div(i, va_range.start - cur_node_va, s);
    assert((i + 1) * s == i * s + s) by (nonlinear_arith);
    lemma_mod_multiples_basic(va_range.start as int / big, big);
    // `i < 512` since `i * s < va_range.end - cur_node_va <= 512 * s`.
    assert(i < 512) by (nonlinear_arith)
        requires
            s > 0,
            i * s < big,
            big == s * 512,
    ;
}

/// Acquires the locks for the given range in the sub-tree rooted at the node.
///
/// `cur_node_va` must be the virtual address of the `cur_node`. The `va_range`
/// must be within the range of the `cur_node`. The range must not be empty.
///
/// The function will forget all the [`PageTableGuard`] objects in the sub-tree.
///
/// This is the locking phase of the protocol: the covering node is already
/// locked (its owner is `cur_own`), and every child that intersects
/// `va_range` is locked in pre-order.
#[verus_spec(
    with Tracked(cur_own): Tracked<&EntryOwner<'rcu, C>>,
        Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'rcu, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: PPtr<PageTableGuard<'rcu, C>>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
)
    requires
        config_is_x86_64::<C>(),
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == cur_node,
        !cur_own.is_stray(),
        1 <= cur_own.level() <= 4,
        cur_own.in_region(*old(regions)),
        cur_node_va == node_start_va(va_range.start, cur_own.level()),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_own.level() + 1) as PagingLevel),
        old(regions).inv(),
        owners_wf(*old(owners), *old(regions)),
    ensures
        regions.inv(),
        regions.slot_owners == old(regions).slot_owners,
        owners_wf(*owners, *regions),
        *owners == *old(owners),
    decreases cur_own.level(),
{
    proof {
        lemma_config_is_x86_64::<C>();
        cur_own.lemma_in_region_relates(*regions);
    }

    let cur_level = {
        let cur_guard = cur_node.borrow(Tracked(cur_own.guard_perm.borrow()));
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
        #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
        let level = cur_guard.level();
        level
    };
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let size = page_size(cur_level);
    let start = idx_range.start;
    let end = idx_range.end;
    let mut i = start;
    while i < end
        invariant
            config_is_x86_64::<C>(),
            start <= i <= end,
            end <= 512,
            start == (va_range.start - cur_node_va) / size as int,
            end == (va_range.end - cur_node_va + size - 1) / size as int,
            size == page_size(cur_level),
            2 <= cur_level <= 4,
            cur_level == cur_own.level(),
            cur_own.inv(),
            !cur_own.is_stray(),
            cur_own.guard_perm@.pptr() == cur_node,
            cur_own.in_region(*old(regions)),
            cur_node_va == node_start_va(va_range.start, cur_level),
            cur_node_va <= va_range.start,
            va_range.start < va_range.end,
            va_range.end <= cur_node_va + page_size((cur_level + 1) as PagingLevel),
            regions.inv(),
            regions.slot_owners == old(regions).slot_owners,
            owners_wf(*owners, *regions),
            *owners == *old(owners),
        decreases end - i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
            cur_own.lemma_in_region_relates(*regions);
        }
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
        #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, i);

        let ghost r0 = *regions;
        proof {
            axiom_pte_paddr_wf(child.pte);
            axiom_node_handle_raw(*regions, child.pte.paddr());
        }
        #[verus_spec(with Tracked(cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        proof {
            lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                proof {
                    axiom_pte_child_owned(*owners, *cur_own, child_pa);
                    axiom_locked_child_live(*cur_own, owners[child_pa]);
                    lemma_owner_slot(*owners, *regions, child_pa);
                    lemma_owners_wf_remove(*owners, *regions, child_pa);
                }
                let ghost owners0 = *owners;
                let tracked child_own = owners.tracked_remove(child_pa);
                assert(pt.inner.ptr == child_own.slot_perm@.pptr());
                #[verus_spec(with Tracked(&child_own))]
                let pt_guard = pt.lock(guard);

                proof {
                    lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                }
                let child_node_va = cur_node_va + i * size;
                let va_start = if va_range.start > child_node_va {
                    va_range.start
                } else {
                    child_node_va
                };
                let va_end = if va_range.end - child_node_va <= size {
                    va_range.end
                } else {
                    child_node_va + size
                };
                proof {
                    lemma_child_node_start(cur_node_va, cur_level, i as int, va_start as int);
                }

                #[verus_spec(with Tracked(&child_own), Tracked(owners), Tracked(regions))]
                dfs_acquire_lock(guard, pt_guard, child_node_va, va_start..va_end);

                // The child's guard is forgotten (`ManuallyDrop` in the original):
                // the child stays locked until `dfs_release_lock`.
                proof {
                    lemma_owners_wf_insert(*owners, *regions, child_pa, child_own);
                    owners.tracked_insert(child_pa, child_own);
                    assert(*owners =~= owners0);
                }
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
        i = i + 1;
    }
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten (which the `requires` below express: the
/// caller holds the owner of the sub-tree root).
#[verus_spec(
    with Tracked(cur_own): Tracked<&EntryOwner<'rcu, C>>,
        Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'rcu, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: PPtr<PageTableGuard<'rcu, C>>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
)
    requires
        config_is_x86_64::<C>(),
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == cur_node,
        !cur_own.is_stray(),
        1 <= cur_own.level() <= 4,
        cur_own.in_region(*old(regions)),
        cur_node_va == node_start_va(va_range.start, cur_own.level()),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_own.level() + 1) as PagingLevel),
        old(regions).inv(),
        owners_wf(*old(owners), *old(regions)),
    ensures
        regions.inv(),
        regions.slot_owners == old(regions).slot_owners,
        owners_wf(*owners, *regions),
        *owners == *old(owners),
    decreases cur_own.level(),
{
    proof {
        lemma_config_is_x86_64::<C>();
        cur_own.lemma_in_region_relates(*regions);
    }

    let cur_level = {
        let cur_guard = cur_node.borrow(Tracked(cur_own.guard_perm.borrow()));
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
        #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
        let level = cur_guard.level();
        level
    };
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let size = page_size(cur_level);
    let start = idx_range.start;
    let end = idx_range.end;
    // Reverse order of acquisition.
    let mut i = end;
    while i > start
        invariant
            config_is_x86_64::<C>(),
            start <= i <= end,
            end <= 512,
            start == (va_range.start - cur_node_va) / size as int,
            end == (va_range.end - cur_node_va + size - 1) / size as int,
            size == page_size(cur_level),
            2 <= cur_level <= 4,
            cur_level == cur_own.level(),
            cur_own.inv(),
            !cur_own.is_stray(),
            cur_own.guard_perm@.pptr() == cur_node,
            cur_own.in_region(*old(regions)),
            cur_node_va == node_start_va(va_range.start, cur_level),
            cur_node_va <= va_range.start,
            va_range.start < va_range.end,
            va_range.end <= cur_node_va + page_size((cur_level + 1) as PagingLevel),
            regions.inv(),
            regions.slot_owners == old(regions).slot_owners,
            owners_wf(*owners, *regions),
            *owners == *old(owners),
        decreases i,
    {
        i = i - 1;

        proof {
            lemma_config_is_x86_64::<C>();
            cur_own.lemma_in_region_relates(*regions);
        }
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
        #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, i);

        let ghost r0 = *regions;
        proof {
            axiom_pte_paddr_wf(child.pte);
            axiom_node_handle_raw(*regions, child.pte.paddr());
        }
        #[verus_spec(with Tracked(cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        proof {
            lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                proof {
                    axiom_pte_child_owned(*owners, *cur_own, child_pa);
                    axiom_locked_child_live(*cur_own, owners[child_pa]);
                    lemma_owner_slot(*owners, *regions, child_pa);
                    lemma_owners_wf_remove(*owners, *regions, child_pa);
                }
                let ghost owners0 = *owners;
                let tracked child_own = owners.tracked_remove(child_pa);
                assert(pt.inner.ptr == child_own.slot_perm@.pptr());
                // The node is locked (by `dfs_acquire_lock`) and its guard was
                // forgotten, so re-creating the guard is unique.
                #[verus_spec(with Tracked(&child_own))]
                let child_node = pt.make_guard_unchecked(guard);

                proof {
                    lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                }
                let child_node_va = cur_node_va + i * size;
                let va_start = if va_range.start > child_node_va {
                    va_range.start
                } else {
                    child_node_va
                };
                let va_end = if va_range.end - child_node_va <= size {
                    va_range.end
                } else {
                    child_node_va + size
                };
                proof {
                    lemma_child_node_start(cur_node_va, cur_level, i as int, va_start as int);
                }

                // All the nodes in the sub-tree are locked and all guards are forgotten.
                #[verus_spec(with Tracked(&child_own), Tracked(owners), Tracked(regions))]
                dfs_release_lock(guard, child_node, child_node_va, va_start..va_end);

                // Dropping the re-created guard releases the child's lock.
                #[verus_spec(with Tracked(&child_own))]
                PageTableGuard::<'rcu, C>::unlock(child_node);
                proof {
                    lemma_owners_wf_insert(*owners, *regions, child_pa, child_own);
                    owners.tracked_insert(child_pa, child_own);
                    assert(*owners =~= owners0);
                }
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }
}

/// Marks all the nodes in the sub-tree rooted at the node as stray, and
/// returns the num of pages mapped within the sub-tree.
///
/// It must be called upon the node after the node is removed from the parent
/// page table. It also unlocks the nodes in the sub-tree.
///
/// This function returns the number of physical frames mapped in the sub-tree.
///
/// The caller must ensure that all the nodes in the sub-tree are locked
/// and all guards are forgotten (expressed below by the caller holding the
/// sub-tree root's owner).
///
/// This function must not be called upon a shared node, e.g., the second-
/// top level nodes that the kernel space and user space share.
///
/// In the protocol this is what makes a concurrent traversal that reaches a
/// recycled node notice it and retry: every node of the detached sub-tree is
/// flagged stray before its lock is released.
#[verus_spec(
    with Tracked(cur_own): Tracked<&mut EntryOwner<'a, C>>,
        Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'a, C>>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
pub fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
    rcu_guard: &'a A,
    sub_tree: PPtr<PageTableGuard<'a, C>>,
) -> (num_frames: usize)
    requires
        config_is_x86_64::<C>(),
        old(cur_own).inv(),
        old(cur_own).guard_perm@.pptr() == sub_tree,
        1 <= old(cur_own).level() <= 4,
        old(cur_own).in_region(*old(regions)),
        old(regions).inv(),
        owners_wf(*old(owners), *old(regions)),
    ensures
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == sub_tree,
        cur_own.slot_perm == old(cur_own).slot_perm,
        cur_own.level() == old(cur_own).level(),
        cur_own.is_stray(),
        cur_own.in_region(*regions),
        num_frames <= max_frames(old(cur_own).level()),
        regions.inv(),
        regions.slot_owners == old(regions).slot_owners,
        owners_wf(*owners, *regions),
    decreases old(cur_own).level(),
{
    proof {
        lemma_config_is_x86_64::<C>();
        cur_own.lemma_in_region_relates(*regions);
    }

    let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
    let sub_tree_val = sub_tree.borrow(Tracked(cur_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
    let stray_cell = sub_tree_val.stray_mut();
    let _was_stray = stray_cell.replace(
        Tracked(cur_own.node_own.meta_own.stray.borrow_mut()),
        true,
    );
    assert(cur_own.level() == old(cur_own).level());
    assert(cur_own.inv());

    #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
    let level = sub_tree_val.level();
    if level == 1 {
        #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
        let nr_children = sub_tree_val.nr_children();
        // Dropping the guard releases the lock.
        #[verus_spec(with Tracked(&*cur_own))]
        PageTableGuard::<'a, C>::unlock(sub_tree);
        proof {
            lemma_max_frames_bounded(1);
        }
        return nr_children as usize;
    }
    let mut num_frames: usize = 0;

    let end = nr_subpage_per_huge::<C>();
    let mut i: usize = 0;
    while i < end
        invariant
            config_is_x86_64::<C>(),
            i <= end,
            end == 512,
            1 < level <= 4,
            level == cur_own.level(),
            cur_own.level() == old(cur_own).level(),
            cur_own.slot_perm == old(cur_own).slot_perm,
            cur_own.inv(),
            cur_own.guard_perm@.pptr() == sub_tree,
            cur_own.is_stray(),
            cur_own.in_region(*old(regions)),
            num_frames <= i * max_frames((level - 1) as PagingLevel),
            regions.inv(),
            regions.slot_owners == old(regions).slot_owners,
            owners_wf(*owners, *regions),
        decreases end - i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
            cur_own.lemma_in_region_relates(*regions);
        }
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
        #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'a, C>::entry(sub_tree, i);

        let ghost r0 = *regions;
        proof {
            axiom_pte_paddr_wf(child.pte);
            axiom_node_handle_raw(*regions, child.pte.paddr());
        }
        #[verus_spec(with Tracked(&*cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        proof {
            lemma_owners_wf_same_slot_owners(*owners, r0, *regions);
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                proof {
                    axiom_pte_child_owned(*owners, *cur_own, child_pa);
                    lemma_owner_slot(*owners, *regions, child_pa);
                    lemma_owners_wf_remove(*owners, *regions, child_pa);
                }
                let tracked mut child_own = owners.tracked_remove(child_pa);
                assert(pt.inner.ptr == child_own.slot_perm@.pptr());
                // The node is locked and the new guard is unique.
                #[verus_spec(with Tracked(&child_own))]
                let locked_pt = pt.make_guard_unchecked(rcu_guard);

                // All the nodes in the sub-tree are locked and all guards are forgotten.
                #[verus_spec(with Tracked(&mut child_own), Tracked(owners), Tracked(regions))]
                let frames_below = dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                proof {
                    lemma_max_frames_bounded(level);
                    lemma_mul_inequality(i as int + 1, 512, max_frames((level - 1) as PagingLevel));
                    lemma_mul_is_distributive_add_other_way(
                        max_frames((level - 1) as PagingLevel),
                        i as int,
                        1,
                    );
                }
                num_frames = num_frames + frames_below;
                proof {
                    lemma_owners_wf_insert(*owners, *regions, child_pa, child_own);
                    owners.tracked_insert(child_pa, child_own);
                }
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {
                proof {
                    lemma_max_frames_bounded(level);
                    lemma_mul_inequality(
                        i as int,
                        i as int + 1,
                        max_frames((level - 1) as PagingLevel),
                    );
                }
            },
        }
        i = i + 1;
    }

    // Dropping the guard releases the lock of this node.
    #[verus_spec(with Tracked(&*cur_own))]
    PageTableGuard::<'a, C>::unlock(sub_tree);

    proof {
        lemma_max_frames_bounded(level);
    }
    num_frames
}

/// The range of child indices of the node at `cur_node_level` (starting at
/// `cur_node_va`) that `va_range` touches.
fn dfs_get_idx_range<C: PagingConstsTrait>(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_range: &Range<Vaddr>,
) -> (res: Range<usize>)
    requires
        1 <= cur_node_level <= PagingConsts::NR_LEVELS(),
        // `page_size` is defined in terms of `PagingConsts`, so the node
        // geometry of `C` must agree with it.
        nr_subpage_per_huge::<C>() == nr_subpage_per_huge::<PagingConsts>(),
        va_range.start >= cur_node_va,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_node_level + 1) as PagingLevel),
    ensures
        res.start == (va_range.start - cur_node_va) / page_size(cur_node_level) as int,
        res.end == (va_range.end - cur_node_va + page_size(cur_node_level) - 1) / page_size(
            cur_node_level,
        ) as int,
        res.start < res.end,
        res.end <= nr_subpage_per_huge::<C>(),
{
    proof {
        lemma_page_size_next_level(cur_node_level);
    }
    let size = page_size(cur_node_level);

    let start_idx = (va_range.start - cur_node_va) / size;
    let end_idx = (va_range.end - cur_node_va).div_ceil(size);

    proof {
        let start_within_node = (va_range.start - cur_node_va) as int;
        let end_within_node = (va_range.end - cur_node_va) as int;
        let page_size = size as int;
        let entries_per_page = nr_subpage_per_huge::<PagingConsts>() as int;
        assert(start_within_node / page_size < (end_within_node + page_size - 1) / page_size
            <= entries_per_page) by (nonlinear_arith)
            requires
                0 < page_size,
                0 <= start_within_node < end_within_node <= page_size * entries_per_page,
        ;
    }

    start_idx..end_idx
}

} // verus!
