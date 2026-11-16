// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
use vstd::prelude::*;
use vstd_extra::{array_ptr::*, ghost_tree::*, ownership::*};

use crate::specs::{
    mm::{
        frame::meta_owners::{PtLockCell, PtLockPayload},
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{
            node::{Guards, entry_owners::EntryOwner},
            page_table_coverage_end_spec,
        },
    },
    task::InAtomicMode,
};

use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::frame::{
    MetaSlot,
    meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
};
use crate::mm::page_table::*;
use crate::mm::{
    NR_ENTRIES, NR_LEVELS, PAGE_SIZE, Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr,
    nr_subpage_per_huge, paddr_to_vaddr, page_table::*,
};
use crate::specs::mm::page_table::node::owners::{
    lemma_count_where_raw, lemma_raw_decode, lock_key_wf,
};
use align_ext::AlignExt;
use core::ops::IndexMut;
use core::{marker::PhantomData, ops::Range, sync::atomic::Ordering};
use vstd_extra::drop_tracking::{DropObligation, ManuallyDrop, TrackDrop};
use vstd_extra::resource::flat_tree::{LockedTree, LockedValue, tree_wf, tree_wf_at};

verus! {

broadcast use group_ghost_tree_lemmas;

#[verus_spec(ret =>
    with Tracked(pt_own): Tracked<PageTableOwner<C>>,
        Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards>
    requires
        pt.relates_owner(pt_own, *old(regions)),
        pt_own.0.value().node().relate_guard(root_guard),
        forall|i: int| 0 <= i < NR_ENTRIES ==> pt_own.0.has_child(i),
        va.start < va.end,
        Cursor::<C, A>::cursor_new_success_conditions(*va),
        // No node of the page table has a live guard.
        pt_own.0.subtree_satisfies(pt_own.0.value().path, node_unguarded::<C>(*old(guards))),
        old(guards).held.dom() == Set::<usize>::empty(),
    ensures
            final(regions).slots == old(regions).slots,
            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                old(regions).contains(idx) && old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                    final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
        ret.0.invariants(*ret.1, *final(regions), *final(guards)),
        (*ret.1).in_barrier_va(),
        ret.0.level == ret.0.guard_level,
        ret.0.va < ret.0.barrier_va.end,
        ret.0.va == va.start,
        ret.0.barrier_va == *va,
        (*ret.1).as_page_table_owner() == pt_own,
        (*ret.1).continuations[3].path() == pt_own.0.value().path,
        (forall |i: int| #![trigger old(regions).slot_owners[i]]
            old(regions).contains(i)
            && old(regions).ref_count(i)
                != REF_COUNT_UNUSED
            ==> old(regions).ref_count(i) + 1
                < REF_COUNT_MAX)
        ==>
        (forall |i: int| #![trigger final(regions).slot_owners[i]]
            final(regions).contains(i)
            && final(regions).ref_count(i)
                != REF_COUNT_UNUSED
            ==> final(regions).ref_count(i) + 1
                < REF_COUNT_MAX),
        // Locking only allocates page-table nodes from UNUSED slots, so any
        // slot that was already in use keeps its paths_in_pt intact.
        forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).contains(idx) && old(regions).ref_count(idx)
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        forall|idx: int| #![trigger final(regions).slot_owners[idx]]
            old(regions).contains(idx)
            && old(regions).ref_count(idx)
                != REF_COUNT_UNUSED
            ==> final(regions).ref_count(idx)
                    == old(regions).ref_count(idx)
                && final(regions).slot_owners[idx].usage
                    == old(regions).slot_owners[idx].usage,
        forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
            final(regions).ref_count(idx)
                >= REF_COUNT_MAX
            ==> old(regions).ref_count(idx)
                    == final(regions).ref_count(idx),
        forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
            old(regions).ref_count(idx)
                >= REF_COUNT_MAX
            ==> final(regions).ref_count(idx)
                    == old(regions).ref_count(idx),
        // Frames that were item_not_mapped before remain so after locking.
        forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
            CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
            CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
)]
#[verifier::spinoff_prover]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
pub fn lock_range<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &'rcu PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> (Cursor<'rcu, C, A>, Tracked<CursorOwner<'rcu, C>>) {
    proof {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(va.start, C::NR_LEVELS());
        assert forall|i: int| 0 <= i < NR_ENTRIES implies (
        #[trigger] pt_own.0.children()[i]) is Some by {
            assert(pt_own.0.has_child(i));
        };
    }

    let tracked mut cursor_own: CursorOwner<'rcu, C> = CursorOwner::tracked_new(
        pt_own.0,
        *va,
        root_guard,
    );

    // Retry if the candidate subtree became stray before we acquired its lock.
    let mut subtree_root = None;
    #[verus_spec(
        invariant
            cursor_own.va == va.start,
            cursor_own.barrier_va == *va,
            regions.slots == old(regions).slots,
            forall|idx: int| #![trigger regions.slot_owners[idx]]
                old(regions).contains(idx) && old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                    regions.slot_owners[idx] == old(regions).slot_owners[idx],
            forall|idx: int| #![trigger regions.slot_owners[idx].ref_count()]
                regions.ref_count(idx) >= REF_COUNT_MAX ==>
                    old(regions).ref_count(idx) == regions.ref_count(idx),
            forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
                old(regions).ref_count(idx) >= REF_COUNT_MAX ==>
                    regions.ref_count(idx) == old(regions).ref_count(idx),
            forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
                CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
                    CursorMut::<C, A>::item_not_mapped(item, *regions),
            subtree_root is None ==> {
                &&& *regions == *old(regions)
                &&& cursor_own.level == NR_LEVELS
                &&& cursor_own.continuations.dom().contains(NR_LEVELS - 1)
                &&& cursor_own.continuations[NR_LEVELS - 1].all_some()
                &&& cursor_own.continuations[NR_LEVELS - 1].level() == NR_LEVELS
                &&& cursor_own.continuations[NR_LEVELS - 1].as_subtree() == pt_own.0
                &&& cursor_own.continuations[NR_LEVELS - 1].path() == pt_own.0.value().path
                &&& *guards == *old(guards)
                &&& cursor_own.cells == Map::<usize, PtLockCell>::empty()
            },
            subtree_root is Some ==> {
                &&& va.end - va.start <= page_size::<C>((cursor_own.level + 1) as PagingLevel)
                &&& nat_align_down(va.start as nat, page_size::<C>((cursor_own.level + 1) as PagingLevel) as nat)
                    + page_size::<C>((cursor_own.level + 1) as PagingLevel) >= va.end
                &&& regions.inv()
                &&& 1 <= cursor_own.level <= NR_LEVELS
                &&& cursor_own.continuations.dom().contains(cursor_own.level - 1)
                &&& cursor_own.continuations[cursor_own.level - 1].inv()
                &&& cursor_own.continuations[cursor_own.level - 1].level() == cursor_own.level
                &&& (C::HIGHEST_TRANSLATION_LEVEL() < C::NR_LEVELS()
                    && page_table_coverage_end_spec::<C>()
                        - page_size::<C>(C::NR_LEVELS()) <= va.start
                    && va.end < page_table_coverage_end_spec::<C>())
                    ==> cursor_own.level < C::NR_LEVELS()
                &&& cursor_own.continuations[cursor_own.level - 1].guard == subtree_root->0
                &&& cursor_own.continuations[cursor_own.level - 1].entry_own.is_node()
                &&& cursor_own.continuations[cursor_own.level - 1].entry_own.inv()
                &&& cursor_own.continuations[cursor_own.level - 1].entry_own.node().relate_guard(
                    cursor_own.continuations[cursor_own.level - 1].guard,
                )
                &&& cursor_own.continuations[cursor_own.level - 1].entry_own.metaregion_sound(
                    *regions,
                )
                &&& guards.lock_held(
                    cursor_own.continuations[cursor_own.level - 1]
                        .entry_own.node().slot_vaddr(),
                )
                &&& guards.cells_wf(cursor_own.cells)
                &&& guards.held.dom() == set![
                    cursor_own.continuations[cursor_own.level - 1]
                        .entry_own.node().slot_vaddr()]
                &&& locked_subtree_ready(
                    cursor_own.continuations[cursor_own.level - 1],
                    *va,
                    *regions,
                    *guards,
                )
            },
    )]
    while subtree_root.is_none() {
        #[verus_spec(with Tracked(&mut cursor_own), Tracked(regions), Tracked(guards))]
        let candidate = try_traverse_and_lock_subtree_root(pt, guard, va);
        if let Some(candidate_root) = candidate {
            subtree_root = Some(candidate_root);
        }
    }
    let mut subtree_root = subtree_root.unwrap();

    // Once we have locked the sub-tree that is not stray, we won't read any
    // stray nodes in the following traversal since we must lock before reading.
    let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
    let ghost cont_slot_idx = cont.entry_own.tracked_borrow_node().slot_index;
    proof {
        assert(cont.entry_own.metaregion_sound(*regions));
        assert(regions.contains(cont_slot_idx));
    }
    let tracked cont_node_owner = cont.entry_own.tracked_borrow_node();
    #[verus_spec(with Tracked(cont_node_owner))]
    let guard_level = subtree_root.level();
    proof {
        cursor_own.guard_level = guard_level;
    }
    proof {
        let top = C::NR_LEVELS();
        let body_end = page_table_coverage_end_spec::<C>();
        if va.end + page_size::<C>(top) <= body_end {
            lemma_page_size_monotone::<C>(guard_level, top);
        } else {
            lemma_page_size_is_pow2_pte_index_bit_offset::<C>((top - 1) as PagingLevel);
            assert(va.end < body_end);
            assert(guard_level < top);
            lemma_page_size_monotone::<C>(guard_level, (top - 1) as PagingLevel);
        }
        assert(va.end + page_size::<C>(guard_level) <= body_end);
    }
    let cur_node_va = va.start.align_down(page_size::<C>(guard_level + 1));
    proof {
        cursor_own.prefix = cur_node_va;
    }

    let ghost cont0 = cont;
    let tracked mut locked_subtree = OwnerSubtree::<C>::tracked_new(
        cont.entry_own,
        cont.tree_level,
        cont.children,
    );
    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        assert(locked_subtree == cont0.as_subtree());
        cont0.as_page_table_owner_pt_inv();
        assert(1 <= guard_level <= NR_LEVELS);
        assert(cur_node_va <= va.start);
        assert(va.end <= cur_node_va + page_size::<PagingConsts>((guard_level + 1) as PagingLevel));
        assert(cur_node_va % page_size::<PagingConsts>((guard_level + 1) as PagingLevel) == 0);
        assert(va.end + page_size::<PagingConsts>(guard_level) <= usize::MAX + 1) by {
            crate::specs::arch::lemma_arch_specific_consts_properties::<C>();
            crate::specs::mm::page_table::vaddr_range_proofs::lemma_leading_bits_properties::<C>();
            lemma_page_size_is_pow2_pte_index_bit_offset::<C>((C::NR_LEVELS() + 1) as PagingLevel);
            lemma_page_size_is_pow2_pte_index_bit_offset::<C>(guard_level);
            lemma_page_size_spec_values();
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma2_to64_rest();
            assert(page_size::<C>(guard_level) == page_size::<PagingConsts>(guard_level));
            assert(page_table_coverage_end_spec::<C>() <= usize::MAX + 1);
        }
        assert(dfs_range_ok(guard_level, cur_node_va, *va));
    }
    proof {
        // The root's cell, which `try_traverse_and_lock_subtree_root` put in
        // the cursor, agrees with the root.
        let tracked node = locked_subtree.tracked_borrow_value().tracked_borrow_node();
        node.lemma_held_cell(*guards, cursor_own.cells);
        node.tracked_lemma_holds(cursor_own.cells.tracked_borrow(node.slot_vaddr()));
    }
    #[verus_spec(with Tracked(&locked_subtree), Tracked(&mut cursor_own.cells), Tracked(guards), Tracked(regions))]
    dfs_acquire_lock(guard, &mut subtree_root, cur_node_va, va.clone());

    proof {
        let tracked (entry_own, children) = locked_subtree.tracked_into_parts();
        cont.entry_own = entry_own;
        cont.children = children;
        cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
    }

    let mut path = [None, None, None, None];
    path[guard_level as usize - 1] = Some(subtree_root);

    let res = (
        Cursor::<'rcu, C, A> {
            path,
            rcu_guard: guard,
            level: guard_level,
            guard_level,
            va: va.start,
            barrier_va: va.clone(),
            _phantom: PhantomData,
        },
        Tracked(cursor_own),
    );

    // TODO: the details of the locking mechanism being admitted here
    // are superseded by the CortenMM version. They should be merged, first
    // at the spec level, then the code.
    proof {
        assert(res.1.va == res.0.va);
        assert(res.1.barrier_va == res.0.barrier_va);
        assert(res.1.in_barrier_va());
        assert(res.0.inv());
        assert(res.1.level == res.0.level);
        assert(res.1.locked_range().start <= res.0.barrier_va.start);
        assert(res.0.barrier_va.end <= res.1.locked_range().end);
        assume(res.0.invariants(*res.1, *regions, *guards) && res.0.level == res.0.guard_level
            && res.0.va < res.0.barrier_va.end && (*res.1).as_page_table_owner() == pt_own && (
        *res.1).continuations[3].path() == pt_own.0.value().path);
        assume((forall|i: int|
            #![trigger old(regions).slot_owners[i]]
            old(regions).contains(i) && old(regions).ref_count(i) != REF_COUNT_UNUSED ==> old(
                regions,
            ).ref_count(i) + 1 < REF_COUNT_MAX) ==> (forall|i: int|
            #![trigger regions.slot_owners[i]]
            regions.contains(i) && regions.ref_count(i) != REF_COUNT_UNUSED ==> regions.ref_count(i)
                + 1 < REF_COUNT_MAX));
    }
    res
}

#[verifier::external_body]
pub fn unlock_range<C: PageTableConfig, A: InAtomicMode>(cursor: &mut Cursor<'_, C, A>) {
    unimplemented!()/*    let end = cursor.guard_level as usize - 1;
    for i in (0..end) {
        if let Some(guard) = cursor.path[end - i].take() {
            let _ = ManuallyDrop::new(guard);
        }
    }
    let guard_node = cursor.path[cursor.guard_level as usize - 1].take().unwrap();
    let cur_node_va = cursor.barrier_va.start.align_down(page_size(cursor.guard_level + 1));

    // SAFETY: A cursor maintains that its corresponding sub-tree is locked.
    dfs_release_lock(
        cursor.rcu_guard,
        guard_node,
        cur_node_va,
        cursor.barrier_va.clone(),
    );*/

}

/// What [`try_traverse_and_lock_subtree_root`] guarantees about the subtree
/// it locked, beyond the continuation invariant: the facts
/// [`dfs_acquire_lock`] needs.
pub open spec fn locked_subtree_ready<'rcu, C: PageTableConfig>(
    cont: CursorContinuation<'rcu, C>,
    va: Range<Vaddr>,
    regions: MetaRegionOwners,
    guards: Guards,
) -> bool {
    let t = cont.as_subtree();
    let level = cont.entry_own.node().level();
    let ps_up = page_size::<PagingConsts>((level + 1) as PagingLevel);
    let node_va = nat_align_down(va.start as nat, ps_up as nat) as Vaddr;
    &&& cont.all_some()
    // The root's lock cell is held: it was just locked.
    &&& cont.entry_own.node().held_in(guards)
    &&& PageTableOwner(t).metaregion_sound(regions)
    &&& children_unguarded(t, guards)
    &&& 1 <= level <= NR_LEVELS
    // The locked node covers the range.
    &&& va.end <= node_va
        + ps_up
    // The range stays clear of borrowed (shared) entries.
    &&& forall|i: int|
        0 <= i < NR_ENTRIES ==> !(#[trigger] t.child(i)).value().is_borrowed() || !(idx_range_spec(
            level,
            node_va,
            va.start,
            va.end,
        ).0 <= i < idx_range_spec(level, node_va, va.start, va.end).1)
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
#[verus_spec(r =>
    with Tracked(cursor_own): Tracked<&mut CursorOwner<'rcu, C>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards>
    requires
        old(cursor_own).level == NR_LEVELS,
        old(cursor_own).continuations.dom().contains(NR_LEVELS - 1),
        old(cursor_own).continuations[NR_LEVELS - 1].all_some(),
        old(cursor_own).continuations[NR_LEVELS - 1].level() == NR_LEVELS,
        old(cursor_own).va == va.start,
        old(cursor_own).barrier_va == *va,
        Cursor::<C, A>::cursor_new_success_conditions(*va),
        // No node of the page table has a live guard.
        old(cursor_own).continuations[NR_LEVELS - 1].as_subtree().subtree_satisfies(
            old(cursor_own).continuations[NR_LEVELS - 1].path(),
            node_unguarded::<C>(*old(guards)),
        ),
        old(guards).held.dom() == Set::<usize>::empty(),
        old(cursor_own).cells == Map::<usize, PtLockCell>::empty(),
    ensures
            final(regions).slots == old(regions).slots,
            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                old(regions).contains(idx) && old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                    final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
        // The subtree root's lock cell is the only one held, by the cursor.
        r is Some ==> final(guards).cells_wf(final(cursor_own).cells),
        r is Some ==> final(guards).held.dom() == set![
            final(cursor_own).continuations[final(cursor_own).level - 1]
                .entry_own.node().slot_vaddr()],
        r is None ==> {
            &&& *final(cursor_own) == *old(cursor_own)
            &&& *final(regions) == *old(regions)
            &&& *final(guards) == *old(guards)
        },
        r is Some ==> {
            &&& va.end - va.start <= page_size::<C>((final(cursor_own).level + 1) as PagingLevel)
            &&& nat_align_down(va.start as nat, page_size::<C>((final(cursor_own).level + 1) as PagingLevel) as nat)
                + page_size::<C>((final(cursor_own).level + 1) as PagingLevel) >= va.end
            &&& final(cursor_own).va == old(cursor_own).va
            &&& final(cursor_own).barrier_va == old(cursor_own).barrier_va
            &&& final(cursor_own).prefix == old(cursor_own).prefix
            &&& final(cursor_own).view_mappings() == old(cursor_own).view_mappings()
            &&& final(cursor_own).popped_too_high == false
            &&& 1 <= final(cursor_own).level <= NR_LEVELS
            &&& final(cursor_own).continuations.dom().contains(final(cursor_own).level - 1)
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].inv()
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].level() == final(cursor_own).level
            // Above the highest leaf level, a single-slot request must descend.
            &&& (C::HIGHEST_TRANSLATION_LEVEL() < C::NR_LEVELS()
                && page_table_coverage_end_spec::<C>()
                    - page_size::<C>(C::NR_LEVELS()) <= va.start
                && va.end < page_table_coverage_end_spec::<C>())
                ==> final(cursor_own).level < C::NR_LEVELS()
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].guard == r->0
        },
        // The subtree root's entry_own is a valid node with matching guard.
        r is Some ==> {
            let cont = final(cursor_own).continuations[final(cursor_own).level - 1];
            &&& cont.entry_own.is_node()
            &&& cont.entry_own.inv()
            &&& cont.entry_own.node().relate_guard(cont.guard)
            &&& cont.entry_own.metaregion_sound(*final(regions))
        },
        // The subtree root is lock_held in guards.
        r is Some ==> final(guards).lock_held(
            final(cursor_own).continuations[final(cursor_own).level - 1]
                .entry_own.node().slot_vaddr()),
        r is Some ==> locked_subtree_ready(
            final(cursor_own).continuations[final(cursor_own).level - 1],
            *va,
            *final(regions),
            *final(guards),
        ),
        // regions invariant preserved
        final(regions).inv(),
        // Locking only allocates fresh page-table nodes from UNUSED slots;
        // it does not mutate any slot that was already in use.
        forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).contains(idx) && old(regions).ref_count(idx)
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        // For *in-use* slots (non-UNUSED refcount), the refcount value and
        // usage are exactly preserved — locking only allocates fresh PT
        // nodes from UNUSED slots; it never mutates a slot already in use.
        forall|idx: int| #![trigger final(regions).slot_owners[idx]]
            old(regions).contains(idx)
            && old(regions).ref_count(idx)
                != REF_COUNT_UNUSED
            ==> final(regions).ref_count(idx)
                    == old(regions).ref_count(idx)
                && final(regions).slot_owners[idx].usage
                    == old(regions).slot_owners[idx].usage,
        // Saturated-slot bridge (bidirectional): a slot is at
        // `>= REF_COUNT_MAX` before iff after, with the same value.
        // Fresh PT-node allocations start at rc=1 (well below
        // `REF_COUNT_MAX = i64::MAX as u64`); locking doesn't touch
        // already-saturated slots. Used by `KVirtArea::query` to bridge
        // the inner `Cursor::query`'s per-specific-slot saturation
        // condition back to the caller's `*old(regions)` snapshot.
        forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
            final(regions).ref_count(idx)
                >= REF_COUNT_MAX
            ==> old(regions).ref_count(idx)
                    == final(regions).ref_count(idx),
        forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
            old(regions).ref_count(idx)
                >= REF_COUNT_MAX
            ==> final(regions).ref_count(idx)
                    == old(regions).ref_count(idx),
        // Therefore any frame that was `item_not_mapped` (its paths_in_pt was
        // empty, hence ref_count` might be UNUSED-or-non-UNUSED) stays so:
        // the paddr range's slots either had non-UNUSED ref_count (preserved
        // per above) or UNUSED ref_count (and freshly-allocated PT nodes go
        // into OTHER slot indices, so frame paddrs' paths_in_pt stays empty).
        forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
            CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
            CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
)]
#[verifier::external_body]
fn try_traverse_and_lock_subtree_root<'rcu, C: PageTableConfig, A: InAtomicMode>(
    pt: &PageTable<C>,
    guard: &'rcu A,
    va: &Range<Vaddr>,
) -> Option<PageTableGuard<'rcu, C>> {
    let mut cur_node_guard: Option<PageTableGuard<'rcu, C>> = None;

    let mut cur_pt_addr = pt.root.start_paddr();

    for cur_level in (1..=C::NR_LEVELS()).rev() {
        let start_idx = pte_index::<C>(va.start, cur_level);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, cur_level);
            cur_level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            break;
        }
        let cur_pt_ptr = ArrayPtr::<C::E, NR_ENTRIES>::from_addr(paddr_to_vaddr(cur_pt_addr));
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = unsafe { load_pte(cur_pt_ptr.add(start_idx), Ordering::Acquire) };

        if cur_pte.is_present() {
            if cur_pte.is_last(cur_level) {
                break;
            }
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            proof {
                let ghost next_idx = pte_index::<C>(va.start, (cur_level - 1) as PagingLevel);
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
            continue;
        }
        // In case the child is absent, we should lock and allocate a new page table node.

        let mut pt_guard = if let Some(pt_guard) = cur_node_guard.take() {
            pt_guard
        } else {
            // SAFETY: The node must be alive for at least `'rcu` since the
            // address is read from the page table node.
            let tracked cont = cursor_own.continuations.tracked_borrow(cursor_own.level - 1);
            let tracked node_owner = cont.entry_own.tracked_borrow_node();
            let tracked slot_perm = *regions.slots.tracked_borrow(node_owner.slot_index);
            let node_ref = unsafe {
                #[verus_spec(with Tracked(slot_perm), Tracked(&node_owner.frame_permission))]
                PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr)
            };
            node_ref.lock(guard)
        };

        let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
        let tracked node_owner = cont.entry_own.tracked_borrow_node();
        #[verus_spec(with
            Tracked(node_owner.tracked_borrow_metadata_perm()),
            Tracked(&()),
            Ghost(node_owner.meta_value().stray.id())
        )]
        let stray = pt_guard.stray_mut();
        let is_stray = *(stray.borrow(
            Tracked(
                &cursor_own.cells.tracked_borrow(
                    cont.entry_own.node().slot_vaddr(),
                ).tracked_borrow_value().meta.stray,
            ),
        ));

        proof {
            cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
        }

        if is_stray {
            return None;
        }
        let mut cur_entry = pt_guard.entry(start_idx);
        if cur_entry.is_none() {
            let allocated_guard = cur_entry.alloc_if_none(guard).unwrap();
            cur_pt_addr = allocated_guard.start_paddr();
            cur_node_guard = Some(allocated_guard);
            proof {
                let ghost next_idx = pte_index::<C>(va.start, (cur_level - 1) as PagingLevel);
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
        } else if cur_entry.is_node() {
            let opt_pt = match cur_entry.to_ref() {
                ChildRef::PageTable(pt) => Some(pt),
                _ => None,
            };
            let pt = opt_pt.unwrap();

            cur_pt_addr = pt.start_paddr();
            cur_node_guard = None;
            proof {
                let ghost next_idx = pte_index::<C>(va.start, (cur_level - 1) as PagingLevel);
                proof_decl! {
                    let tracked mut new_guard: PageTableGuard<'rcu, C>;
                }
                let tracked mut cont = cursor_own.continuations.tracked_remove(
                    cursor_own.level - 1,
                );
                let tracked child_cont = cont.tracked_make_cont(next_idx, new_guard);
                cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
                cursor_own.continuations.tracked_insert(cursor_own.level - 2, child_cont);
                cursor_own.level = (cursor_own.level - 1) as PagingLevel;
            }
        } else {
            break;
        }
    }

    let mut pt_guard = if let Some(pt_guard) = cur_node_guard {
        pt_guard
    } else {
        // SAFETY: The node must be alive for at least `'rcu` since the
        // address is read from the page table node.
        let tracked cont = cursor_own.continuations.tracked_borrow(cursor_own.level - 1);
        let tracked node_owner = cont.entry_own.tracked_borrow_node();
        let tracked slot_perm = *regions.slots.tracked_borrow(node_owner.slot_index);
        let node_ref = unsafe {
            #[verus_spec(with Tracked(slot_perm), Tracked(&node_owner.frame_permission))]
            PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr)
        };
        node_ref.lock(guard)
    };

    let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
    let tracked node_owner = cont.entry_own.tracked_borrow_node();
    #[verus_spec(with
        Tracked(node_owner.tracked_borrow_metadata_perm()),
        Tracked(&()),
        Ghost(node_owner.meta_value().stray.id())
    )]
    let stray = pt_guard.stray_mut();
    let is_stray = *(stray.borrow(
        Tracked(
            &cursor_own.cells.tracked_borrow(
                cont.entry_own.node().slot_vaddr(),
            ).tracked_borrow_value().meta.stray,
        ),
    ));

    proof {
        cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
    }

    if is_stray {
        return None;
    }
    Some(pt_guard)
}

/// The range conditions under which `dfs_acquire_lock` visits a node at
/// `level` covering `[node_va, node_va + page_size::<PagingConsts>(level + 1))`.
pub open spec fn dfs_range_ok(level: PagingLevel, node_va: Vaddr, va_range: Range<Vaddr>) -> bool {
    &&& 1 <= level <= NR_LEVELS
    &&& node_va <= va_range.start
    &&& va_range.start < va_range.end
    &&& va_range.end <= node_va + page_size::<PagingConsts>((level + 1) as PagingLevel)
    &&& node_va % page_size::<PagingConsts>((level + 1) as PagingLevel)
        == 0
    // The node's children can be addressed without overflow: `va_range.end` may
    // be the end of the address space, but no child starts at or after it.
    &&& va_range.end + page_size::<PagingConsts>(level) <= usize::MAX + 1
}

/// The node's lock cell is in `cells`, agrees with the node
/// ([`NodeOwner::holds`]), and counts the node's children
/// ([`NodeOwner::count_consistent`]): whoever holds `cells` has locked the
/// node, and can unlock it.
pub open spec fn node_cell_ok<C: PageTableConfig>(
    node: NodeOwner<C>,
    cells: Map<usize, PtLockCell>,
) -> bool {
    &&& cells.contains_key(node.slot_vaddr())
    &&& node.holds(cells[node.slot_vaddr()])
    &&& node.count_consistent(cells[node.slot_vaddr()])
}

/// `cells1` keeps every cell of `cells0`.
pub open spec fn cells_extend(
    cells0: Map<usize, PtLockCell>,
    cells1: Map<usize, PtLockCell>,
) -> bool {
    forall|a: usize| #[trigger]
        cells0.contains_key(a) ==> cells1.contains_key(a) && cells1[a] == cells0[a]
}

/// The page-table node whose metadata slot is at `a` is at or below `prefix`
/// in the page table: every path its slot records extends `prefix`. A node's
/// slot records exactly the node's own path (`metaregion_sound`), so nodes in
/// disjoint subtrees have different addresses.
pub open spec fn addr_under<C: PageTableConfig>(
    regions: MetaRegionOwners,
    a: usize,
    prefix: TreePath<NR_ENTRIES>,
) -> bool {
    forall|p: TreePath<NR_ENTRIES>| #[trigger]
        regions.slot_owners[frame_to_index(meta_to_frame(a))].paths_in_pt.contains(p)
            ==> PageTableOwner::<C>::is_prefix_of(prefix, p)
}

/// A path that does not extend `prefix`, and is at least as long, has no
/// descendant that does.
proof fn lemma_not_prefix_push_tail<C: PageTableConfig>(
    prefix: TreePath<NR_ENTRIES>,
    path: TreePath<NR_ENTRIES>,
    i: int,
)
    requires
        path.inv(),
        0 <= i < NR_ENTRIES,
        prefix.len() <= path.len(),
        !PageTableOwner::<C>::is_prefix_of(prefix, path),
    ensures
        prefix.len() <= path.push_tail(i).len(),
        !PageTableOwner::<C>::is_prefix_of(prefix, path.push_tail(i)),
{
    path.lemma_push_tail_len(i);
    if PageTableOwner::<C>::is_prefix_of(prefix, path.push_tail(i)) {
        assert forall|k: int| 0 <= k < prefix.len() implies prefix[k] == path[k] by {
            path.lemma_push_tail_index(i);
            assert(prefix[k] == path.push_tail(i)[k]);
        }
    }
}

/// In a sound, path-correct subtree at `path`, a node held in `g1` but not in
/// `g0` would be below `prefix`; if no position in the subtree is, its nodes
/// stay unguarded.
proof fn lemma_unguarded_after<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    g0: Guards,
    g1: Guards,
    regions: MetaRegionOwners,
    prefix: TreePath<NR_ENTRIES>,
)
    requires
        t.inv(),
        path.inv(),
        path.len() == t.level(),
        t.subtree_satisfies(path, node_unguarded::<C>(g0)),
        t.subtree_satisfies(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        t.subtree_satisfies(path, PageTableOwner::<C>::path_correct_pred()),
        g1.guards == g0.guards,
        forall|a: usize| #[trigger]
            g1.held.contains_key(a) ==> g0.held.contains_key(a) || addr_under::<C>(
                regions,
                a,
                prefix,
            ),
        prefix.len() <= path.len(),
        !PageTableOwner::<C>::is_prefix_of(prefix, path),
    ensures
        t.subtree_satisfies(path, node_unguarded::<C>(g1)),
    decreases INC_LEVELS - t.level(),
{
    let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let f_path = PageTableOwner::<C>::path_correct_pred();
    let e = t.value();
    assert(f_sound(e, path));
    assert(f_path(e, path));
    if e.is_node() && g1.held.contains_key(e.node().slot_vaddr()) {
        let idx = frame_to_index(e.meta_slot_paddr()->0);
        assert(e.metaregion_sound(regions));
        assert(regions.slot_owners[idx].paths_in_pt.contains(e.path));
    }
    if t.level() < INC_LEVELS - 1 {
        assert forall|i: int|
            0 <= i < t.children().len() && (
            #[trigger] t.children()[i]) is Some implies t.children()[i].unwrap().subtree_satisfies(
            path.push_tail(i),
            node_unguarded::<C>(g1),
        ) by {
            t.lemma_subtree_satisfies_unroll_once(path, node_unguarded::<C>(g0), i);
            t.lemma_subtree_satisfies_unroll_once(path, f_sound, i);
            t.lemma_subtree_satisfies_unroll_once(path, f_path, i);
            lemma_not_prefix_push_tail::<C>(prefix, path, i);
            path.lemma_push_tail_preserves_inv(i);
            lemma_unguarded_after(t.child(i), path.push_tail(i), g0, g1, regions, prefix);
        };
    }
}

/// A node is not at or below `prefix` (as its metadata slot records).
pub open spec fn not_under_pred<C: PageTableConfig>(
    regions: MetaRegionOwners,
    prefix: TreePath<NR_ENTRIES>,
) -> spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool {
    |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
        e.is_node() ==> !addr_under::<C>(regions, e.node().slot_vaddr(), prefix)
}

/// In a sound subtree at `path`, which leaves `prefix` at position `k`, no
/// node is at or below `prefix`.
proof fn lemma_subtree_not_under<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    regions: MetaRegionOwners,
    prefix: TreePath<NR_ENTRIES>,
    k: int,
)
    requires
        PageTableOwner(t).pt_inv(),
        t.value().path == path,
        path.inv(),
        t.subtree_satisfies(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        0 <= k < path.len(),
        k < prefix.len(),
        path[k] != prefix[k],
    ensures
        t.subtree_satisfies(path, not_under_pred::<C>(regions, prefix)),
    decreases INC_LEVELS - t.level(),
{
    let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let e = t.value();
    assert(f_sound(e, path));
    if e.is_node() {
        let idx = frame_to_index(e.meta_slot_paddr()->0);
        assert(e.metaregion_sound(regions));
        assert(regions.slot_owners[idx].paths_in_pt.contains(e.path));
    }
    if t.level() < INC_LEVELS - 1 {
        assert forall|i: int|
            0 <= i < t.children().len() && (
            #[trigger] t.children()[i]) is Some implies t.children()[i].unwrap().subtree_satisfies(
            path.push_tail(i),
            not_under_pred::<C>(regions, prefix),
        ) by {
            if e.is_node() {
                PageTableOwner(t).pt_inv_unroll(i);
                t.lemma_subtree_satisfies_unroll_once(path, f_sound, i);
                path.lemma_push_tail_preserves_inv(i);
                path.lemma_push_tail_len(i);
                path.lemma_push_tail_index(i);
                lemma_subtree_not_under(t.child(i), path.push_tail(i), regions, prefix, k);
            } else {
                PageTableOwner(t).pt_inv_non_node(i);
            }
        };
    }
}

/// The path of the entry the cursor points to extends the path of every
/// continuation, through that continuation's index.
proof fn lemma_cont_path_prefix<'rcu, C: PageTableConfig>(owner: CursorOwner<'rcu, C>, i: int)
    requires
        owner.inv(),
        owner.level - 1 <= i < NR_LEVELS,
    ensures
        PageTableOwner::<C>::is_prefix_of(
            owner.continuations[i].path().push_tail(owner.continuations[i].idx as int),
            owner.continuations[owner.level - 1].path().push_tail(owner.index() as int),
        ),
        owner.continuations[i].path().len() + 1 <= owner.continuations[owner.level
            - 1].path().push_tail(owner.index() as int).len(),
    decreases i - (owner.level - 1),
{
    let prefix = owner.continuations[owner.level - 1].path().push_tail(owner.index() as int);
    owner.lemma_inv_continuation(i);
    owner.continuations[i].path().lemma_push_tail_len(owner.continuations[i].idx as int);
    if i > owner.level - 1 {
        lemma_cont_path_prefix(owner, i - 1);
        owner.lemma_inv_continuation(i - 1);
        let ci = owner.continuations[i];
        let cl = owner.continuations[i - 1];
        // The continuation below is the child at this one's index.
        assert(cl.path() == ci.path().push_tail(ci.idx as int)) by {
            if i == 3 {
            } else if i == 2 {
            } else {
                assert(i == 1);
            }
        }
        let a = ci.path().push_tail(ci.idx as int);
        let b = cl.path().push_tail(cl.idx as int);
        cl.path().lemma_push_tail_len(cl.idx as int);
        assert forall|m: int| 0 <= m < a.len() implies a[m] == prefix[m] by {
            cl.path().lemma_push_tail_index(cl.idx as int);
            assert(a[m] == b[m]);
        }
    }
}

/// Once the cursor's current entry is replaced by a non-node, no node left in
/// the cursor's tree is at or below the current entry's path.
pub proof fn lemma_cursor_nodes_not_under<'rcu, C: PageTableConfig>(
    owner: CursorOwner<'rcu, C>,
    regions: MetaRegionOwners,
)
    requires
        owner.inv(),
        owner.metaregion_sound(regions),
        !owner.cur_entry_owner().is_node(),
    ensures
        forall|i: int|
            #![trigger owner.continuations[i]]
            owner.level - 1 <= i < NR_LEVELS ==> owner.continuations[i].map_children(
                not_under_pred::<C>(
                    regions,
                    owner.continuations[owner.level - 1].path().push_tail(owner.index() as int),
                ),
            ),
        forall|i: int|
            #![trigger owner.continuations[i]]
            owner.level - 1 <= i < NR_LEVELS ==> !addr_under::<C>(
                regions,
                owner.continuations[i].entry_own.node().slot_vaddr(),
                owner.continuations[owner.level - 1].path().push_tail(owner.index() as int),
            ),
{
    let prefix = owner.continuations[owner.level - 1].path().push_tail(owner.index() as int);
    let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let h = not_under_pred::<C>(regions, prefix);
    assert forall|i: int|
        #![trigger owner.continuations[i]]
        owner.level - 1 <= i < NR_LEVELS implies owner.continuations[i].map_children(h) by {
        owner.lemma_inv_continuation(i);
        lemma_cont_path_prefix(owner, i);
        let cont = owner.continuations[i];
        let k = cont.path().len() as int;
        cont.path().lemma_push_tail_len(cont.idx as int);
        cont.path().lemma_push_tail_index(cont.idx as int);
        assert(prefix[k] == cont.idx);
        assert(cont.map_children(f_sound));
        reveal(CursorContinuation::map_children);
        assert forall|j: int|
            #![trigger cont.children[j]]
            0 <= j < cont.children.len()
                && cont.children[j] is Some implies cont.children[j]->0.subtree_satisfies(
            cont.path().push_tail(j),
            h,
        ) by {
            cont.lemma_pt_inv_children_unroll(j);
            cont.lemma_inv_children_rel_unroll(j);
            let child = cont.children[j]->0;
            let pj = cont.path().push_tail(j);
            cont.path().lemma_push_tail_len(j);
            cont.path().lemma_push_tail_index(j);
            assert(cont.entry_own.path.inv());
            cont.path().lemma_push_tail_preserves_inv(j);
            if j == cont.idx {
                // Only the current continuation has a child at its index: the
                // entry the cursor points to, which is not a node.
                assert(i == owner.level - 1);
                assert(!child.value().is_node());
                assert forall|m: int| 0 <= m < NR_ENTRIES implies !child.has_child(m) by {
                    PageTableOwner(child).pt_inv_non_node(m);
                }
            } else {
                lemma_subtree_not_under(child, pj, regions, prefix, k);
            }
        }
    }
    reveal(CursorOwner::path_metaregion_sound);
    assert forall|i: int|
        #![trigger owner.continuations[i]]
        owner.level - 1 <= i < NR_LEVELS implies !addr_under::<C>(
        regions,
        owner.continuations[i].entry_own.node().slot_vaddr(),
        prefix,
    ) by {
        owner.lemma_inv_continuation(i);
        lemma_cont_path_prefix(owner, i);
        let e = owner.continuations[i].entry_own;
        assert(e.metaregion_sound(regions));
        let idx = frame_to_index(e.meta_slot_paddr()->0);
        assert(regions.slot_owners[idx].paths_in_pt.contains(e.path));
    }
}

/// Every page-table node below `t` whose range overlaps `[va_start, va_end)`
/// has its lock cell in `cells` ([`node_cell_ok`]): exactly the nodes
/// `dfs_acquire_lock` locks.
pub open spec fn dfs_locked_below<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 && t.value().is_node() && t.value().node().level() > 1 ==> {
        let ps = page_size::<PagingConsts>(t.value().node().level()) as int;
        forall|i: int|
            #![trigger t.child(i)]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                && t.child(i).value().is_node() ==> {
                let cva = node_va + i * ps;
                &&& node_cell_ok(t.child(i).value().node(), cells)
                &&& dfs_locked_below(
                    t.child(i),
                    cells,
                    cva,
                    if va_start < cva {
                        cva
                    } else {
                        va_start
                    },
                    if va_end < cva + ps {
                        va_end
                    } else {
                        cva + ps
                    },
                    (depth - 1) as nat,
                )
            }
    }
}

/// [`dfs_locked_below`] survives adding cells.
proof fn lemma_dfs_locked_below_extend<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    c0: Map<usize, PtLockCell>,
    c1: Map<usize, PtLockCell>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
)
    requires
        dfs_locked_below(t, c0, node_va, va_start, va_end, depth),
        cells_extend(c0, c1),
    ensures
        dfs_locked_below(t, c1, node_va, va_start, va_end, depth),
    decreases depth,
{
    if depth > 0 && t.value().is_node() && t.value().node().level() > 1 {
        let ps = page_size::<PagingConsts>(t.value().node().level()) as int;
        assert forall|i: int|
            #![trigger t.child(i)]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                && t.child(i).value().is_node() implies {
            let cva = node_va + i * ps;
            &&& node_cell_ok(t.child(i).value().node(), c1)
            &&& dfs_locked_below(
                t.child(i),
                c1,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            )
        } by {
            let cva = node_va + i * ps;
            assert(c0.contains_key(t.child(i).value().node().slot_vaddr()));
            lemma_dfs_locked_below_extend(
                t.child(i),
                c0,
                c1,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            );
        }
    }
}

/// [`dfs_locked_below`] survives changing cells only below `prefix`, in a
/// sound, path-correct subtree that is not below `prefix`.
proof fn lemma_dfs_locked_below_agree<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    c0: Map<usize, PtLockCell>,
    c1: Map<usize, PtLockCell>,
    regions: MetaRegionOwners,
    prefix: TreePath<NR_ENTRIES>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
)
    requires
        PageTableOwner(t).pt_inv(),
        path.inv(),
        path.len() == t.level(),
        dfs_locked_below(t, c0, node_va, va_start, va_end, depth),
        t.subtree_satisfies(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        t.subtree_satisfies(path, PageTableOwner::<C>::path_correct_pred()),
        forall|a: usize| #[trigger]
            c0.contains_key(a) && !addr_under::<C>(regions, a, prefix) ==> c1.contains_key(a)
                && c1[a] == c0[a],
        prefix.len() <= path.len(),
        !PageTableOwner::<C>::is_prefix_of(prefix, path),
    ensures
        dfs_locked_below(t, c1, node_va, va_start, va_end, depth),
    decreases depth,
{
    let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let f_path = PageTableOwner::<C>::path_correct_pred();
    if depth > 0 && t.value().is_node() && t.value().node().level() > 1 {
        let ps = page_size::<PagingConsts>(t.value().node().level()) as int;
        assert forall|i: int|
            #![trigger t.child(i)]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                && t.child(i).value().is_node() implies {
            let cva = node_va + i * ps;
            &&& node_cell_ok(t.child(i).value().node(), c1)
            &&& dfs_locked_below(
                t.child(i),
                c1,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            )
        } by {
            let cva = node_va + i * ps;
            PageTableOwner(t).pt_inv_unroll(i);
            t.lemma_subtree_satisfies_unroll_once(path, f_sound, i);
            t.lemma_subtree_satisfies_unroll_once(path, f_path, i);
            lemma_not_prefix_push_tail::<C>(prefix, path, i);
            path.lemma_push_tail_preserves_inv(i);
            let c = t.child(i);
            assert(f_sound(c.value(), path.push_tail(i)));
            assert(f_path(c.value(), path.push_tail(i)));
            let a = c.value().node().slot_vaddr();
            let idx = frame_to_index(c.value().meta_slot_paddr()->0);
            assert(c.value().metaregion_sound(regions));
            assert(regions.slot_owners[idx].paths_in_pt.contains(c.value().path));
            assert(!addr_under::<C>(regions, a, prefix));
            assert(c0.contains_key(a));
            lemma_dfs_locked_below_agree(
                c,
                path.push_tail(i),
                c0,
                c1,
                regions,
                prefix,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            );
        }
    }
}

/// [`idx_range_spec`]'s casts are exact.
proof fn lemma_idx_range_spec_exact(level: PagingLevel, node_va: Vaddr, va_range: Range<Vaddr>)
    requires
        dfs_range_ok(level, node_va, va_range),
    ensures
        idx_range_spec(level, node_va, va_range.start, va_range.end).0 as int == (va_range.start
            - node_va) / (page_size::<PagingConsts>(level) as int),
        idx_range_spec(level, node_va, va_range.start, va_range.end).1 as int == ceil_div(
            va_range.end - node_va,
            page_size::<PagingConsts>(level) as int,
        ),
{
    use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
    use vstd::arithmetic::div_mod::*;
    lemma_page_size_spec_values();
    let ps = page_size::<PagingConsts>(level) as int;
    let x = va_range.start - node_va;
    let y = va_range.end - node_va + ps - 1;
    lemma_div_is_ordered_by_denominator(x, 1, ps);
    lemma_div_is_ordered_by_denominator(y, 1, ps);
    lemma_div_pos_is_pos(x, ps);
    lemma_div_pos_is_pos(y, ps);
    assert(y / ps <= y / 1);
    assert(y < usize::MAX);
}

/// The child ranges `dfs_acquire_lock` recurses on are well-formed.
proof fn lemma_dfs_child_range(level: PagingLevel, node_va: Vaddr, va_range: Range<Vaddr>, i: int)
    requires
        dfs_range_ok(level, node_va, va_range),
        level > 1,
        (va_range.start - node_va) / (page_size::<PagingConsts>(level) as int) <= i < ceil_div(
            va_range.end - node_va,
            page_size::<PagingConsts>(level) as int,
        ),
        i < NR_ENTRIES,
    ensures
        ({
            let ps = page_size::<PagingConsts>(level) as int;
            let cva = node_va + i * ps;
            let cs = if va_range.start < cva {
                cva
            } else {
                va_range.start as int
            };
            let ce = if va_range.end < cva + ps {
                va_range.end as int
            } else {
                cva + ps
            };
            &&& cva + ps <= usize::MAX
            &&& dfs_range_ok((level - 1) as PagingLevel, cva as Vaddr, (cs as Vaddr)..(ce as Vaddr))
        }),
{
    use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
    use vstd::arithmetic::div_mod::*;
    lemma_page_size_spec_values();
    lemma_page_size_divides::<PagingConsts>(level, (level + 1) as PagingLevel);
    let ps = page_size::<PagingConsts>(level) as int;
    let psl = page_size::<PagingConsts>((level - 1) as PagingLevel) as int;
    let psu = page_size::<PagingConsts>((level + 1) as PagingLevel) as int;
    let v = node_va as int;
    let s = va_range.start as int;
    let e = va_range.end as int;
    let cva = v + i * ps;
    lemma_fundamental_div_mod(s - v, ps);
    lemma_fundamental_div_mod(e - v + ps - 1, ps);
    let q1 = (s - v) / ps;
    let q2 = (e - v + ps - 1) / ps;
    assert(s < cva + ps && cva < e) by (nonlinear_arith)
        requires
            s - v == ps * q1 + (s - v) % ps,
            0 <= (s - v) % ps < ps,
            e - v + ps - 1 == ps * q2 + (e - v + ps - 1) % ps,
            0 <= (e - v + ps - 1) % ps < ps,
            q1 <= i < q2,
            cva == v + i * ps,
            ps > 0,
    ;
    lemma_fundamental_div_mod(v, psu);
    lemma_fundamental_div_mod(psu, ps);
    assert(cva % ps == 0) by {
        let k = v / psu;
        let m = psu / ps;
        assert(cva == (m * k + i) * ps) by (nonlinear_arith)
            requires
                v == psu * k + v % psu,
                v % psu == 0,
                psu == ps * m + psu % ps,
                psu % ps == 0,
                cva == v + i * ps,
        ;
        lemma_mod_multiples_basic(m * k + i, ps);
    }
}

/// Acquires the locks for the given range in the sub-tree rooted at the node.
///
/// `cur_node_va` must be the virtual address of the `cur_node`. The `va_range`
/// must be within the range of the `cur_node`. The range must not be empty.
///
/// The function will forget all the [`PageTableGuard`] objects in the sub-tree.
///
/// # Verified Properties
/// ## Preconditions
/// - `subtree` is the owner of the sub-tree rooted at `cur_node`, sound with
///   respect to `regions`. No node strictly below its root has a live guard,
///   or is held by this thread.
/// - The root is locked: its cell is in `cells` ([`node_cell_ok`]), which are
///   the cells this thread holds ([`Guards::cells_wf`]).
/// - The range is within the node's range (see [`dfs_range_ok`]).
/// ## Postconditions
/// - Every page-table node below the root that overlaps the range has its lock
///   cell in `cells` ([`dfs_locked_below`]); the cells come from the nodes'
///   locks. Together they form a [`flat_tree`] tree, complete over the range
///   ([`dfs_locked_flat`]).
/// - Only cells of nodes in the subtree are added, and they are recorded as
///   held. The child guards are forgotten, so `guards.guards` is unchanged.
/// - The page table tree itself is unchanged: it does not hold the cells.
///
/// [`flat_tree`]: vstd_extra::resource::flat_tree
#[verus_spec(
    with Tracked(subtree): Tracked<&OwnerSubtree<C>>,
        Tracked(cells): Tracked<&mut Map<usize, PtLockCell>>,
        Tracked(guards): Tracked<&mut Guards>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        PageTableOwner(*subtree).pt_inv(),
        PageTableOwner(*subtree).metaregion_sound(*old(regions)),
        subtree.value().is_node(),
        subtree.value().path.len() == subtree.level(),
        node_cell_ok(subtree.value().node(), *old(cells)),
        old(guards).cells_wf(*old(cells)),
        subtree.value().node().relate_guard(*old(cur_node)),
        children_unguarded(*subtree, *old(guards)),
        dfs_range_ok(subtree.value().node().level(), cur_node_va, va_range),
        // Borrowed (shared) entries only occur at the top level, and the range
        // stays clear of them.
        forall|i: int| 0 <= i < NR_ENTRIES ==> !(#[trigger] subtree.child(i)).value().is_borrowed()
            || !(idx_range_spec(subtree.value().node().level(), cur_node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(subtree.value().node().level(), cur_node_va, va_range.start, va_range.end).1),
        old(regions).inv(),
    ensures
        PageTableOwner(*subtree).metaregion_sound(*final(regions)),
        dfs_locked_below(
            *subtree,
            *final(cells),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - subtree.level()) as nat,
        ),
        dfs_locked_flat(*subtree, *final(cells), cur_node_va, va_range),
        cells_extend(*old(cells), *final(cells)),
        forall|a: usize|
            #[trigger] final(cells).contains_key(a) && !old(cells).contains_key(a) ==> addr_under::<C>(
                *old(regions),
                a,
                subtree.value().path,
            ),
        final(guards).cells_wf(*final(cells)),
        final(guards).guards == old(guards).guards,
        *final(cur_node) == *old(cur_node),
        final(regions).inv(),
        final(regions).slot_owners == old(regions).slot_owners,
        final(regions).slots == old(regions).slots,
)]
#[verifier::spinoff_prover]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let ghost root = subtree.value();
    let ghost root_addr = root.node().slot_vaddr();
    proof {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        assert(regions.contains(root.node().slot_index));
        PageTableOwner::<C>::lemma_pt_inv_implies_path_correct(*subtree, root.path);
    }
    let cur_level = {
        let tracked node_owner = subtree.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_owner))]
        cur_node.level()
    };
    if cur_level == 1 {
        proof {
            lemma_dfs_locked_flat(*subtree, *cells, *regions, cur_node_va, va_range);
        }
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let ghost s0 = idx_range.start as int;
    let ghost e0 = idx_range.end as int;
    let ghost ps = page_size::<PagingConsts>(cur_level) as int;
    proof {
        lemma_idx_range_spec_exact(cur_level, cur_node_va, va_range);
    }
    let ghost depth = (INC_LEVELS - subtree.level()) as nat;
    let ghost guards0 = *guards;
    let ghost regions0 = *regions;
    let ghost cells0 = *cells;
    let ghost f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions0);
    let ghost f_path = PageTableOwner::<C>::path_correct_pred();
    for i in idx_range
        invariant
            s0 <= i <= e0 <= NR_ENTRIES,
            cur_level == root.node().level(),
            ps == page_size::<PagingConsts>(cur_level) as int,
            depth == INC_LEVELS - subtree.level(),
            root == subtree.value(),
            root_addr == root.node().slot_vaddr(),
            PageTableOwner(*subtree).pt_inv(),
            PageTableOwner(*subtree).metaregion_sound(*regions),
            subtree.subtree_satisfies(root.path, f_path),
            f_sound == PageTableOwner::<C>::metaregion_sound_pred(regions0),
            f_path == PageTableOwner::<C>::path_correct_pred(),
            *cur_node == *old(cur_node),
            guards.guards == guards0.guards,
            guards0 == *old(guards),
            regions0 == *old(regions),
            cells0 == *old(cells),
            regions.inv(),
            regions.slot_owners == regions0.slot_owners,
            regions.slots == regions0.slots,
            guards.cells_wf(*cells),
            cells_extend(cells0, *cells),
            forall|a: usize| #[trigger]
                cells.contains_key(a) && !cells0.contains_key(a) ==> addr_under::<C>(
                    regions0,
                    a,
                    root.path,
                ),
            node_cell_ok(root.node(), *cells),
            // The children not visited yet are untouched.
            forall|j: int|
                #![trigger subtree.child(j)]
                i <= j < NR_ENTRIES && subtree.has_child(j) ==> subtree.child(j).subtree_satisfies(
                    root.path.push_tail(j),
                    node_unguarded::<C>(*guards),
                ),
            forall|j: int|
                #![trigger subtree.child(j)]
                s0 <= j < i && subtree.child(j).value().is_node() ==> {
                    let cva = cur_node_va + j * ps;
                    &&& node_cell_ok(subtree.child(j).value().node(), *cells)
                    &&& dfs_locked_below(
                        subtree.child(j),
                        *cells,
                        cva,
                        if va_range.start < cva {
                            cva
                        } else {
                            va_range.start as int
                        },
                        if va_range.end < cva + ps {
                            va_range.end as int
                        } else {
                            cva + ps
                        },
                        (depth - 1) as nat,
                    )
                },
    {
        let ghost regions_i = *regions;
        proof {
            PageTableOwner(*subtree).pt_inv_unroll(i as int);
            subtree.lemma_subtree_satisfies_unroll_once(
                root.path,
                PageTableOwner::<C>::metaregion_sound_pred(*regions),
                i as int,
            );
        }
        let ghost child0 = subtree.child(i as int);
        let child = {
            let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
            let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value();
            let tracked parent_cell = cells.tracked_borrow(root_addr);
            #[verus_spec(with Tracked(parent_owner), Tracked(child_owner), Tracked(&*regions),
                Tracked(&parent_cell.tracked_borrow_value().ptes))]
            cur_node.entry(i)
        };
        let child_ref = {
            let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
            let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value();
            #[verus_spec(with Tracked(child_owner), Tracked(parent_owner), Tracked(regions))]
            child.to_ref()
        };
        proof {
            PageTableOwner::<C>::lemma_metaregion_sound_preserved_slot_owners_eq_subtree(
                *subtree,
                root.path,
                regions_i,
                *regions,
            );
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost regions1 = *regions;
                let ghost guards_i = *guards;
                let ghost cells_i = *cells;
                let ghost path_i = root.path.push_tail(i as int);
                let ghost child_addr = child0.value().node().slot_vaddr();
                proof {
                    subtree.lemma_subtree_satisfies_unroll_once(root.path, f_path, i as int);
                    root.path.lemma_push_tail_preserves_inv(i as int);
                    assert(child0.subtree_satisfies(path_i, node_unguarded::<C>(guards_i)));
                    assert(guards_i.unlocked(child_addr));
                    assert(!guards_i.held.contains_key(child_addr));
                    assert(!cells_i.contains_key(child_addr));
                }
                proof_decl! {
                    let tracked lock_cell: PtLockCell;
                    let tracked guard_obl: DropObligation<usize>;
                }
                let mut pt_guard = {
                    let tracked child_owner = subtree.tracked_borrow_child(
                        i as int,
                    ).tracked_borrow_value().tracked_borrow_node();
                    #[verus_spec(with Tracked(child_owner), Tracked(guards) => Tracked(lock_cell))]
                    pt.lock(guard)
                };
                let ghost guards1 = *guards;
                proof {
                    lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                }
                let child_node_va = cur_node_va + i * page_size::<C>(cur_level);
                let child_node_va_end = child_node_va + page_size::<C>(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                proof {
                    guard_obl = pt_guard.tracked_redeem(guards);
                    assert forall|x: usize| #[trigger]
                        guards.guards.contains(x) == guards_i.guards.contains(x) by {
                        if guards_i.lock_held(x) {
                            assert(guards1.lock_held(x));
                        } else {
                            assert(guards_i.unlocked(x));
                        }
                    }
                    assert(guards.guards =~= guards_i.guards);
                    guards_i.lemma_cells_wf_insert(*guards, cells_i, child_addr, lock_cell);
                    cells.tracked_insert(child_addr, lock_cell);
                    // The child's slot records the child's path.
                    assert(f_sound(child0.value(), path_i));
                    assert(child0.value().metaregion_sound(regions0));
                    let idx = frame_to_index(child0.value().meta_slot_paddr()->0);
                    assert(regions0.slot_owners[idx].paths_in_pt == set![path_i]);
                    // No node below the child is held: their slots record longer
                    // paths than the child's.
                    assert forall|j: int|
                        0 <= j < NR_ENTRIES && #[trigger] child0.has_child(j) implies child0.child(
                        j,
                    ).subtree_satisfies(path_i.push_tail(j), node_unguarded::<C>(*guards)) by {
                        child0.lemma_subtree_satisfies_unroll_once(
                            path_i,
                            node_unguarded::<C>(guards_i),
                            j,
                        );
                        child0.lemma_subtree_satisfies_unroll_once(path_i, f_sound, j);
                        child0.lemma_subtree_satisfies_unroll_once(path_i, f_path, j);
                        path_i.lemma_push_tail_preserves_inv(j);
                        path_i.lemma_push_tail_len(j);
                        assert(!PageTableOwner::<C>::is_prefix_of(path_i.push_tail(j), path_i));
                        PageTableOwner::<C>::lemma_neq_old_from_path_disjoint(
                            child0.child(j),
                            path_i.push_tail(j),
                            child0.value(),
                            regions0,
                        );
                        let g_neq = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                            e.meta_slot_paddr_neq(child0.value());
                        child0.child(j).lemma_subtree_satisfies_implies_and(
                            path_i.push_tail(j),
                            node_unguarded::<C>(guards_i),
                            g_neq,
                            node_unguarded::<C>(*guards),
                        );
                    }
                    // Below the top level, no entry is borrowed.
                    assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] child0.child(
                        j,
                    )).value().is_borrowed() by {
                        PageTableOwner(child0).pt_inv_unroll(j);
                    }
                    assert(node_cell_ok(child0.value().node(), *cells));
                    assert(guards.cells_wf(*cells));
                }

                proof {
                    assert(va_start == (if va_range.start < child_node_va {
                        child_node_va
                    } else {
                        va_range.start
                    }));
                    assert(va_end == (if va_range.end < child_node_va_end {
                        va_range.end
                    } else {
                        child_node_va_end
                    }));
                }
                let ghost cells2 = *cells;
                let ghost guards2 = *guards;
                {
                    let tracked c = subtree.tracked_borrow_child(i as int);
                    #[verus_spec(with Tracked(c), Tracked(cells), Tracked(guards), Tracked(regions))]
                    dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
                }
                proof_with!(Tracked(guard_obl));
                let _ = ManuallyDrop::new(pt_guard);
                proof {
                    PageTableOwner::<C>::lemma_metaregion_sound_preserved_slot_owners_eq_subtree(
                        *subtree,
                        root.path,
                        regions1,
                        *regions,
                    );
                    // Every cell added for the child is below the child, and so
                    // below the root.
                    assert forall|a: usize| #[trigger]
                        cells.contains_key(a) && !cells_i.contains_key(a) implies addr_under::<C>(
                        regions0,
                        a,
                        path_i,
                    ) by {
                        if !cells2.contains_key(a) {
                            assert(addr_under::<C>(regions1, a, path_i));
                        } else {
                            assert(a == child_addr);
                        }
                    }
                    assert forall|a: usize| #[trigger]
                        cells.contains_key(a) && !cells0.contains_key(a) implies addr_under::<C>(
                        regions0,
                        a,
                        root.path,
                    ) by {
                        if !cells_i.contains_key(a) {
                            assert forall|p: TreePath<NR_ENTRIES>| #[trigger]
                                regions0.slot_owners[frame_to_index(
                                    meta_to_frame(a),
                                )].paths_in_pt.contains(p) implies PageTableOwner::<
                                C,
                            >::is_prefix_of(root.path, p) by {
                                assert(PageTableOwner::<C>::is_prefix_of(path_i, p));
                                root.path.lemma_push_tail_len(i as int);
                                assert forall|k: int| 0 <= k < root.path.len() implies root.path[k]
                                    == p[k] by {
                                    root.path.lemma_push_tail_index(i as int);
                                    assert(path_i[k] == root.path[k]);
                                }
                            }
                        }
                    }
                    // The children not visited yet are still untouched.
                    assert forall|j: int|
                        #![trigger subtree.child(j)]
                        i + 1 <= j < NR_ENTRIES && subtree.has_child(j) implies subtree.child(
                        j,
                    ).subtree_satisfies(root.path.push_tail(j), node_unguarded::<C>(*guards)) by {
                        subtree.lemma_subtree_satisfies_unroll_once(root.path, f_sound, j);
                        subtree.lemma_subtree_satisfies_unroll_once(root.path, f_path, j);
                        PageTableOwner(*subtree).pt_inv_unroll(j);
                        root.path.lemma_push_tail_preserves_inv(j);
                        root.path.lemma_push_tail_len(i as int);
                        root.path.lemma_push_tail_len(j);
                        assert(!PageTableOwner::<C>::is_prefix_of(path_i, root.path.push_tail(j)))
                            by {
                            root.path.lemma_push_tail_index(i as int);
                            root.path.lemma_push_tail_index(j);
                            assert(path_i[root.path.len() as int] != root.path.push_tail(
                                j,
                            )[root.path.len() as int]);
                        }
                        assert forall|a: usize| #[trigger]
                            guards.held.contains_key(a) implies guards_i.held.contains_key(a)
                            || addr_under::<C>(regions0, a, path_i) by {
                            assert(cells.contains_key(a));
                            if !cells_i.contains_key(a) {
                            } else {
                                assert(guards_i.held.contains_key(a));
                            }
                        }
                        lemma_unguarded_after(
                            subtree.child(j),
                            root.path.push_tail(j),
                            guards_i,
                            *guards,
                            regions0,
                            path_i,
                        );
                    }
                    // The children visited before keep their cells.
                    assert forall|a: usize| #[trigger]
                        cells_i.contains_key(a) implies cells.contains_key(a) && cells[a]
                        == cells_i[a] by {
                        assert(cells2.contains_key(a));
                    }
                    assert(cells_extend(cells_i, *cells));
                    assert forall|j: int|
                        #![trigger subtree.child(j)]
                        s0 <= j < i + 1 && subtree.child(j).value().is_node() implies {
                        let cva = cur_node_va + j * ps;
                        &&& node_cell_ok(subtree.child(j).value().node(), *cells)
                        &&& dfs_locked_below(
                            subtree.child(j),
                            *cells,
                            cva,
                            if va_range.start < cva {
                                cva
                            } else {
                                va_range.start as int
                            },
                            if va_range.end < cva + ps {
                                va_range.end as int
                            } else {
                                cva + ps
                            },
                            (depth - 1) as nat,
                        )
                    } by {
                        let cva = cur_node_va + j * ps;
                        if j != i {
                            assert(cells_i.contains_key(
                                subtree.child(j).value().node().slot_vaddr(),
                            ));
                            lemma_dfs_locked_below_extend(
                                subtree.child(j),
                                cells_i,
                                *cells,
                                cva,
                                if va_range.start < cva {
                                    cva
                                } else {
                                    va_range.start as int
                                },
                                if va_range.end < cva + ps {
                                    va_range.end as int
                                } else {
                                    cva + ps
                                },
                                (depth - 1) as nat,
                            );
                        } else {
                            assert(cells2.contains_key(child_addr));
                        }
                    }
                    assert(cells_extend(cells0, *cells));
                    assert(cells_i.contains_key(root_addr));
                }
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {
                proof {
                    assert(!child0.value().is_node());
                }
            },
        }
    }
    proof {
        lemma_dfs_locked_flat(*subtree, *cells, *regions, cur_node_va, va_range);
    }
}

/// Every page-table node below `t` whose range overlaps `[va_start, va_end)`
/// has no lock cell in `cells`: exactly the nodes `dfs_release_lock` unlocks.
pub open spec fn dfs_unlocked_below<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 && t.value().is_node() && t.value().node().level() > 1 ==> {
        let ps = page_size::<PagingConsts>(t.value().node().level()) as int;
        forall|i: int|
            #![trigger t.child(i)]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                && t.child(i).value().is_node() ==> {
                let cva = node_va + i * ps;
                &&& !cells.contains_key(t.child(i).value().node().slot_vaddr())
                &&& dfs_unlocked_below(
                    t.child(i),
                    cells,
                    cva,
                    if va_start < cva {
                        cva
                    } else {
                        va_start
                    },
                    if va_end < cva + ps {
                        va_end
                    } else {
                        cva + ps
                    },
                    (depth - 1) as nat,
                )
            }
    }
}

/// [`dfs_unlocked_below`] survives removing cells.
proof fn lemma_dfs_unlocked_below_shrink<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    c0: Map<usize, PtLockCell>,
    c1: Map<usize, PtLockCell>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
)
    requires
        dfs_unlocked_below(t, c0, node_va, va_start, va_end, depth),
        forall|a: usize| #[trigger] c1.contains_key(a) ==> c0.contains_key(a),
    ensures
        dfs_unlocked_below(t, c1, node_va, va_start, va_end, depth),
    decreases depth,
{
    if depth > 0 && t.value().is_node() && t.value().node().level() > 1 {
        let ps = page_size::<PagingConsts>(t.value().node().level()) as int;
        assert forall|i: int|
            #![trigger t.child(i)]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                && t.child(i).value().is_node() implies {
            let cva = node_va + i * ps;
            &&& !c1.contains_key(t.child(i).value().node().slot_vaddr())
            &&& dfs_unlocked_below(
                t.child(i),
                c1,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            )
        } by {
            let cva = node_va + i * ps;
            lemma_dfs_unlocked_below_shrink(
                t.child(i),
                c0,
                c1,
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            );
        }
    }
}

/// A subtree of held page table lock cells, as a [`flat_tree`] tree.
///
/// [`flat_tree`]: vstd_extra::resource::flat_tree
pub type PtLockedTree = LockedTree<PtLockPayload, NR_ENTRIES, NR_LEVELS>;

/// The lock cells in `cells` of the nodes of `t`, assembled into a tree: the
/// root node's cell and, below it, the cells of the locked page-table nodes
/// reachable from the root through locked nodes. A node at paging level
/// `level` is at flat-tree level `NR_LEVELS - level`; `depth` is the root's
/// paging level.
pub open spec fn locked_cells_at<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    depth: nat,
) -> PtLockedTree
    decreases depth,
{
    PtLockedTree::new(
        cells[t.value().node().slot_vaddr()],
        (NR_LEVELS - t.value().node().level()) as nat,
        Seq::new(
            NR_ENTRIES as nat,
            |i: int|
                if depth > 0 && t.has_child(i) && t.child(i).value().is_node() && node_cell_ok(
                    t.child(i).value().node(),
                    cells,
                ) {
                    Some(locked_cells_at(t.child(i), cells, (depth - 1) as nat))
                } else {
                    None
                },
        ),
    )
}

/// [`locked_cells_at`] for a node subtree.
pub open spec fn locked_cells<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
) -> PtLockedTree {
    locked_cells_at(t, cells, t.value().node().level() as nat)
}

/// In `t`, every child slot whose range overlaps `[va_start, va_end)` has been
/// grafted exactly when the PTE model points to a child node: the holder has
/// all of the range below the root. The flat-tree counterpart of
/// [`dfs_locked_below`], with the same clipped ranges.
pub open spec fn locked_complete_in_range(
    t: PtLockedTree,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 && t.value().value().pt_level > 1 ==> {
        let ps = page_size::<PagingConsts>(t.value().value().pt_level) as int;
        forall|i: int|
            #![trigger t.children()[i]]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                ==> {
                let cva = node_va + i * ps;
                &&& (t.value().value().child_key(i) is Some <==> t.has_child(i))
                &&& t.has_child(i) ==> locked_complete_in_range(
                    t.child(i),
                    cva,
                    if va_start < cva {
                        cva
                    } else {
                        va_start
                    },
                    if va_end < cva + ps {
                        va_end
                    } else {
                        cva + ps
                    },
                    (depth - 1) as nat,
                )
            }
    }
}

/// The key of a node's lock cell is the node's physical address.
proof fn lemma_cell_key<C: PageTableConfig>(
    e: EntryOwner<C>,
    cell: PtLockCell,
    regions: MetaRegionOwners,
)
    requires
        e.metaregion_sound(regions),
        e.is_node(),
        e.node().holds(cell),
    ensures
        cell.key() == meta_to_frame(e.node().slot_vaddr()),
{
    reveal(lock_key_wf);
}

/// What a node's lock cell says about child slot `i`: its PTE model points to
/// a child node exactly when the child entry is a node, and then to the
/// child's physical address.
proof fn lemma_cell_child_key<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cell: PtLockCell,
    regions: MetaRegionOwners,
    i: int,
)
    requires
        PageTableOwner(t).pt_inv(),
        t.value().metaregion_sound(regions),
        t.value().is_node(),
        t.value().node().holds(cell),
        0 <= i < NR_ENTRIES,
        !t.child(i).value().is_borrowed(),
    ensures
        cell.value().pt_level == t.value().node().level(),
        cell.value().child_key(i) == if t.child(i).value().is_node() {
            Some(meta_to_frame(t.child(i).value().node().slot_vaddr()))
        } else {
            None::<Paddr>
        },
{
    PageTableOwner(t).pt_inv_unroll(i);
    let node = t.value().node();
    reveal(PageTablePageMeta::lock_consts_wf);
    assert(cell.value().pte_auth@[i] == node.pte_view@[i]);
    if t.child(i).value().is_node() {
        assert(t.child(i).value().node().inv());
    }
}

/// The lock cells of a node subtree that are in `cells` form a well-formed
/// flat tree.
proof fn lemma_locked_cells_wf<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    regions: MetaRegionOwners,
    depth: nat,
)
    requires
        PageTableOwner(t).pt_inv(),
        PageTableOwner(t).metaregion_sound(regions),
        t.value().is_node(),
        node_cell_ok(t.value().node(), cells),
        depth == t.value().node().level(),
    ensures
        locked_cells_at(t, cells, depth).inv(),
        tree_wf_at(locked_cells_at(t, cells, depth), depth),
    decreases depth,
{
    let lt = locked_cells_at(t, cells, depth);
    let node = t.value().node();
    let cell = cells[node.slot_vaddr()];
    let lvl = (NR_LEVELS - node.level()) as nat;
    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::la_inv(t.value(), t.level()));
    assert(t.value().metaregion_sound(regions));
    reveal(PageTablePageMeta::lock_consts_wf);
    assert(lt.value() == cell);
    node.lemma_holds_inv_cell(cell);
    reveal(PageTablePageMeta::lock_consts_wf);
    assert(lt.level() == lvl);
    assert(lt.value().inv_cell());
    assert forall|i: int|
        #![trigger lt.children()[i]]
        0 <= i < NR_ENTRIES && lt.has_child(i) implies {
        &&& t.has_child(i)
        &&& lt.child(i) == locked_cells_at(t.child(i), cells, (depth - 1) as nat)
        &&& lt.child(i).level() == lvl + 1
        &&& lt.child(i).inv()
        &&& tree_wf_at(lt.child(i), (depth - 1) as nat)
        &&& lt.value().value().child_key(i) == Some(lt.child(i).value().key())
    } by {
        PageTableOwner(t).pt_inv_unroll(i);
        t.lemma_subtree_satisfies_unroll_once(
            t.value().path,
            PageTableOwner::<C>::metaregion_sound_pred(regions),
            i,
        );
        let c = t.child(i);
        assert(c.value().node().inv());
        lemma_cell_child_key(t, cell, regions, i);
        lemma_cell_key(c.value(), cells[c.value().node().slot_vaddr()], regions);
        lemma_locked_cells_wf(c, cells, regions, (depth - 1) as nat);
    }
    if node.level() == 1 {
        assert forall|i: int| 0 <= i < NR_ENTRIES implies !(
        #[trigger] lt.children()[i] is Some) by {
            if lt.has_child(i) {
                PageTableOwner(t).pt_inv_unroll(i);
                assert(t.child(i).value().node().inv());
            }
        }
    }
    assert(lt.inv_children());
    assert(lt.inv());
}

/// The lock cells of a node subtree in which [`dfs_acquire_lock`] has locked a
/// range form a flat tree that is complete over the range.
proof fn lemma_locked_cells_complete<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    regions: MetaRegionOwners,
    depth: nat,
    node_va: int,
    va_start: int,
    va_end: int,
)
    requires
        PageTableOwner(t).pt_inv(),
        PageTableOwner(t).metaregion_sound(regions),
        t.value().is_node(),
        node_cell_ok(t.value().node(), cells),
        depth == t.value().node().level(),
        dfs_locked_below(t, cells, node_va, va_start, va_end, (INC_LEVELS - t.level()) as nat),
        forall|i: int|
            0 <= i < NR_ENTRIES ==> !(#[trigger] t.child(i)).value().is_borrowed() || !((va_start
                - node_va) / (page_size::<PagingConsts>(t.value().node().level()) as int) <= i
                < ceil_div(
                va_end - node_va,
                page_size::<PagingConsts>(t.value().node().level()) as int,
            )),
    ensures
        locked_complete_in_range(
            locked_cells_at(t, cells, depth),
            node_va,
            va_start,
            va_end,
            depth,
        ),
    decreases depth,
{
    let lt = locked_cells_at(t, cells, depth);
    let node = t.value().node();
    let cell = cells[node.slot_vaddr()];
    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::la_inv(t.value(), t.level()));
    assert(t.value().metaregion_sound(regions));
    reveal(PageTablePageMeta::lock_consts_wf);
    assert(lt.value() == cell);
    if node.level() > 1 {
        let ps = page_size::<PagingConsts>(node.level()) as int;
        assert(lt.value().value().pt_level == node.level());
        assert forall|i: int|
            #![trigger lt.children()[i]]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(
                va_end - node_va,
                ps,
            ) implies {
            let cva = node_va + i * ps;
            &&& (lt.value().value().child_key(i) is Some <==> lt.has_child(i))
            &&& lt.has_child(i) ==> locked_complete_in_range(
                lt.child(i),
                cva,
                if va_start < cva {
                    cva
                } else {
                    va_start
                },
                if va_end < cva + ps {
                    va_end
                } else {
                    cva + ps
                },
                (depth - 1) as nat,
            )
        } by {
            PageTableOwner(t).pt_inv_unroll(i);
            t.lemma_subtree_satisfies_unroll_once(
                t.value().path,
                PageTableOwner::<C>::metaregion_sound_pred(regions),
                i,
            );
            let c = t.child(i);
            lemma_cell_child_key(t, cell, regions, i);
            if c.value().is_node() {
                let cva = node_va + i * ps;
                assert(c.value().node().inv());
                assert(node_cell_ok(c.value().node(), cells));
                assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] c.child(
                    j,
                )).value().is_borrowed() by {
                    PageTableOwner(c).pt_inv_unroll(j);
                }
                lemma_locked_cells_complete(
                    c,
                    cells,
                    regions,
                    (depth - 1) as nat,
                    cva,
                    if va_start < cva {
                        cva
                    } else {
                        va_start
                    },
                    if va_end < cva + ps {
                        va_end
                    } else {
                        cva + ps
                    },
                );
            }
        }
    }
}

/// [`dfs_acquire_lock`]'s postcondition, restated as a [`flat_tree`] tree: if
/// the root is locked, the cells in `cells` of the subtree's nodes form a
/// well-formed tree that is complete over the range.
///
/// [`flat_tree`]: vstd_extra::resource::flat_tree
pub open spec fn dfs_locked_flat<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    node_va: Vaddr,
    va_range: Range<Vaddr>,
) -> bool {
    node_cell_ok(t.value().node(), cells) ==> {
        &&& tree_wf(locked_cells(t, cells))
        &&& locked_complete_in_range(
            locked_cells(t, cells),
            node_va as int,
            va_range.start as int,
            va_range.end as int,
            t.value().node().level() as nat,
        )
    }
}

proof fn lemma_dfs_locked_flat<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    cells: Map<usize, PtLockCell>,
    regions: MetaRegionOwners,
    node_va: Vaddr,
    va_range: Range<Vaddr>,
)
    requires
        PageTableOwner(t).pt_inv(),
        PageTableOwner(t).metaregion_sound(regions),
        t.value().is_node(),
        dfs_range_ok(t.value().node().level(), node_va, va_range),
        dfs_locked_below(
            t,
            cells,
            node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - t.level()) as nat,
        ),
        forall|i: int|
            0 <= i < NR_ENTRIES ==> !(#[trigger] t.child(i)).value().is_borrowed() || !(
            idx_range_spec(t.value().node().level(), node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(
                t.value().node().level(),
                node_va,
                va_range.start,
                va_range.end,
            ).1),
    ensures
        dfs_locked_flat(t, cells, node_va, va_range),
{
    if node_cell_ok(t.value().node(), cells) {
        let depth = t.value().node().level() as nat;
        lemma_idx_range_spec_exact(t.value().node().level(), node_va, va_range);
        lemma_locked_cells_wf(t, cells, regions, depth);
        lemma_locked_cells_complete(
            t,
            cells,
            regions,
            depth,
            node_va as int,
            va_range.start as int,
            va_range.end as int,
        );
        assert(locked_cells(t, cells).level() == NR_LEVELS - t.value().node().level());
    }
}

/// A node has no live guard. (Unlike [`node_unguarded`], it may be held.)
pub open spec fn node_no_guard<C: PageTableConfig>(guards: Guards) -> spec_fn(
    EntryOwner<C>,
    TreePath<NR_ENTRIES>,
) -> bool {
    |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
        e.is_node() ==> guards.unlocked(e.node().slot_vaddr())
}

/// No node strictly below the root of `t` has a live guard.
pub open spec fn children_no_guard<C: PageTableConfig>(t: OwnerSubtree<C>, guards: Guards) -> bool {
    forall|i: int|
        0 <= i < NR_ENTRIES && #[trigger] t.has_child(i) ==> t.child(i).subtree_satisfies(
            t.value().path.push_tail(i),
            node_no_guard::<C>(guards),
        )
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// # Safety
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten.
///
/// # Verified Properties
/// ## Preconditions
/// - `subtree` is the owner of the sub-tree rooted at `cur_node`, sound with
///   respect to `regions`, and no node strictly below its root has a live guard.
/// - The root and every page-table node below it that overlaps the range have
///   their lock cells in `cells` ([`node_cell_ok`], [`dfs_locked_below`]), as
///   [`dfs_acquire_lock`] left them; `cells` are the cells this thread holds.
/// - `cur_node` has been redeemed from the [`Guards`] ledger: `obl` is its drop
///   obligation.
/// - The range is within the node's range (see [`dfs_range_ok`]).
/// ## Postconditions
/// - The root and every page-table node below it that overlaps the range have
///   returned their cells to their locks ([`dfs_unlocked_below`]); the cells are
///   no longer held.
/// - Only cells of nodes in the subtree are removed. The guards made for the
///   children are redeemed, so `guards.guards` is unchanged.
#[verus_spec(
    with Tracked(subtree): Tracked<&OwnerSubtree<C>>,
        Tracked(cells): Tracked<&mut Map<usize, PtLockCell>>,
        Tracked(guards): Tracked<&mut Guards>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(obl): Tracked<DropObligation<usize>>
    requires
        PageTableOwner(*subtree).pt_inv(),
        PageTableOwner(*subtree).metaregion_sound(*old(regions)),
        subtree.value().is_node(),
        subtree.value().path.len() == subtree.level(),
        node_cell_ok(subtree.value().node(), *old(cells)),
        old(guards).cells_wf(*old(cells)),
        subtree.value().node().relate_guard(cur_node),
        obl.value() == subtree.value().node().slot_vaddr(),
        children_no_guard(*subtree, *old(guards)),
        dfs_range_ok(subtree.value().node().level(), cur_node_va, va_range),
        // Borrowed (shared) entries only occur at the top level, and the range
        // stays clear of them.
        forall|i: int| 0 <= i < NR_ENTRIES ==> !(#[trigger] subtree.child(i)).value().is_borrowed()
            || !(idx_range_spec(subtree.value().node().level(), cur_node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(subtree.value().node().level(), cur_node_va, va_range.start, va_range.end).1),
        dfs_locked_below(
            *subtree,
            *old(cells),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - subtree.level()) as nat,
        ),
        old(regions).inv(),
    ensures
        PageTableOwner(*subtree).metaregion_sound(*final(regions)),
        !final(cells).contains_key(subtree.value().node().slot_vaddr()),
        dfs_unlocked_below(
            *subtree,
            *final(cells),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - subtree.level()) as nat,
        ),
        forall|a: usize|
            #[trigger] final(cells).contains_key(a) ==> old(cells).contains_key(a)
                && final(cells)[a] == old(cells)[a],
        forall|a: usize|
            #[trigger] old(cells).contains_key(a) && !final(cells).contains_key(a) ==> addr_under::<C>(
                *old(regions),
                a,
                subtree.value().path,
            ),
        final(guards).cells_wf(*final(cells)),
        final(guards).guards == old(guards).guards,
        final(regions).inv(),
        final(regions).slot_owners == old(regions).slot_owners,
        final(regions).slots == old(regions).slots,
)]
#[verifier::spinoff_prover]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
unsafe fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    mut cur_node: PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let ghost root = subtree.value();
    let ghost root_addr = root.node().slot_vaddr();
    let ghost f_sound0 = PageTableOwner::<C>::metaregion_sound_pred(*old(regions));
    let ghost f_path = PageTableOwner::<C>::path_correct_pred();
    proof {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        assert(regions.contains(root.node().slot_index));
        PageTableOwner::<C>::lemma_pt_inv_implies_path_correct(*subtree, root.path);
        // The root's slot records the root's path, so the root is below it.
        assert(root.metaregion_sound(*old(regions)));
        let idx = frame_to_index(root.meta_slot_paddr()->0);
        assert(old(regions).slot_owners[idx].paths_in_pt == set![root.path]);
        assert(addr_under::<C>(*old(regions), root_addr, root.path));
    }
    let cur_level = {
        let tracked node_owner = subtree.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_owner))]
        cur_node.level()
    };
    let ghost depth = (INC_LEVELS - subtree.level()) as nat;
    let ghost guards0 = *guards;
    let ghost regions0 = *regions;
    let ghost cells0 = *cells;
    if cur_level > 1 {
        let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
        let ghost s0 = idx_range.start as int;
        let ghost e0 = idx_range.end as int;
        let ghost ps = page_size::<PagingConsts>(cur_level) as int;
        proof {
            lemma_idx_range_spec_exact(cur_level, cur_node_va, va_range);
        }
        let start = idx_range.start;
        // `for i in idx_range.rev()` upstream.
        let mut i = idx_range.end;
        while i > start
            invariant
                s0 <= i <= e0 <= NR_ENTRIES,
                start == s0,
                root.node().relate_guard(cur_node),
                cur_level == root.node().level(),
                cur_level > 1,
                ps == page_size::<PagingConsts>(cur_level) as int,
                depth == INC_LEVELS - subtree.level(),
                root == subtree.value(),
                root_addr == root.node().slot_vaddr(),
                PageTableOwner(*subtree).pt_inv(),
                PageTableOwner(*subtree).metaregion_sound(*regions),
                subtree.subtree_satisfies(root.path, f_path),
                f_sound0 == PageTableOwner::<C>::metaregion_sound_pred(regions0),
                f_path == PageTableOwner::<C>::path_correct_pred(),
                guards.guards == guards0.guards,
                guards0 == *old(guards),
                regions0 == *old(regions),
                cells0 == *old(cells),
                regions.inv(),
                regions.slot_owners == regions0.slot_owners,
                regions.slots == regions0.slots,
                guards.cells_wf(*cells),
                forall|a: usize| #[trigger]
                    cells.contains_key(a) ==> cells0.contains_key(a) && cells[a] == cells0[a],
                forall|a: usize| #[trigger]
                    cells0.contains_key(a) && !cells.contains_key(a) ==> addr_under::<C>(
                        regions0,
                        a,
                        root.path,
                    ),
                node_cell_ok(root.node(), *cells),
                forall|j: int|
                    #![trigger subtree.child(j)]
                    s0 <= j < i && subtree.child(j).value().is_node() ==> {
                        let cva = cur_node_va + j * ps;
                        &&& node_cell_ok(subtree.child(j).value().node(), *cells)
                        &&& dfs_locked_below(
                            subtree.child(j),
                            *cells,
                            cva,
                            if va_range.start < cva {
                                cva
                            } else {
                                va_range.start as int
                            },
                            if va_range.end < cva + ps {
                                va_range.end as int
                            } else {
                                cva + ps
                            },
                            (depth - 1) as nat,
                        )
                    },
                forall|j: int|
                    #![trigger subtree.child(j)]
                    i <= j < e0 && subtree.child(j).value().is_node() ==> {
                        let cva = cur_node_va + j * ps;
                        &&& !cells.contains_key(subtree.child(j).value().node().slot_vaddr())
                        &&& dfs_unlocked_below(
                            subtree.child(j),
                            *cells,
                            cva,
                            if va_range.start < cva {
                                cva
                            } else {
                                va_range.start as int
                            },
                            if va_range.end < cva + ps {
                                va_range.end as int
                            } else {
                                cva + ps
                            },
                            (depth - 1) as nat,
                        )
                    },
            decreases i,
        {
            i = i - 1;
            let ghost regions_i = *regions;
            proof {
                PageTableOwner(*subtree).pt_inv_unroll(i as int);
                subtree.lemma_subtree_satisfies_unroll_once(
                    root.path,
                    PageTableOwner::<C>::metaregion_sound_pred(*regions),
                    i as int,
                );
            }
            let ghost child0 = subtree.child(i as int);
            let child = {
                let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
                let tracked child_owner = subtree.tracked_borrow_child(
                    i as int,
                ).tracked_borrow_value();
                let tracked parent_cell = cells.tracked_borrow(root_addr);
                #[verus_spec(with Tracked(parent_owner), Tracked(child_owner), Tracked(&*regions),
                    Tracked(&parent_cell.tracked_borrow_value().ptes))]
                cur_node.entry(i)
            };
            let child_ref = {
                let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
                let tracked child_owner = subtree.tracked_borrow_child(
                    i as int,
                ).tracked_borrow_value();
                #[verus_spec(with Tracked(child_owner), Tracked(parent_owner), Tracked(regions))]
                child.to_ref()
            };
            proof {
                PageTableOwner::<C>::lemma_metaregion_sound_preserved_slot_owners_eq_subtree(
                    *subtree,
                    root.path,
                    regions_i,
                    *regions,
                );
            }
            match child_ref {
                ChildRef::PageTable(pt) => {
                    let ghost regions1 = *regions;
                    let ghost guards_i = *guards;
                    let ghost cells_i = *cells;
                    let ghost path_i = root.path.push_tail(i as int);
                    proof {
                        subtree.lemma_subtree_satisfies_unroll_once(root.path, f_path, i as int);
                        assert(child0.subtree_satisfies(path_i, node_no_guard::<C>(guards0)));
                        root.path.lemma_push_tail_preserves_inv(i as int);
                        assert(guards_i.unlocked(child0.value().node().slot_vaddr()));
                        lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                    }
                    proof_decl! {
                        let tracked child_obl: DropObligation<usize>;
                    }
                    // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                    let child_node = unsafe {
                        let tracked child_owner = subtree.tracked_borrow_child(
                            i as int,
                        ).tracked_borrow_value().tracked_borrow_node();
                        #[verus_spec(with Tracked(child_owner), Tracked(guards))]
                        pt.make_guard_unchecked(guard)
                    };
                    let ghost guards1 = *guards;
                    proof {
                        child_obl = child_node.tracked_redeem(guards);
                        assert forall|x: usize| #[trigger]
                            guards.guards.contains(x) == guards_i.guards.contains(x) by {
                            if guards_i.lock_held(x) {
                                assert(guards1.lock_held(x));
                            } else {
                                assert(guards_i.unlocked(x));
                            }
                        }
                        assert(guards.guards =~= guards_i.guards);
                        assert(guards.held == guards_i.held);
                        // No node below the child has a guard.
                        assert forall|j: int|
                            0 <= j < NR_ENTRIES && #[trigger] child0.has_child(
                                j,
                            ) implies child0.child(j).subtree_satisfies(
                            path_i.push_tail(j),
                            node_no_guard::<C>(*guards),
                        ) by {
                            child0.lemma_subtree_satisfies_unroll_once(
                                path_i,
                                node_no_guard::<C>(guards0),
                                j,
                            );
                            assert(node_no_guard::<C>(*guards) == node_no_guard::<C>(guards0));
                        }
                        // Below the top level, no entry is borrowed.
                        assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] child0.child(
                            j,
                        )).value().is_borrowed() by {
                            PageTableOwner(child0).pt_inv_unroll(j);
                        }
                    }
                    let child_node_va = cur_node_va + i * page_size::<C>(cur_level);
                    let child_node_va_end = child_node_va + page_size::<C>(cur_level);
                    let va_start = va_range.start.max(child_node_va);
                    let va_end = va_range.end.min(child_node_va_end);
                    proof {
                        assert(va_start == (if va_range.start < child_node_va {
                            child_node_va
                        } else {
                            va_range.start
                        }));
                        assert(va_end == (if va_range.end < child_node_va_end {
                            va_range.end
                        } else {
                            child_node_va_end
                        }));
                    }
                    // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                    // guards are forgotten.
                    unsafe {
                        let tracked c = subtree.tracked_borrow_child(i as int);
                        #[verus_spec(with Tracked(c), Tracked(cells), Tracked(guards), Tracked(regions), Tracked(child_obl))]
                        dfs_release_lock(guard, child_node, child_node_va, va_start..va_end)
                    };
                    proof {
                        PageTableOwner::<
                            C,
                        >::lemma_metaregion_sound_preserved_slot_owners_eq_subtree(
                            *subtree,
                            root.path,
                            regions1,
                            *regions,
                        );
                        // Every cell removed is below the child, and so below the root.
                        assert forall|a: usize| #[trigger]
                            cells0.contains_key(a) && !cells.contains_key(a) implies addr_under::<
                            C,
                        >(regions0, a, root.path) by {
                            if cells_i.contains_key(a) {
                                assert(addr_under::<C>(regions1, a, path_i));
                                assert forall|p: TreePath<NR_ENTRIES>| #[trigger]
                                    regions0.slot_owners[frame_to_index(
                                        meta_to_frame(a),
                                    )].paths_in_pt.contains(p) implies PageTableOwner::<
                                    C,
                                >::is_prefix_of(root.path, p) by {
                                    assert(PageTableOwner::<C>::is_prefix_of(path_i, p));
                                    root.path.lemma_push_tail_len(i as int);
                                    assert forall|k: int|
                                        0 <= k < root.path.len() implies root.path[k] == p[k] by {
                                        root.path.lemma_push_tail_index(i as int);
                                        assert(path_i[k] == root.path[k]);
                                    }
                                }
                            }
                        }
                        // The root keeps its cell: its slot records a path not below the child.
                        root.path.lemma_push_tail_len(i as int);
                        assert(root.metaregion_sound(regions0));
                        let ridx = frame_to_index(root.meta_slot_paddr()->0);
                        assert(regions0.slot_owners[ridx].paths_in_pt.contains(root.path));
                        assert(!addr_under::<C>(regions0, root_addr, path_i));
                        assert(cells.contains_key(root_addr));
                        // The children not visited yet keep their cells.
                        assert forall|j: int|
                            #![trigger subtree.child(j)]
                            s0 <= j < i && subtree.child(j).value().is_node() implies {
                            let cva = cur_node_va + j * ps;
                            &&& node_cell_ok(subtree.child(j).value().node(), *cells)
                            &&& dfs_locked_below(
                                subtree.child(j),
                                *cells,
                                cva,
                                if va_range.start < cva {
                                    cva
                                } else {
                                    va_range.start as int
                                },
                                if va_range.end < cva + ps {
                                    va_range.end as int
                                } else {
                                    cva + ps
                                },
                                (depth - 1) as nat,
                            )
                        } by {
                            let cva = cur_node_va + j * ps;
                            PageTableOwner(*subtree).pt_inv_unroll(j);
                            subtree.lemma_subtree_satisfies_unroll_once(root.path, f_sound0, j);
                            subtree.lemma_subtree_satisfies_unroll_once(root.path, f_path, j);
                            root.path.lemma_push_tail_preserves_inv(j);
                            root.path.lemma_push_tail_len(j);
                            let pj = root.path.push_tail(j);
                            assert(!PageTableOwner::<C>::is_prefix_of(path_i, pj)) by {
                                root.path.lemma_push_tail_index(i as int);
                                root.path.lemma_push_tail_index(j);
                                assert(path_i[root.path.len() as int]
                                    != pj[root.path.len() as int]);
                            }
                            let cj = subtree.child(j);
                            assert(cj.value().metaregion_sound(regions0));
                            let jidx = frame_to_index(cj.value().meta_slot_paddr()->0);
                            assert(regions0.slot_owners[jidx].paths_in_pt.contains(
                                cj.value().path,
                            ));
                            assert(!addr_under::<C>(
                                regions0,
                                cj.value().node().slot_vaddr(),
                                path_i,
                            ));
                            lemma_dfs_locked_below_agree(
                                cj,
                                pj,
                                cells_i,
                                *cells,
                                regions0,
                                path_i,
                                cva,
                                if va_range.start < cva {
                                    cva
                                } else {
                                    va_range.start as int
                                },
                                if va_range.end < cva + ps {
                                    va_range.end as int
                                } else {
                                    cva + ps
                                },
                                (depth - 1) as nat,
                            );
                        }
                        // The children visited before stay unlocked.
                        assert forall|j: int|
                            #![trigger subtree.child(j)]
                            i <= j < e0 && subtree.child(j).value().is_node() implies {
                            let cva = cur_node_va + j * ps;
                            &&& !cells.contains_key(subtree.child(j).value().node().slot_vaddr())
                            &&& dfs_unlocked_below(
                                subtree.child(j),
                                *cells,
                                cva,
                                if va_range.start < cva {
                                    cva
                                } else {
                                    va_range.start as int
                                },
                                if va_range.end < cva + ps {
                                    va_range.end as int
                                } else {
                                    cva + ps
                                },
                                (depth - 1) as nat,
                            )
                        } by {
                            let cva = cur_node_va + j * ps;
                            if j != i {
                                lemma_dfs_unlocked_below_shrink(
                                    subtree.child(j),
                                    cells_i,
                                    *cells,
                                    cva,
                                    if va_range.start < cva {
                                        cva
                                    } else {
                                        va_range.start as int
                                    },
                                    if va_range.end < cva + ps {
                                        va_range.end as int
                                    } else {
                                        cva + ps
                                    },
                                    (depth - 1) as nat,
                                );
                            }
                        }
                    }
                },
                ChildRef::None | ChildRef::Frame(_, _, _) => {
                    proof {
                        assert(!child0.value().is_node());
                    }
                },
            }
        }
    }
    // Upstream, `cur_node` is dropped here, which unlocks it.

    let ghost cells1 = *cells;
    proof_decl! {
        let tracked root_cell = cells.tracked_remove(root_addr);
    }
    {
        let tracked node_owner = subtree.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_owner), Tracked(root_cell), Tracked(guards), Tracked(obl))]
        cur_node.unlock();
    }
    proof {
        assert(cells.dom() =~= guards.held.dom());
        if cur_level > 1 {
            let ps = page_size::<PagingConsts>(cur_level) as int;
            assert forall|j: int|
                #![trigger subtree.child(j)]
                0 <= j < NR_ENTRIES && (va_range.start - cur_node_va) / ps <= j < ceil_div(
                    va_range.end - cur_node_va,
                    ps,
                ) && subtree.child(j).value().is_node() implies {
                let cva = cur_node_va + j * ps;
                &&& !cells.contains_key(subtree.child(j).value().node().slot_vaddr())
                &&& dfs_unlocked_below(
                    subtree.child(j),
                    *cells,
                    cva,
                    if va_range.start < cva {
                        cva
                    } else {
                        va_range.start as int
                    },
                    if va_range.end < cva + ps {
                        va_range.end as int
                    } else {
                        cva + ps
                    },
                    (depth - 1) as nat,
                )
            } by {
                let cva = cur_node_va + j * ps;
                lemma_dfs_unlocked_below_shrink(
                    subtree.child(j),
                    cells1,
                    *cells,
                    cva,
                    if va_range.start < cva {
                        cva
                    } else {
                        va_range.start as int
                    },
                    if va_range.end < cva + ps {
                        va_range.end as int
                    } else {
                        cva + ps
                    },
                    (depth - 1) as nat,
                );
            }
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
/// # Safety
///
/// The caller must ensure that all the nodes in the sub-tree are locked
/// and all guards are forgotten.
///
/// This function must not be called upon a shared node, e.g., the second-
/// top level nodes that the kernel space and user space share.
#[verus_spec(res =>
    with Tracked(owner): Tracked<&mut CursorOwner<'a, C>>,
        Tracked(guards): Tracked<&mut Guards>,
        Ghost(locked_addr): Ghost<usize>,
        Ghost(subtree_mappings_count): Ghost<nat>,
        Ghost(regions): Ghost<MetaRegionOwners>
    requires
        old(owner).inv(),
        // The locked_addr must be the address that was locked (held in guards)
        old(guards).lock_held(locked_addr),
        old(guards).cells_wf(old(owner).cells),
    ensures
        // The cells of the sub-tree's nodes, which are below the entry the
        // cursor points to, go back to their locks. The cursor keeps the rest.
        final(guards).cells_wf(final(owner).cells),
        forall|a: usize| #[trigger] final(owner).cells.contains_key(a)
            ==> old(owner).cells.contains_key(a) && final(owner).cells[a] == old(owner).cells[a],
        forall|a: usize| #[trigger] old(owner).cells.contains_key(a) && !addr_under::<C>(
            regions,
            a,
            old(owner).continuations[old(owner).level - 1].path().push_tail(old(owner).index() as int),
        ) ==> final(owner).cells.contains_key(a) && final(owner).cells[a] == old(owner).cells[a],
        // The return value equals the number of mappings in the subtree.
        // This connects the physical DFS frame count to the ghost view_rec mappings count.
        res as nat == subtree_mappings_count,
        final(owner).inv(),
        final(owner).guard_level == old(owner).guard_level,
        final(owner).level == old(owner).level,
        final(owner).va == old(owner).va,
        final(owner).barrier_va == old(owner).barrier_va,
        final(owner).prefix == old(owner).prefix,
        final(owner).popped_too_high == old(owner).popped_too_high,
        // Preserve the guard for each continuation level
        final(owner).level <= 4 ==> final(owner).continuations[3].guard == old(owner).continuations[3].guard,
        final(owner).level <= 3 ==> final(owner).continuations[2].guard == old(owner).continuations[2].guard,
        final(owner).level <= 2 ==> final(owner).continuations[1].guard == old(owner).continuations[1].guard,
        final(owner).level == 1 ==> final(owner).continuations[0].guard == old(owner).continuations[0].guard,
        final(owner).continuations[final(owner).level - 1].children[final(owner).continuations[final(owner).level - 1].idx as int]->0.value().is_absent(),
        // entry_own at current level is preserved
        final(owner).continuations[final(owner).level - 1].entry_own == old(owner).continuations[old(owner).level - 1].entry_own,
        // Children at current level are preserved
        forall |i: int| 0 <= i < NR_ENTRIES ==>
            #[trigger]
            final(owner).continuations[final(owner).level - 1].children[i] == old(owner).continuations[old(owner).level - 1].children[i],
        // Continuations at higher levels are completely preserved
        forall |lvl: int| #![trigger final(owner).continuations[lvl]]
            final(owner).level <= lvl < NR_LEVELS ==> final(owner).continuations[lvl] == old(owner).continuations[lvl],
        // Guards postconditions:
        // 1. Everything that was unlocked before is still unlocked (no new locks added)
        forall |addr: usize| old(guards).unlocked(addr) ==> final(guards).unlocked(addr),
        // 2. The locked address is now unlocked
        final(guards).unlocked(locked_addr),
        // 3. Other locked addresses remain locked
        forall |addr: usize| addr != locked_addr && old(guards).lock_held(addr) ==> final(guards).lock_held(addr),
)]
#[verifier::external_body]
pub unsafe fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
    rcu_guard: &A,
    sub_tree: &PageTableGuard<'a, C>,
) -> usize {
    unimplemented!();
    /*
    let mut sub_tree_val = sub_tree.take(Tracked(guard_perm));
    let stray_mut = sub_tree_val.stray_mut();
    let tracked node_owner = entry_own.tracked_take_node();
    let stray = stray_mut.take(Tracked(&mut node_owner.as_node.meta_own.stray));

    stray_mut.put(Tracked(&mut node_owner.as_node.meta_own.stray), true);

    proof {
        entry_own.tracked_put_node(node_owner);
    }

    if sub_tree_val.level() == 1 {
        return sub_tree_val.nr_children() as usize;
    }
    sub_tree.put(Tracked(guard_perm), sub_tree_val);

    let mut num_frames = 0;

    let end = nr_subpage_per_huge::<C>();
    for i in 0..end {
        let child = PageTableGuard::entry(sub_tree, i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let locked_pt = unsafe { pt.make_guard_unchecked(rcu_guard) };
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                num_frames += unsafe { dfs_mark_stray_and_unlock(rcu_guard, locked_pt) };
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }

    num_frames*/
}

/// Spec-level ceiling division: `ceil(x / d)` for non-negative `x` and positive `d`.
pub open spec fn ceil_div(x: int, d: int) -> int
    recommends
        d > 0,
        x >= 0,
{
    (x + d - 1) / d
}

pub open spec fn idx_range_spec(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_start: Vaddr,
    va_end: Vaddr,
) -> (usize, usize) {
    let ps = page_size::<PagingConsts>(cur_node_level) as int;
    let start_idx = (va_start - cur_node_va) / ps;
    let end_idx = ceil_div(va_end - cur_node_va, ps);
    (start_idx as usize, end_idx as usize)
}

#[verus_spec(ret =>
    requires
        1 <= cur_node_level <= NR_LEVELS,
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size::<PagingConsts>((cur_node_level + 1) as PagingLevel),
        cur_node_va % page_size::<PagingConsts>((cur_node_level + 1) as PagingLevel) == 0,
    ensures
        ret.start == idx_range_spec(cur_node_level, cur_node_va, va_range.start, va_range.end).0,
        ret.end == idx_range_spec(cur_node_level, cur_node_va, va_range.start, va_range.end).1,
        ret.start < ret.end,
        ret.end <= NR_ENTRIES,
)]
fn dfs_get_idx_range<C: PagingConstsTrait>(
    cur_node_level: PagingLevel,
    cur_node_va: Vaddr,
    va_range: &Range<Vaddr>,
) -> Range<usize> {
    let ps = page_size::<PagingConsts>(cur_node_level);
    let diff = va_range.end - cur_node_va;

    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        use vstd::arithmetic::div_mod::*;
        lemma_page_size_ge_base::<PagingConsts>(cur_node_level);
        lemma_page_size_spec_values();

        // diff + ps - 1 fits in usize: both <= page_size::<PagingConsts>(5) = 2^48
    }

    let start_idx = (va_range.start - cur_node_va) / ps;
    let end_idx = (diff + ps - 1) / ps;

    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        use vstd::arithmetic::div_mod::*;

        let ai = ps as int;
        let xi = diff as int;
        let si = va_range.start - cur_node_va;

        // -- start_idx < end_idx --
        // start_idx * ps <= si < xi <= end_idx * ps, so start_idx < end_idx.
        assert(start_idx < end_idx) by {
            lemma_fundamental_div_mod(si, ai);
            lemma_fundamental_div_mod(xi + ai - 1, ai);
            let q1 = si / ai;
            let r1 = si % ai;
            let q2 = (xi + ai - 1) / ai;
            let r2 = (xi + ai - 1) % ai;
            assert(q1 < q2) by (nonlinear_arith)
                requires
                    si == ai * q1 + r1,
                    xi + ai - 1 == ai * q2 + r2,
                    0 <= r1 < ai,
                    0 <= r2 < ai,
                    0 <= si < xi,
                    ai > 0,
            ;
        };

        // -- end_idx <= NR_ENTRIES --
        // diff <= page_size::<PagingConsts>(level+1) = NR_ENTRIES * ps
        // So ceil_div(diff, ps) <= NR_ENTRIES.
        let psu = page_size::<PagingConsts>((cur_node_level + 1) as PagingLevel) as int;
        // (psu + ai - 1) / ai == NR_ENTRIES (since psu = NR_ENTRIES * ai)
        assert(psu + ai - 1 == NR_ENTRIES * ai + (ai - 1)) by (nonlinear_arith)
            requires
                psu == NR_ENTRIES * ai,
        ;
        lemma_fundamental_div_mod_converse(psu + ai - 1, ai, NR_ENTRIES as int, ai - 1);
        // So (psu + ai - 1) / ai == NR_ENTRIES
        // xi + ai - 1 <= psu + ai - 1, so end_idx = (xi+ai-1)/ai <= (psu+ai-1)/ai = NR_ENTRIES
        lemma_div_is_ordered(xi + ai - 1, psu + ai - 1, ai);
    }

    start_idx..end_idx
}

} // verus!
