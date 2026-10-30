// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
use vstd::prelude::*;
use vstd_extra::{array_ptr::*, drop_tracking::TrackDrop, ghost_tree::*, ownership::*};

use crate::specs::{
    mm::{
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{
            node::{Guards, entry_owners::EntryOwner},
            page_table_coverage_end_spec,
        },
    },
    task::InAtomicMode,
};

use crate::mm::frame::{
    MetaSlot,
    meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
};
use crate::mm::page_table::*;
use crate::mm::{
    NR_ENTRIES, NR_LEVELS, PAGE_SIZE, Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr,
    nr_subpage_per_huge, paddr_to_vaddr, page_table::*,
};
use align_ext::AlignExt;
use core::ops::IndexMut;
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Range, sync::atomic::Ordering};

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

    #[verus_spec(with Tracked(&cont.entry_own), Tracked(guards), Tracked(regions))]
    dfs_acquire_lock(guard, &mut subtree_root, cur_node_va, va.clone());

    proof {
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
    ensures
            final(regions).slots == old(regions).slots,
            forall|idx: int| #![trigger final(regions).slot_owners[idx]]
                old(regions).contains(idx) && old(regions).ref_count(idx) != REF_COUNT_UNUSED ==>
                    final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
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
            Ghost(node_owner.meta_own.stray.id())
        )]
        let stray = pt_guard.stray_mut();
        let is_stray = *(stray.borrow(
            Tracked(&cont.entry_own.tracked_borrow_node().meta_own.stray),
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
        Ghost(node_owner.meta_own.stray.id())
    )]
    let stray = pt_guard.stray_mut();
    let is_stray = *(stray.borrow(Tracked(&cont.entry_own.tracked_borrow_node().meta_own.stray)));

    proof {
        cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
    }

    if is_stray {
        return None;
    }
    Some(pt_guard)
}

/// Acquires the locks for the given range in the sub-tree rooted at the node.
///
/// `cur_node_va` must be the virtual address of the `cur_node`. The `va_range`
/// must be within the range of the `cur_node`. The range must not be empty.
///
/// The function will forget all the [`PageTableGuard`] objects in the sub-tree.
#[verus_spec(
    with Tracked(entry_own): Tracked<&EntryOwner<C>>,
        Tracked(guards): Tracked<&mut Guards>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        entry_own.is_node(),
        entry_own.inv(),
        entry_own.node().relate_guard(*cur_node),
        old(guards).lock_held(entry_own.node().slot_vaddr()),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        old(regions).inv(),
    ensures
        // The root node is still lock_held (not ManuallyDrop'd by this fn).
        *final(cur_node) == *old(cur_node),
        final(guards).lock_held(entry_own.node().slot_vaddr()),
        // All other locks are preserved: addresses not in this subtree are unchanged.
        forall |addr: usize|
            addr != entry_own.node().slot_vaddr()
            && old(guards).guards.contains(addr) ==>
            #[trigger] final(guards).guards.contains(addr),
        // Addresses not in old guards don't appear in final guards
        // (acquire + ManuallyDrop is a no-op on the guards set for child addrs).
        forall |addr: usize|
            !old(guards).guards.contains(addr) ==>
            !#[trigger] final(guards).guards.contains(addr),
        // regions preserved
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        final(regions).slot_owners == old(regions).slot_owners,
)]
#[verifier::external_body]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let cur_level = cur_node.level();
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    for i in idx_range {
        let child = cur_node.entry(i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                let mut pt_guard = pt.lock(guard);
                let child_node_va = cur_node_va + i * page_size::<C>(cur_level);
                let child_node_va_end = child_node_va + page_size::<C>(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
                let _ = ManuallyDrop::new(pt_guard);
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }
}

/// Releases the locks for the given range in the sub-tree rooted at the node.
///
/// # Safety
///
/// The caller must ensure that the nodes in the specified sub-tree are locked
/// and all guards are forgotten.
#[verus_spec(
    with Tracked(entry_own): Tracked<EntryOwner<C>>,
        Tracked(guards): Tracked<&mut Guards>
)]
#[verifier::external_body]
unsafe fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let cur_level = cur_node.level();
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let end = idx_range.end;
    for i in idx_range {
        let child = cur_node.entry(end - i);
        match child.to_ref() {
            ChildRef::PageTable(pt) => {
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let mut child_node = unsafe {
                    #[verus_spec(with Tracked(entry_own.tracked_borrow_node()), Tracked(guards))]
                    pt.make_guard_unchecked(guard)
                };
                let child_node_va = cur_node_va + (end - i) * page_size::<C>(cur_level);
                let child_node_va_end = child_node_va + page_size::<C>(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and all
                // guards are forgotten.
                unsafe { dfs_release_lock(guard, &mut child_node, child_node_va, va_start..va_end)
                };
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
    }
}

/// The owner held at the root of `n`.
pub open spec fn node_owner<C: PageTableConfig>(n: PageTableOwner<C>) -> EntryOwner<C> {
    n.0.value()
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
    with Tracked(owner): Tracked<&mut PageTableOwner<C>>,
        Tracked(guards): Tracked<&mut Guards>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Ghost(locked_addr): Ghost<usize>,
        Ghost(subtree_mappings_count): Ghost<nat>
    requires
        old(owner).inv(),
        // `sub_tree` is the guard of the subtree's root node.
        old(owner).0.value().node().relate_guard(*sub_tree),
        locked_addr == old(owner).0.value().node().slot_vaddr(),
        old(guards).lock_held(locked_addr),
        subtree_mappings_count == old(owner)@.mappings.len(),
        old(regions).inv(),
    ensures
        // The number of frames equals the number of mappings in the subtree.
        res as nat == subtree_mappings_count,
        final(owner).0.value().is_node(),
        // The caller takes this back to clone the page-table node.
        final(owner).0.value().node().frame_permission
            == old(owner).0.value().node().frame_permission,
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        final(regions).slot_owners == old(regions).slot_owners,
        // 1. Everything that was unlocked before is still unlocked.
        forall |addr: usize| old(guards).unlocked(addr) ==> final(guards).unlocked(addr),
        // 2. The locked address is now unlocked.
        final(guards).unlocked(locked_addr),
        // 3. Other locked addresses remain locked.
        forall |addr: usize| addr != locked_addr && old(guards).lock_held(addr)
            ==> final(guards).lock_held(addr),
    decreases old(owner).0.value().node().level(),
)]
pub unsafe fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
    rcu_guard: &A,
    sub_tree: &PageTableGuard<'a, C>,
) -> usize {
    // Mark the node as stray. The lock is held, so we have exclusive access.
    let tracked node_own = owner.0.tracked_borrow_mut_value().tracked_borrow_mut_node();
    #[verus_spec(with
        Tracked(Some(node_own.frame_permission.tracked_borrow())),
        Tracked(&())
    )]
    let meta = sub_tree.meta();
    let _was_stray = meta.stray.replace(Tracked(&mut node_own.meta_own.stray), true);

    let tracked node_own = owner.0.tracked_borrow_value().tracked_borrow_node();
    #[verus_spec(with Tracked(node_own))]
    let level = sub_tree.level();

    if level == 1 {
        let tracked node_own = owner.0.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_own))]
        let nr_children = sub_tree.nr_children();
        // Dropping the guard releases the lock.
        proof {
            let tracked _obl = (*sub_tree).tracked_redeem(guards);
        }
        return nr_children as usize;
    }

    let mut num_frames: usize = 0;
    let end = nr_subpage_per_huge::<C>();
    let mut i: usize = 0;
    while i < end
        invariant
            true,
        decreases end - i,
    {
        let ghost ii = i as int;
        let tracked node_own = owner.0.tracked_borrow_value().tracked_borrow_node();
        let tracked child_entry_own = owner.0.tracked_borrow_child(ii).tracked_borrow_value();
        // `entry` needs `&mut PageTableGuard`, so read the PTE directly instead.
        let pte = unsafe {
            #[verus_spec(with Tracked(node_own), Tracked(&*regions))]
            sub_tree.read_pte(i)
        };
        let child_ref = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(child_entry_own))]
            ChildRef::<'a, C>::from_pte(&pte, level)
        };
        match child_ref {
            ChildRef::PageTable(pt) => {
                let tracked mut child_owner = PageTableOwner(owner.0.tracked_take_child(ii));
                let ghost child_locked_addr = child_owner.0.value().node().slot_vaddr();
                let ghost child_count = child_owner@.mappings.len();
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let locked_pt = unsafe {
                    #[verus_spec(with
                        Tracked(child_owner.0.tracked_borrow_value().tracked_borrow_node()),
                        Tracked(guards)
                    )]
                    pt.make_guard_unchecked(rcu_guard)
                };
                // SAFETY: The caller ensures that all the nodes in the sub-tree are locked and
                // all guards are forgotten.
                #[verus_spec(with
                    Tracked(&mut child_owner),
                    Tracked(guards),
                    Tracked(regions),
                    Ghost(child_locked_addr),
                    Ghost(child_count)
                )]
                let frames_below = dfs_mark_stray_and_unlock(rcu_guard, &locked_pt);
                proof {
                    let tracked PageTableOwner(child) = child_owner;
                    owner.0.tracked_put_child(ii, child);
                }
                num_frames = num_frames + frames_below;
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
        i = i + 1;
    }
    // Dropping the guard releases the lock.
    proof {
        let tracked _obl = (*sub_tree).tracked_redeem(guards);
    }
    num_frames
}

//  pub fn dfs_mark_stray_and_unlock<'a, C: PageTableConfig, A: InAtomicMode>(
//      rcu_guard: &'a A,
//      sub_tree: PPtr<PageTableGuard<'a, C>>,
//  ) -> (num_frames: usize)
//      requires
//          config_is_x86_64::<C>(),
//          old(regions).inv(),
//          subtree_wf(*old(owner), *old(regions), node_owner(*old(owner)).level() as nat),
//          node_owner(*old(owner)).guard_perm@.pptr() == sub_tree,
//      ensures
//          *regions == *old(regions),
//          subtree_wf(*owner, *regions, node_owner(*old(owner)).level() as nat),
//          node_owner(*owner).is_stray(),
//          stray_propagates(*owner, node_owner(*old(owner)).level() as nat),
//          node_owner(*owner).guard_perm == node_owner(*old(owner)).guard_perm,
//          node_owner(*owner).slot_perm == node_owner(*old(owner)).slot_perm,
//          node_owner(*owner).level() == node_owner(*old(owner)).level(),
//          num_frames <= max_frames(node_owner(*old(owner)).level()),
//      decreases node_owner(*old(owner)).level(),
//  {
//      proof {
//          lemma_config_is_x86_64::<C>();
//      }
//      let ghost old_root = *owner;
//      let ghost lv = node_owner(old_root).level() as nat;
//  
//      // Mark this node stray. Its owner is taken out of the tree node while
//      // the flag is written.
//      let tracked mut cur_own = owner.value.tree_node.tracked_take();
//      proof {
//          lemma_owner_frame(cur_own, *regions);
//      }
//      let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
//      let sub_tree_val = sub_tree.borrow(Tracked(cur_own.guard_perm.borrow()));
//      #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
//      let stray_cell = sub_tree_val.stray_mut();
//      let _was_stray = stray_cell.replace(
//          Tracked(cur_own.node_own.meta_own.stray.borrow_mut()),
//          true,
//      );
//      #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
//      let level = sub_tree_val.level();
//      proof {
//          owner.value.tree_node = Some(cur_own);
//      }
//      let ghost marked = node_owner(*owner);
//      assert(marked.ptes() == node_owner(old_root).ptes());
//      assert(owner.children == old_root.children);
//  
//      if level == 1 {
//          let tracked cur_own = owner.value.tree_node.tracked_borrow();
//          let sub_tree_val = sub_tree.borrow(Tracked(cur_own.guard_perm.borrow()));
//          #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
//          let nr_children = sub_tree_val.nr_children();
//          // Dropping the guard releases the lock.
//          #[verus_spec(with Tracked(cur_own))]
//          PageTableGuard::<'a, C>::unlock(sub_tree);
//          proof {
//              lemma_max_frames_bounded(1);
//              assert forall|i: int| 0 <= i < NR_ENTRIES() implies (
//              #[trigger] owner.children[i] is Some <==> marked.pte_is_node(i)) by {
//                  assert(old_root.children[i] is Some <==> node_owner(old_root).pte_is_node(i));
//              }
//          }
//          return nr_children as usize;
//      }
//      let mut num_frames: usize = 0;
//  
//      let end = nr_subpage_per_huge::<C>();
//      let mut i: usize = 0;
//      while i < end
//          invariant
//              config_is_x86_64::<C>(),
//              i <= end,
//              end == 512,
//              2 <= level <= 4,
//              level == lv,
//              *regions == *old(regions),
//              regions.inv(),
//              subtree_wf(old_root, *regions, lv),
//              old_root == *old(owner),
//              lv == node_owner(*old(owner)).level(),
//              owner.value.tree_node is Some,
//              node_owner(*owner) == marked,
//              marked.inv(),
//              marked.in_region(*regions),
//              marked.is_stray(),
//              marked.level() == lv,
//              marked.ptes() == node_owner(old_root).ptes(),
//              marked.guard_perm == node_owner(old_root).guard_perm,
//              marked.slot_perm == node_owner(old_root).slot_perm,
//              marked.guard_perm@.pptr() == sub_tree,
//              owner.children.len() == 512,
//              // Not yet visited: unchanged.
//              forall|j: int| i <= j < 512 ==> #[trigger] owner.children[j] == old_root.children[j],
//              // Visited: same shape, and the whole child sub-tree is stray.
//              forall|j: int|
//                  0 <= j < i ==> (#[trigger] owner.children[j] is Some
//                      <==> old_root.children[j] is Some),
//              forall|j: int|
//                  0 <= j < i && #[trigger] owner.children[j] is Some ==> {
//                      &&& node_owner(owner.children[j].unwrap()).paddr() == marked.child_paddr(j)
//                      &&& subtree_wf(owner.children[j].unwrap(), *regions, (lv - 1) as nat)
//                      &&& node_owner(owner.children[j].unwrap()).is_stray()
//                      &&& stray_propagates(owner.children[j].unwrap(), (lv - 1) as nat)
//                  },
//              num_frames <= i * max_frames((level - 1) as PagingLevel),
//          decreases end - i,
//      {
//          proof {
//              lemma_config_is_x86_64::<C>();
//          }
//          let ghost ii = i as int;
//          let tracked cur_own = owner.value.tree_node.tracked_borrow();
//          proof {
//              lemma_owner_frame(*cur_own, *regions);
//          }
//          let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(cur_own.paddr()));
//          #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
//          let child = PageTableGuard::<'a, C>::entry(sub_tree, i);
//  
//          proof {
//              assert(owner.children[ii] == old_root.children[ii]);
//              assert(old_root.children[ii] is Some <==> node_owner(old_root).pte_is_node(ii));
//              if marked.pte_is_node(ii) {
//                  let c = old_root.children[ii].unwrap();
//                  assert(subtree_wf(c, *regions, (lv - 1) as nat));
//                  assert(node_owner(c).in_region(*regions));
//              }
//          }
//          #[verus_spec(with Tracked(cur_own), Tracked(regions))]
//          let child_ref = child.to_ref();
//          match child_ref {
//              ChildRef::PageTable(pt) => {
//                  let ghost before = *owner;
//                  let tracked mut child_node = owner.tracked_take_child(ii);
//                  let ghost c_old = child_node;
//                  proof {
//                      assert(subtree_wf(c_old, *regions, (lv - 1) as nat));
//                      assert(node_owner(c_old).level() == lv - 1);
//                      assert(node_owner(c_old).level() < node_owner(*old(owner)).level());
//                  }
//                  let tracked child_own = child_node.value.tree_node.tracked_borrow();
//                  proof {
//                      lemma_owner_frame(*child_own, *regions);
//                  }
//                  assert(pt.inner.ptr == child_own.slot_perm@.pptr());
//                  // The node is locked and the new guard is unique.
//                  #[verus_spec(with Tracked(child_own))]
//                  let locked_pt = pt.make_guard_unchecked(rcu_guard);
//  
//                  // All the nodes in the sub-tree are locked and all guards are forgotten.
//                  #[verus_spec(with Tracked(&mut child_node), Tracked(regions))]
//                  let frames_below = dfs_mark_stray_and_unlock(rcu_guard, locked_pt);
//  
//                  proof {
//                      owner.tracked_put_child(ii, child_node);
//                      assert(owner.children =~= before.children.update(ii, Some(child_node)));
//                      lemma_max_frames_bounded(level);
//                      lemma_mul_inequality(i as int + 1, 512, max_frames((level - 1) as PagingLevel));
//                      lemma_mul_is_distributive_add_other_way(
//                          max_frames((level - 1) as PagingLevel),
//                          i as int,
//                          1,
//                      );
//                  }
//                  num_frames = num_frames + frames_below;
//              },
//              ChildRef::None | ChildRef::Frame(_, _, _) => {
//                  proof {
//                      lemma_max_frames_bounded(level);
//                      lemma_mul_inequality(
//                          i as int,
//                          i as int + 1,
//                          max_frames((level - 1) as PagingLevel),
//                      );
//                  }
//              },
//          }
//          i = i + 1;
//      }

//     // Dropping the guard releases the lock of this node.
//     let tracked cur_own = owner.value.tree_node.tracked_borrow();
//     #[verus_spec(with Tracked(cur_own))]
//     PageTableGuard::<'a, C>::unlock(sub_tree);
// 
//     proof {
//         lemma_max_frames_bounded(level);
//         assert forall|j: int| 0 <= j < NR_ENTRIES() implies (#[trigger] owner.children[j] is Some
//             <==> marked.pte_is_node(j)) by {
//             assert(old_root.children[j] is Some <==> node_owner(old_root).pte_is_node(j));
//         }
//         assert(subtree_wf(*owner, *regions, lv));
//         assert(stray_propagates(*owner, lv));
//     }
//     num_frames
// }

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
        va_range.start % page_size::<PagingConsts>(cur_node_level) == 0,
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
    proof {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
    }
    let ps = page_size::<C>(cur_node_level);
    let diff = va_range.end - cur_node_va;

    proof {
        use vstd::arithmetic::div_mod::*;

        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        lemma_page_size_ge_base::<PagingConsts>(cur_node_level);
        lemma_page_size_spec_values();
        lemma_page_size_next::<PagingConsts>(cur_node_level);
        crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();

        // diff + ps - 1 fits in usize: both <= page_size(5) = 2^48
    }

    let start_idx = (va_range.start - cur_node_va) / ps;
    let end_idx = (diff + ps - 1) / ps;

    proof {
        use vstd::arithmetic::div_mod::*;

        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;

        let ai = ps as int;
        let xi = diff as int;
        let si = va_range.start - cur_node_va;

        assert(start_idx < end_idx) by {
            // si = start_idx * ai (exact division since si % ai == 0)
            lemma_page_size_divides::<PagingConsts>(
                cur_node_level,
                (cur_node_level + 1) as PagingLevel,
            );
            // Prove si % ai == 0: va_range.start and cur_node_va are both multiples of ps.
            // cur_node_va % ps == 0: cur_node_va % page_size(level+1) == 0 and ps | page_size(level+1).
            let psu = page_size::<PagingConsts>((cur_node_level + 1) as PagingLevel) as int;
            assert(cur_node_va as int % ai == 0) by {
                // cur_node_va % psu == 0, psu % ai == 0
                // ==> cur_node_va is a multiple of ai
                lemma_fundamental_div_mod(cur_node_va as int, psu);
                lemma_fundamental_div_mod(psu, ai);
                let k = cur_node_va as int / psu;
                let m = psu / ai;
                // lemma gives: cur_node_va == psu * k + (cur_node_va % psu)
                //              psu == ai * m + (psu % ai)
                assert(cur_node_va == (m * k) * ai) by (nonlinear_arith)
                    requires
                        cur_node_va == psu * k + 0,
                        psu == ai * m + 0,
                        cur_node_va as int % psu == 0,
                        psu % ai == 0,
                ;
                lemma_mod_multiples_basic(m * k, ai);
            };
            assert(si % ai == 0) by {
                // va_range.start = si + cur_node_va, both multiples of ai
                // si % ai + cur_node_va % ai == va_range.start % ai (mod ai)
                lemma_mod_adds(si, cur_node_va as int, ai);
                // gives: si%ai + 0 == 0 + ai * ((si%ai + 0)/ai)
                // so si%ai == ai * (si%ai / ai)
                // since 0 <= si%ai < ai, si%ai / ai == 0, so si%ai == 0
            };

            // start_idx * ai = si (exact division since si % ai == 0)
            lemma_fundamental_div_mod(si, ai);
            // si == ai * (si / ai) + (si % ai) == ai * start_idx + 0
            vstd::arithmetic::mul::lemma_mul_is_commutative(ai, si / ai);

            // end_idx * ai >= xi: ceil_div(xi, ai) * ai >= xi
            lemma_fundamental_div_mod(xi + ai - 1, ai);
            let qi = (xi + ai - 1) / ai;
            let ri = (xi + ai - 1) % ai;
            // xi + ai - 1 == ai * qi + ri
            vstd::arithmetic::mul::lemma_mul_is_commutative(ai, qi);
            assert(qi * ai >= xi) by (nonlinear_arith)
                requires
                    xi + ai - 1 == qi * ai + ri,
                    0 <= ri < ai,
                    ai > 0,
            ;

            assert(start_idx * ai < end_idx * ai) by (nonlinear_arith)
                requires
                    start_idx * ai == si,
                    end_idx * ai >= xi,
                    si < xi,
            ;
            vstd::arithmetic::mul::lemma_mul_strict_inequality_converse(
                start_idx as int,
                end_idx as int,
                ai,
            );
        };

        // -- end_idx <= NR_ENTRIES --
        // diff <= page_size(level+1) = NR_ENTRIES * ps
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
