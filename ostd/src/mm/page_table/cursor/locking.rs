// SPDX-License-Identifier: MPL-2.0
//! Implementation of the locking protocol.
use core::{marker::PhantomData, ops::Range, sync::atomic::Ordering};

use vstd_extra::drop_tracking::{DropObligation, ManuallyDrop, TrackDrop};

use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{
    MetaSlot,
    meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
};
use crate::mm::{
    NR_ENTRIES, NR_LEVELS, PAGE_SIZE, Paddr, PagingConsts, PagingConstsTrait, PagingLevel, Vaddr,
    nr_subpage_per_huge, paddr_to_vaddr, page_table::*,
};

use vstd_extra::array_ptr::*;

use crate::mm::page_table::*;
use crate::specs::mm::frame::meta_owners::{PtLockCell, PtLockPayload};
use vstd_extra::resource::flat_tree::{LockedTree, LockedValue, tree_wf, tree_wf_at};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::page_table::node::entry_owners::{EntryOwner, EntryOwnerKind};
use crate::specs::mm::page_table::node::owners::{NodeOwner, lemma_count_where_pte_bytes, lock_key_wf};
use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::specs::task::InAtomicMode;

use align_ext::AlignExt;
use core::ops::IndexMut;

verus! {

broadcast use group_ghost_tree_lemmas;

pub assume_specification<Idx: Clone>[ Range::<Idx>::clone ](range: &Range<Idx>) -> (res: Range<Idx>)
    ensures
        res == *range,
;

#[verus_spec(ret =>
    with Tracked(pt_own): Tracked<PageTableOwner<C>>,
        Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>
    requires
        pt.relates_owner(pt_own, *old(regions)),
        pt_own.0.value().node().relate_guard(root_guard),
        forall|i: int| 0 <= i < NR_ENTRIES ==> pt_own.0.has_child(i),
        va.start < va.end,
        // Per-config tightening; see `Cursor::new`. Pulled through to the
        // cursor's `LOCKED_END_BOUND_spec` invariant.
        va.end <= C::LOCKED_END_BOUND_spec(),
        crate::specs::mm::page_table::is_valid_range_spec::<C>(*va),
        // The range ends well below the top of the address space, so the
        // child ranges computed while locking do not overflow.
        va.end + page_size(NR_LEVELS as PagingLevel) <= usize::MAX,
        // This thread holds no guard on any node of the page table.
        pt_own.0.subtree_satisfies(pt_own.0.value().path, node_unguarded::<C>(*old(guards))),
    ensures
        ret.0.invariants(*ret.1, *final(regions), *final(guards)),
        (*ret.1).in_locked_range(),
        ret.0.level == ret.0.guard_level,
        ret.0.guard_level == NR_LEVELS as PagingLevel,
        ret.0.va < ret.0.barrier_va.end,
        ret.0.va == va.start,
        ret.0.barrier_va == *va,
        (*ret.1).as_page_table_owner() == pt_own,
        // The root continuation's path matches the input's root path — this
        // lets `view_rec(pt_own.0.value.path)` unify with the lemma's
        // `view_rec(continuations[3].path())`.
        (*ret.1).continuations[3].path() == pt_own.0.value().path,
        // Non-saturation preservation: if the caller established that no
        // non-UNUSED slot was one increment away from REF_COUNT_MAX before
        // locking, the same bound holds after. Locking may allocate new PT
        // nodes (bumping some parent ref counts), but ref counts stay within
        // safe bounds during a single lock_range call.
        (forall |i: int| #![trigger old(regions).slot_owners[i]]
            old(regions).contains(i)
            && old(regions).slot_owners[i].ref_count()
                != REF_COUNT_UNUSED
            ==> old(regions).slot_owners[i].ref_count() + 1
                < REF_COUNT_MAX)
        ==>
        (forall |i: int| #![trigger final(regions).slot_owners[i]]
            final(regions).contains(i)
            && final(regions).slot_owners[i].ref_count()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[i].ref_count() + 1
                < REF_COUNT_MAX),
        // Locking only allocates page-table nodes from UNUSED slots, so any
        // slot that was already in use keeps its paths_in_pt intact.
        forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).slot_owners[idx].ref_count()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        // For *in-use* slots, refcount value and usage are exactly
        // preserved across `lock_range` — composes
        // `try_traverse_and_lock_subtree_root`'s in-use preservation with
        // `dfs_acquire_lock`'s `slot_owners ==` preservation.
        forall|idx: int| #![trigger final(regions).slot_owners[idx]]
            old(regions).contains(idx)
            && old(regions).slot_owners[idx].ref_count()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].ref_count()
                    == old(regions).slot_owners[idx].ref_count()
                && final(regions).slot_owners[idx].usage
                    == old(regions).slot_owners[idx].usage,
        // Saturated-slot bridge (bidirectional): a slot is at
        // `>= REF_COUNT_MAX` before iff after, with the same value.
        // Composes helpers' clauses (see their ensures).
        forall|idx: int| #![trigger final(regions).slot_owners[idx].ref_count()]
            final(regions).slot_owners[idx].ref_count()
                >= REF_COUNT_MAX
            ==> old(regions).slot_owners[idx].ref_count()
                    == final(regions).slot_owners[idx].ref_count(),
        forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
            old(regions).slot_owners[idx].ref_count()
                >= REF_COUNT_MAX
            ==> final(regions).slot_owners[idx].ref_count()
                    == old(regions).slot_owners[idx].ref_count(),
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
    let ghost start_idx = AbstractVaddr::from_vaddr(va.start).index[NR_LEVELS - 1];

    proof {
        assert forall|i: int| 0 <= i < NR_ENTRIES implies (
        #[trigger] pt_own.0.children()[i]) is Some by {
            assert(pt_own.0.has_child(i));
        };
    }

    let tracked mut cursor_own: CursorOwner<'rcu, C> = CursorOwner::tracked_new(
        pt_own.0,
        start_idx as usize,
        root_guard,
    );
    proof {
        assert(cursor_own.continuations[NR_LEVELS - 1].as_subtree() =~= pt_own.0);
    }

    // Retry if the candidate subtree became stray before we acquired its lock.
    let mut subtree_root = None;
    #[verus_spec(
        invariant
            subtree_root is None ==> {
                &&& cursor_own.level == NR_LEVELS
                &&& cursor_own.continuations.dom().contains(NR_LEVELS - 1)
                &&& cursor_own.continuations[NR_LEVELS - 1].all_some()
                &&& cursor_own.continuations[NR_LEVELS - 1].as_subtree() == pt_own.0
                &&& cursor_own.continuations[NR_LEVELS - 1].path() == pt_own.0.value().path
                &&& *guards == *old(guards)
            },
            subtree_root is Some ==> {
                &&& regions.inv()
                &&& 1 <= cursor_own.level <= NR_LEVELS
                &&& cursor_own.continuations.dom().contains(cursor_own.level - 1)
                &&& cursor_own.continuations[cursor_own.level - 1].inv()
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
                        .entry_own.node().meta_vaddr(),
                )
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
    #[verus_spec(with Tracked(cont_node_owner), Tracked(&*regions))]
    let guard_level = subtree_root.level();
    proof {
        cursor_own.guard_level = guard_level;
    }
    let cur_node_va = va.start.align_down(page_size(guard_level + 1));

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
        lemma_page_size_monotone(guard_level, NR_LEVELS as PagingLevel);
        assert(dfs_range_ok(guard_level, cur_node_va, *va));
    }
    #[verus_spec(with Tracked(&mut locked_subtree), Tracked(guards), Tracked(regions))]
    dfs_acquire_lock(guard, &mut subtree_root, cur_node_va, va.clone());

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
        assume(res.0.invariants(*res.1, *regions, *guards) && (*res.1).in_locked_range()
            && res.0.level == res.0.guard_level && res.0.va < res.0.barrier_va.end && (
        *res.1).as_page_table_owner() == pt_own && (*res.1).continuations[3].path()
            == pt_own.0.value().path);
        assume((forall|i: int|
            #![trigger old(regions).slot_owners[i]]
            old(regions).contains(i) && old(regions).slot_owners[i].ref_count() != REF_COUNT_UNUSED
                ==> old(regions).slot_owners[i].ref_count() + 1 < REF_COUNT_MAX) ==> (forall|i: int|

            #![trigger regions.slot_owners[i]]
            regions.contains(i) && regions.slot_owners[i].ref_count() != REF_COUNT_UNUSED
                ==> regions.slot_owners[i].ref_count() + 1 < REF_COUNT_MAX));
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
    guards: Guards<'rcu>,
) -> bool {
    let t = cont.as_subtree();
    let level = cont.entry_own.node().level;
    let ps_up = page_size((level + 1) as PagingLevel);
    let node_va = vstd_extra::arithmetic::nat_align_down(va.start as nat, ps_up as nat) as Vaddr;
    &&& cont.all_some()
    &&& PageTableOwner(t).metaregion_sound(regions)
    &&& children_unguarded(t, guards)
    &&& 1 <= level <= NR_LEVELS
    // The locked node covers the range.
    &&& va.end <= node_va + ps_up
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
        Tracked(guards): Tracked<&mut Guards<'rcu>>
    requires
        old(cursor_own).level == NR_LEVELS,
        old(cursor_own).continuations.dom().contains(NR_LEVELS - 1),
        old(cursor_own).continuations[NR_LEVELS - 1].all_some(),
        old(cursor_own).continuations[NR_LEVELS - 1].as_subtree().subtree_satisfies(
            old(cursor_own).continuations[NR_LEVELS - 1].path(),
            node_unguarded::<C>(*old(guards)),
        ),
        crate::specs::mm::page_table::is_valid_range_spec::<C>(*va),
    ensures
        r is None ==> {
            &&& *final(cursor_own) == *old(cursor_own)
            &&& *final(regions) == *old(regions)
            &&& *final(guards) == *old(guards)
        },
        r is Some ==> {
            &&& final(cursor_own).va == old(cursor_own).va
            &&& final(cursor_own).prefix == old(cursor_own).prefix
            &&& final(cursor_own).view_mappings() == old(cursor_own).view_mappings()
            &&& final(cursor_own).popped_too_high == false
            &&& 1 <= final(cursor_own).level <= NR_LEVELS
            &&& final(cursor_own).continuations.dom().contains(final(cursor_own).level - 1)
            &&& final(cursor_own).continuations[final(cursor_own).level - 1].inv()
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
        r is Some ==> locked_subtree_ready(
            final(cursor_own).continuations[final(cursor_own).level - 1],
            *va,
            *final(regions),
            *final(guards),
        ),
        // The subtree root is lock_held in guards.
        r is Some ==> final(guards).lock_held(
            final(cursor_own).continuations[final(cursor_own).level - 1]
                .entry_own.node().meta_vaddr()),
        // regions invariant preserved
        final(regions).inv(),
        // Locking only allocates fresh page-table nodes from UNUSED slots;
        // it does not mutate any slot that was already in use.
        forall|idx: int| #![trigger final(regions).slot_owners[idx].paths_in_pt]
            old(regions).slot_owners[idx].ref_count()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].paths_in_pt
                    == old(regions).slot_owners[idx].paths_in_pt,
        // For *in-use* slots (non-UNUSED refcount), the refcount value and
        // usage are exactly preserved — locking only allocates fresh PT
        // nodes from UNUSED slots; it never mutates a slot already in use.
        forall|idx: int| #![trigger final(regions).slot_owners[idx]]
            old(regions).contains(idx)
            && old(regions).slot_owners[idx].ref_count()
                != REF_COUNT_UNUSED
            ==> final(regions).slot_owners[idx].ref_count()
                    == old(regions).slot_owners[idx].ref_count()
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
            final(regions).slot_owners[idx].ref_count()
                >= REF_COUNT_MAX
            ==> old(regions).slot_owners[idx].ref_count()
                    == final(regions).slot_owners[idx].ref_count(),
        forall|idx: int| #![trigger old(regions).slot_owners[idx].ref_count()]
            old(regions).slot_owners[idx].ref_count()
                >= REF_COUNT_MAX
            ==> final(regions).slot_owners[idx].ref_count()
                    == old(regions).slot_owners[idx].ref_count(),
        // Therefore any frame that was `item_not_mapped` (its paths_in_pt was
        // empty, hence `ref_count` might be UNUSED-or-non-UNUSED) stays so:
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

    let end = C::NR_LEVELS();
    for cur_level in 0..end {
        let start_idx = pte_index::<C>(va.start, end - cur_level + 1);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, end - cur_level + 1);
            (end - cur_level + 1) > 1 && start_idx == end_idx
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
            if cur_pte.is_last(end - cur_level + 1) {
                break;
            }
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            proof {
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
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
            let node_ref = unsafe { PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr) };
            node_ref.lock(guard)
        };

        let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
        let tracked node_owner = cont.entry_own.tracked_borrow_node();
        let tracked meta_points_to = regions.slots.tracked_borrow(node_owner.slot_index);
        let tracked meta_slot_owner = regions.slot_owners.tracked_borrow(node_owner.slot_index);
        #[verus_spec(with
            Tracked(meta_points_to),
            Tracked(&meta_slot_owner.metadata_perm),
            Tracked(&()),
            Ghost(node_owner.meta().stray.id())
        )]
        let stray = pt_guard.stray_mut();
        let is_stray = *(stray.borrow(
            Tracked(&cont.entry_own.tracked_borrow_node().tracked_borrow_meta().stray),
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
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
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
                let ghost next_idx = pte_index::<C>(
                    va.start,
                    (end - cur_level) as PagingLevel,
                ) as usize;
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
        let node_ref = unsafe { PageTableNodeRef::<'rcu, C>::borrow_paddr(cur_pt_addr) };
        node_ref.lock(guard)
    };

    let tracked mut cont = cursor_own.continuations.tracked_remove(cursor_own.level - 1);
    let tracked node_owner = cont.entry_own.tracked_borrow_node();
    let tracked meta_points_to = regions.slots.tracked_borrow(node_owner.slot_index);
    let tracked meta_slot_owner = regions.slot_owners.tracked_borrow(node_owner.slot_index);
    #[verus_spec(with
        Tracked(meta_points_to),
        Tracked(&meta_slot_owner.metadata_perm),
        Tracked(&()),
        Ghost(node_owner.meta().stray.id())
    )]
    let stray = pt_guard.stray_mut();
    let is_stray = *(stray.borrow(Tracked(&cont.entry_own.tracked_borrow_node().tracked_borrow_meta().stray)));

    proof {
        cursor_own.continuations.tracked_insert(cursor_own.level - 1, cont);
    }

    if is_stray {
        return None;
    }
    Some(pt_guard)
}

/// The range conditions under which `dfs_acquire_lock` visits a node at
/// `level` covering `[node_va, node_va + page_size(level + 1))`.
pub open spec fn dfs_range_ok(level: PagingLevel, node_va: Vaddr, va_range: Range<Vaddr>) -> bool {
    &&& 1 <= level <= NR_LEVELS
    &&& node_va <= va_range.start
    &&& va_range.start < va_range.end
    &&& va_range.end <= node_va + page_size((level + 1) as PagingLevel)
    &&& node_va % page_size((level + 1) as PagingLevel) == 0
    &&& va_range.end + page_size(level) <= usize::MAX
}

/// Every page-table node below `t` whose range overlaps `[va_start, va_end)`
/// holds its lock payload: exactly the nodes `dfs_acquire_lock` locks.
pub open spec fn dfs_locked_below<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 && t.value().is_node() && t.value().node().level > 1 ==> {
        let ps = page_size(t.value().node().level) as int;
        forall|i: int|
            #![trigger t.child(i)]
            (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps) && t.child(
                i,
            ).value().is_node() ==> {
                let cva = node_va + i * ps;
                &&& t.child(i).value().node().is_locked()
                &&& dfs_locked_below(
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

/// [`idx_range_spec`]'s casts are exact.
proof fn lemma_idx_range_spec_exact(level: PagingLevel, node_va: Vaddr, va_range: Range<Vaddr>)
    requires
        dfs_range_ok(level, node_va, va_range),
    ensures
        idx_range_spec(level, node_va, va_range.start, va_range.end).0 as int == (va_range.start
            - node_va) / (page_size(level) as int),
        idx_range_spec(level, node_va, va_range.start, va_range.end).1 as int == ceil_div(
            va_range.end - node_va,
            page_size(level) as int,
        ),
{
    use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
    use vstd::arithmetic::div_mod::*;
    lemma_page_size_spec_values();
    let ps = page_size(level) as int;
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
        (va_range.start - node_va) / (page_size(level) as int) <= i < ceil_div(
            va_range.end - node_va,
            page_size(level) as int,
        ),
        i < NR_ENTRIES,
    ensures
        ({
            let ps = page_size(level) as int;
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
    lemma_page_size_divides(level, (level + 1) as PagingLevel);
    let ps = page_size(level) as int;
    let psl = page_size((level - 1) as PagingLevel) as int;
    let psu = page_size((level + 1) as PagingLevel) as int;
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
///   respect to `regions`, and no node strictly below its root has a live guard.
/// - The range is within the node's range (see [`dfs_range_ok`]).
/// ## Postconditions
/// - Every page-table node below the root that overlaps the range holds its
///   lock payload ([`dfs_locked_below`]); the payloads come from the nodes'
///   locks.
/// - The child guards are forgotten, so `guards` is unchanged.
#[verus_spec(
    with Tracked(subtree): Tracked<&mut OwnerSubtree<C>>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        PageTableOwner(*old(subtree)).pt_inv(),
        PageTableOwner(*old(subtree)).metaregion_sound(*old(regions)),
        old(subtree).value().is_node(),
        old(subtree).value().node().relate_guard(*old(cur_node)),
        children_unguarded(*old(subtree), *old(guards)),
        dfs_range_ok(old(subtree).value().node().level, cur_node_va, va_range),
        // Borrowed (shared) entries only occur at the top level, and the range
        // stays clear of them.
        forall|i: int| 0 <= i < NR_ENTRIES ==> !(#[trigger] old(subtree).child(i)).value().is_borrowed()
            || !(idx_range_spec(old(subtree).value().node().level, cur_node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(old(subtree).value().node().level, cur_node_va, va_range.start, va_range.end).1),
        old(regions).inv(),
    ensures
        PageTableOwner(*final(subtree)).pt_inv(),
        PageTableOwner(*final(subtree)).metaregion_sound(*final(regions)),
        final(subtree).value() == old(subtree).value(),
        final(subtree).level() == old(subtree).level(),
        dfs_locked_below(
            *final(subtree),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - final(subtree).level()) as nat,
        ),
        dfs_locked_flat(*final(subtree), cur_node_va, va_range),
        *final(guards) == *old(guards),
        *final(cur_node) == *old(cur_node),
        final(regions).inv(),
        final(regions).slot_owners == old(regions).slot_owners,
        forall|k: int| old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(k),
        forall|k: int| old(regions).slots.contains_key(k) ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
)]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
fn dfs_acquire_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    cur_node: &mut PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let ghost root = subtree.value();
    proof {
        assert(regions.contains(root.node().slot_index));
    }
    let cur_level = {
        let tracked node_owner = subtree.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_owner), Tracked(&*regions))]
        cur_node.level()
    };
    if cur_level == 1 {
        proof {
            lemma_dfs_locked_flat(*subtree, *regions, cur_node_va, va_range);
        }
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let ghost s0 = idx_range.start as int;
    let ghost e0 = idx_range.end as int;
    let ghost ps = page_size(cur_level) as int;
    proof {
        lemma_idx_range_spec_exact(cur_level, cur_node_va, va_range);
    }
    let ghost depth = (INC_LEVELS - subtree.level()) as nat;
    let ghost old_children = subtree.children();
    let ghost guards0 = *guards;
    let ghost regions0 = *regions;
    for i in idx_range
        invariant
            s0 <= i <= e0 <= NR_ENTRIES,
            cur_level == root.node().level,
            ps == page_size(cur_level) as int,
            depth == INC_LEVELS - subtree.level(),
            PageTableOwner(*subtree).pt_inv(),
            PageTableOwner(*subtree).metaregion_sound(*regions),
            subtree.value() == root,
            subtree.level() == old(subtree).level(),
            *cur_node == *old(cur_node),
            *guards == guards0,
            guards0 == *old(guards),
            regions0 == *old(regions),
            root == old(subtree).value(),
            old_children == old(subtree).children(),
            regions.inv(),
            regions.slot_owners == regions0.slot_owners,
            forall|k: int| regions0.slots.contains_key(k) ==> #[trigger] regions.slots.contains_key(k),
            forall|k: int| regions0.slots.contains_key(k) ==> regions0.slots[k] == #[trigger] regions.slots[k],
            forall|j: int| i <= j < NR_ENTRIES ==> #[trigger] subtree.children()[j] == old_children[j],
            forall|j: int| 0 <= j < NR_ENTRIES ==> #[trigger] subtree.child(j).value().is_borrowed() == old(subtree).child(j).value().is_borrowed(),
            forall|j: int|
                #![trigger subtree.child(j)]
                s0 <= j < i && subtree.child(j).value().is_node() ==> {
                    let cva = cur_node_va + j * ps;
                    &&& subtree.child(j).value().node().is_locked()
                    &&& dfs_locked_below(
                        subtree.child(j),
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
        let ghost cur_children = subtree.children();
        let ghost regions_i = *regions;
        proof {
            PageTableOwner(*subtree).pt_inv_unroll(i as int);
            assert(subtree.child(i as int) == old(subtree).child(i as int));
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
            #[verus_spec(with Tracked(parent_owner), Tracked(child_owner), Tracked(&*regions))]
            cur_node.entry(i)
        };
        let child_ref = {
            let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
            let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value();
            #[verus_spec(with Tracked(child_owner), Tracked(parent_owner), Tracked(regions))]
            child.to_ref()
        };
        proof {
            PageTableOwner::<C>::metaregion_sound_preserved_slot_owners_eq_subtree(
                *subtree,
                root.path,
                regions_i,
                *regions,
            );
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost t0 = *subtree;
                let ghost regions1 = *regions;
                let ghost path_i = root.path.push_tail(i as int);
                proof {
                    t0.lemma_subtree_satisfies_unroll_once(
                        root.path,
                        PageTableOwner::<C>::metaregion_sound_pred(regions1),
                        i as int,
                    );
                    assert(old(subtree).has_child(i as int));
                    assert(child0.subtree_satisfies(path_i, node_unguarded::<C>(guards0)));
                    assert(guards0.unlocked(child0.value().node().meta_vaddr()));
                }
                proof_decl! {
                    let tracked lock_cell: PtLockCell;
                    let tracked guard_obl: DropObligation<usize>;
                }
                let mut pt_guard = {
                    let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value().tracked_borrow_node();
                    #[verus_spec(with Tracked(child_owner), Tracked(&*regions), Tracked(guards) => Tracked(lock_cell))]
                    pt.lock(guard)
                };
                let ghost guards1 = *guards;
                proof {
                    lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                }
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                proof {
                    let ghost meta_value = child0.value().node().meta_value(*regions);
                    let tracked c = subtree.tracked_borrow_mut_child(i as int);
                    c.tracked_borrow_mut_value().tracked_install_fresh_node_lock_cell(
                        lock_cell,
                        meta_value,
                    );
                    PageTableOwner::<C>::lemma_replace_root_value(child0, *c, *regions);
                    guard_obl = pt_guard.tracked_redeem(guards);
                    assert forall|x: usize| #[trigger] guards.guards.contains(x) == guards0.guards.contains(x) by {
                        if guards0.lock_held(x) {
                            assert(guards1.lock_held(x));
                        } else {
                            assert(guards0.unlocked(x));
                        }
                    }
                    assert(guards.guards =~= guards0.guards);
                    // No node below the child has a guard.
                    assert forall|j: int|
                        0 <= j < NR_ENTRIES && #[trigger] c.has_child(j) implies c.child(j).subtree_satisfies(
                        c.value().path.push_tail(j),
                        node_unguarded::<C>(*guards),
                    ) by {
                        child0.lemma_subtree_satisfies_unroll_once(
                            path_i,
                            node_unguarded::<C>(guards0),
                            j,
                        );
                    }
                    // Below the top level, no entry is borrowed.
                    assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] c.child(j)).value().is_borrowed() by {
                        PageTableOwner(*c).pt_inv_unroll(j);
                    }
                }

                let ghost c_inst = subtree.child(i as int);
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
                {
                    let tracked c = subtree.tracked_borrow_mut_child(i as int);
                    #[verus_spec(with Tracked(c), Tracked(guards), Tracked(regions))]
                    dfs_acquire_lock(guard, &mut pt_guard, child_node_va, va_start..va_end);
                }
                proof_with!(Tracked(guard_obl));
                let _ = ManuallyDrop::new(pt_guard);
                proof {
                    let ghost c2 = subtree.child(i as int);
                    PageTableOwner::<C>::metaregion_sound_preserved_slot_owners_eq_subtree(
                        t0,
                        root.path,
                        regions1,
                        *regions,
                    );
                    PageTableOwner::<C>::lemma_replace_child(t0, i as int, c2, *regions);
                    assert(*subtree == t0.insert(i as int, c2));
                    assert(subtree.child(i as int) == c2);
                    assert(c2.value() == c_inst.value());
                    assert forall|j: int| 0 <= j < NR_ENTRIES implies #[trigger] subtree.child(j).value().is_borrowed() == old(subtree).child(j).value().is_borrowed() by {
                        if j != i {
                            assert(subtree.child(j) == t0.child(j));
                        }
                    }
                    assert(c2.level() == subtree.level() + 1);
                    assert forall|j: int|
                        #![trigger subtree.child(j)]
                        s0 <= j < i + 1 && subtree.child(j).value().is_node() implies {
                            let cva = cur_node_va + j * ps;
                            &&& subtree.child(j).value().node().is_locked()
                            &&& dfs_locked_below(
                                subtree.child(j),
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
                        if j != i {
                            assert(subtree.child(j) == t0.child(j));
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
    proof {
        lemma_dfs_locked_flat(*subtree, *regions, cur_node_va, va_range);
    }
}

/// Every page-table node below `t` whose range overlaps `[va_start, va_end)` has
/// returned its lock cell: exactly the nodes `dfs_release_lock` unlocks.
pub open spec fn dfs_unlocked_below<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    node_va: int,
    va_start: int,
    va_end: int,
    depth: nat,
) -> bool
    decreases depth,
{
    depth > 0 && t.value().is_node() && t.value().node().level > 1 ==> {
        let ps = page_size(t.value().node().level) as int;
        forall|i: int|
            #![trigger t.child(i)]
            (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps) && t.child(
                i,
            ).value().is_node() ==> {
                let cva = node_va + i * ps;
                &&& !t.child(i).value().node().is_locked()
                &&& dfs_unlocked_below(
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

/// A subtree of held page table lock cells, as a [`flat_tree`] tree.
///
/// [`flat_tree`]: vstd_extra::resource::flat_tree
pub type PtLockedTree = LockedTree<PtLockPayload, NR_ENTRIES, NR_LEVELS>;

/// The lock cells held in `t`: the root node's cell and, below it, the cells of
/// the locked page-table nodes reachable from the root through locked nodes.
/// A node at paging level `level` is at flat-tree level `NR_LEVELS - level`;
/// `depth` is the root's paging level.
pub open spec fn locked_cells_at<C: PageTableConfig>(t: OwnerSubtree<C>, depth: nat) -> PtLockedTree
    decreases depth,
{
    PtLockedTree::new(
        t.value().node().cell(),
        (NR_LEVELS - t.value().node().level) as nat,
        Seq::new(
            NR_ENTRIES as nat,
            |i: int|
                if depth > 0 && t.has_child(i) && t.child(i).value().is_node() && t.child(
                    i,
                ).value().node().is_locked() {
                    Some(locked_cells_at(t.child(i), (depth - 1) as nat))
                } else {
                    None
                },
        ),
    )
}

/// [`locked_cells_at`] for a node subtree.
pub open spec fn locked_cells<C: PageTableConfig>(t: OwnerSubtree<C>) -> PtLockedTree {
    locked_cells_at(t, t.value().node().level as nat)
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
        let ps = page_size(t.value().value().pt_level) as int;
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

/// The key of a held node's lock cell is the node's physical address.
proof fn lemma_cell_key<C: PageTableConfig>(e: EntryOwner<C>, regions: MetaRegionOwners)
    requires
        e.metaregion_sound(regions),
        e.is_node(),
        e.node().is_locked(),
    ensures
        e.node().cell().key() == meta_to_frame(e.node().meta_vaddr()),
{
    reveal(lock_key_wf);
}

/// What a held node's lock cell says about child slot `i`: its PTE model
/// points to a child node exactly when the child entry is a node, and then to
/// the child's physical address.
proof fn lemma_cell_child_key<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    regions: MetaRegionOwners,
    i: int,
)
    requires
        PageTableOwner(t).pt_inv(),
        t.value().metaregion_sound(regions),
        t.value().is_node(),
        t.value().node().is_locked(),
        0 <= i < NR_ENTRIES,
        !t.child(i).value().is_borrowed(),
    ensures
        t.value().node().cell().value().pt_level == t.value().node().level,
        t.value().node().cell().value().child_key(i) == if t.child(i).value().is_node() {
            Some(meta_to_frame(t.child(i).value().node().meta_vaddr()))
        } else {
            None::<Paddr>
        },
{
    PageTableOwner(t).pt_inv_unroll(i);
    let node = t.value().node();
    let pte = node.children_perm.value()[i];
    reveal(PageTablePageMeta::lock_consts_wf);
    ostd_pod::lemma_decode_pod_inverse::<C::E>(pte);
    assert(node.pte_auth()@[i] == ostd_pod::pod_bytes(pte));
    if t.child(i).value().is_node() {
        assert(t.child(i).value().node().inv());
    }
}

/// The lock cells held in a node subtree form a well-formed flat tree.
proof fn lemma_locked_cells_wf<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    regions: MetaRegionOwners,
    depth: nat,
)
    requires
        PageTableOwner(t).pt_inv(),
        PageTableOwner(t).metaregion_sound(regions),
        t.value().is_node(),
        t.value().node().is_locked(),
        depth == t.value().node().level,
    ensures
        locked_cells_at(t, depth).inv(),
        tree_wf_at(locked_cells_at(t, depth), depth),
    decreases depth,
{
    let lt = locked_cells_at(t, depth);
    let node = t.value().node();
    let lvl = (NR_LEVELS - node.level) as nat;
    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::la_inv(t.value(), t.level()));
    assert(t.value().metaregion_sound(regions));
    reveal(PageTablePageMeta::lock_consts_wf);
    lemma_count_where_pte_bytes::<C::E>(
        node.children_perm.value(),
        node.children_perm.value().len() as int,
    );
    assert(lt.value() == node.cell());
    assert(lt.level() == lvl);
    assert(lt.value().inv_cell());
    assert forall|i: int|
        #![trigger lt.children()[i]]
        0 <= i < NR_ENTRIES && lt.has_child(i) implies {
            &&& t.has_child(i)
            &&& lt.child(i) == locked_cells_at(t.child(i), (depth - 1) as nat)
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
        lemma_cell_child_key(t, regions, i);
        lemma_cell_key(c.value(), regions);
        lemma_locked_cells_wf(c, regions, (depth - 1) as nat);
    }
    if node.level == 1 {
        assert forall|i: int| 0 <= i < NR_ENTRIES implies !(#[trigger] lt.children()[i] is Some) by {
            if lt.has_child(i) {
                PageTableOwner(t).pt_inv_unroll(i);
                assert(t.child(i).value().node().inv());
            }
        }
    }
    assert(lt.inv_children());
    assert(lt.inv());
}

/// The lock cells held in a node subtree in which [`dfs_acquire_lock`] has
/// locked a range form a flat tree that is complete over the range.
proof fn lemma_locked_cells_complete<C: PageTableConfig>(
    t: OwnerSubtree<C>,
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
        t.value().node().is_locked(),
        depth == t.value().node().level,
        dfs_locked_below(t, node_va, va_start, va_end, (INC_LEVELS - t.level()) as nat),
        forall|i: int|
            0 <= i < NR_ENTRIES ==> !(#[trigger] t.child(i)).value().is_borrowed() || !((va_start
                - node_va) / (page_size(t.value().node().level) as int) <= i < ceil_div(
                va_end - node_va,
                page_size(t.value().node().level) as int,
            )),
    ensures
        locked_complete_in_range(locked_cells_at(t, depth), node_va, va_start, va_end, depth),
    decreases depth,
{
    let lt = locked_cells_at(t, depth);
    let node = t.value().node();
    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::la_inv(t.value(), t.level()));
    assert(t.value().metaregion_sound(regions));
    reveal(PageTablePageMeta::lock_consts_wf);
    assert(lt.value() == node.cell());
    if node.level > 1 {
        let ps = page_size(node.level) as int;
        assert(lt.value().value().pt_level == node.level);
        assert forall|i: int|
            #![trigger lt.children()[i]]
            0 <= i < NR_ENTRIES && (va_start - node_va) / ps <= i < ceil_div(va_end - node_va, ps)
                implies {
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
            lemma_cell_child_key(t, regions, i);
            if c.value().is_node() {
                let cva = node_va + i * ps;
                assert(c.value().node().inv());
                assert(c.value().node().is_locked());
                assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] c.child(j)).value().is_borrowed() by {
                    PageTableOwner(c).pt_inv_unroll(j);
                }
                lemma_locked_cells_complete(
                    c,
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

/// [`dfs_acquire_lock`]'s postcondition, restated as a [`flat_tree`] tree:
/// if the root is locked, the held cells form a well-formed tree that is
/// complete over the range.
///
/// [`flat_tree`]: vstd_extra::resource::flat_tree
pub open spec fn dfs_locked_flat<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    node_va: Vaddr,
    va_range: Range<Vaddr>,
) -> bool {
    t.value().node().is_locked() ==> {
        &&& tree_wf(locked_cells(t))
        &&& locked_complete_in_range(
            locked_cells(t),
            node_va as int,
            va_range.start as int,
            va_range.end as int,
            t.value().node().level as nat,
        )
    }
}

proof fn lemma_dfs_locked_flat<C: PageTableConfig>(
    t: OwnerSubtree<C>,
    regions: MetaRegionOwners,
    node_va: Vaddr,
    va_range: Range<Vaddr>,
)
    requires
        PageTableOwner(t).pt_inv(),
        PageTableOwner(t).metaregion_sound(regions),
        t.value().is_node(),
        dfs_range_ok(t.value().node().level, node_va, va_range),
        dfs_locked_below(
            t,
            node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - t.level()) as nat,
        ),
        forall|i: int| 0 <= i < NR_ENTRIES ==> !(#[trigger] t.child(i)).value().is_borrowed()
            || !(idx_range_spec(t.value().node().level, node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(t.value().node().level, node_va, va_range.start, va_range.end).1),
    ensures
        dfs_locked_flat(t, node_va, va_range),
{
    if t.value().node().is_locked() {
        let depth = t.value().node().level as nat;
        lemma_idx_range_spec_exact(t.value().node().level, node_va, va_range);
        lemma_locked_cells_wf(t, regions, depth);
        lemma_locked_cells_complete(
            t,
            regions,
            depth,
            node_va as int,
            va_range.start as int,
            va_range.end as int,
        );
        assert(locked_cells(t).level() == NR_LEVELS - t.value().node().level);
    }
}

/// The root value of `t` with its node's lock cell returned.
pub open spec fn unlocked_root<C: PageTableConfig>(e: EntryOwner<C>) -> EntryOwner<C> {
    EntryOwner { kind: EntryOwnerKind::Node(NodeOwner { lock_cell: None, ..e.node() }), ..e }
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
/// - The root and every page-table node below it that overlaps the range hold
///   their lock cells ([`dfs_locked_below`]), as [`dfs_acquire_lock`] left them.
/// - `cur_node` has been redeemed from the [`Guards`] ledger: `obl` is its drop
///   obligation.
/// - The range is within the node's range (see [`dfs_range_ok`]).
/// ## Postconditions
/// - The root and every page-table node below it that overlaps the range have
///   returned their cells to their locks ([`dfs_unlocked_below`]).
/// - The guards made for the children are redeemed, so `guards` is unchanged.
#[verus_spec(
    with Tracked(subtree): Tracked<&mut OwnerSubtree<C>>,
        Tracked(guards): Tracked<&mut Guards<'rcu>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(obl): Tracked<DropObligation<usize>>
    requires
        PageTableOwner(*old(subtree)).pt_inv(),
        PageTableOwner(*old(subtree)).metaregion_sound(*old(regions)),
        old(subtree).value().is_node(),
        old(subtree).value().node().is_locked(),
        old(subtree).value().node().relate_guard(cur_node),
        obl.value() == old(subtree).value().node().meta_vaddr(),
        children_unguarded(*old(subtree), *old(guards)),
        dfs_range_ok(old(subtree).value().node().level, cur_node_va, va_range),
        // Borrowed (shared) entries only occur at the top level, and the range
        // stays clear of them.
        forall|i: int| 0 <= i < NR_ENTRIES ==> !(#[trigger] old(subtree).child(i)).value().is_borrowed()
            || !(idx_range_spec(old(subtree).value().node().level, cur_node_va, va_range.start, va_range.end).0 <= i
                < idx_range_spec(old(subtree).value().node().level, cur_node_va, va_range.start, va_range.end).1),
        dfs_locked_below(
            *old(subtree),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - old(subtree).level()) as nat,
        ),
        old(regions).inv(),
    ensures
        PageTableOwner(*final(subtree)).pt_inv(),
        PageTableOwner(*final(subtree)).metaregion_sound(*final(regions)),
        final(subtree).value() == unlocked_root(old(subtree).value()),
        final(subtree).level() == old(subtree).level(),
        dfs_unlocked_below(
            *final(subtree),
            cur_node_va as int,
            va_range.start as int,
            va_range.end as int,
            (INC_LEVELS - final(subtree).level()) as nat,
        ),
        *final(guards) == *old(guards),
        final(regions).inv(),
        final(regions).slot_owners == old(regions).slot_owners,
        forall|k: int| old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(k),
        forall|k: int| old(regions).slots.contains_key(k) ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
)]
#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
unsafe fn dfs_release_lock<'rcu, C: PageTableConfig, A: InAtomicMode>(
    guard: &'rcu A,
    mut cur_node: PageTableGuard<'rcu, C>,
    cur_node_va: Vaddr,
    va_range: Range<Vaddr>,
) {
    let ghost root = subtree.value();
    proof {
        assert(regions.contains(root.node().slot_index));
    }
    let cur_level = {
        let tracked node_owner = subtree.tracked_borrow_value().tracked_borrow_node();
        #[verus_spec(with Tracked(node_owner), Tracked(&*regions))]
        cur_node.level()
    };
    if cur_level == 1 {
        // Upstream, `cur_node` is dropped here, which unlocks it.
        let ghost t0 = *subtree;
        {
            let tracked node_owner = subtree.tracked_borrow_mut_value().tracked_borrow_mut_node();
            #[verus_spec(with Tracked(node_owner), Tracked(&*regions), Tracked(obl))]
            cur_node.unlock();
        }
        proof {
            PageTableOwner::<C>::lemma_replace_root_value(t0, *subtree, *regions);
        }
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let ghost s0 = idx_range.start as int;
    let ghost e0 = idx_range.end as int;
    let ghost ps = page_size(cur_level) as int;
    proof {
        lemma_idx_range_spec_exact(cur_level, cur_node_va, va_range);
    }
    let ghost depth = (INC_LEVELS - subtree.level()) as nat;
    let ghost old_children = subtree.children();
    let ghost guards0 = *guards;
    let ghost regions0 = *regions;
    let start = idx_range.start;
    // `for i in idx_range.rev()` upstream.
    let mut i = idx_range.end;
    while i > start
        invariant
            s0 <= i <= e0 <= NR_ENTRIES,
            start == s0,
            root.node().relate_guard(cur_node),
            cur_level == root.node().level,
            ps == page_size(cur_level) as int,
            depth == INC_LEVELS - subtree.level(),
            PageTableOwner(*subtree).pt_inv(),
            PageTableOwner(*subtree).metaregion_sound(*regions),
            subtree.value() == root,
            subtree.level() == old(subtree).level(),
            *guards == guards0,
            guards0 == *old(guards),
            regions0 == *old(regions),
            root == old(subtree).value(),
            old_children == old(subtree).children(),
            regions.inv(),
            regions.slot_owners == regions0.slot_owners,
            forall|k: int| regions0.slots.contains_key(k) ==> #[trigger] regions.slots.contains_key(k),
            forall|k: int| regions0.slots.contains_key(k) ==> regions0.slots[k] == #[trigger] regions.slots[k],
            forall|j: int| 0 <= j < i ==> #[trigger] subtree.children()[j] == old_children[j],
            forall|j: int|
                #![trigger subtree.child(j)]
                i <= j < e0 && subtree.child(j).value().is_node() ==> {
                    let cva = cur_node_va + j * ps;
                    &&& !subtree.child(j).value().node().is_locked()
                    &&& dfs_unlocked_below(
                        subtree.child(j),
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
            assert(subtree.child(i as int) == old(subtree).child(i as int));
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
            #[verus_spec(with Tracked(parent_owner), Tracked(child_owner), Tracked(&*regions))]
            cur_node.entry(i)
        };
        let child_ref = {
            let tracked parent_owner = subtree.tracked_borrow_value().tracked_borrow_node();
            let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value();
            #[verus_spec(with Tracked(child_owner), Tracked(parent_owner), Tracked(regions))]
            child.to_ref()
        };
        proof {
            PageTableOwner::<C>::metaregion_sound_preserved_slot_owners_eq_subtree(
                *subtree,
                root.path,
                regions_i,
                *regions,
            );
        }
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost t0 = *subtree;
                let ghost regions1 = *regions;
                let ghost path_i = root.path.push_tail(i as int);
                proof {
                    t0.lemma_subtree_satisfies_unroll_once(
                        root.path,
                        PageTableOwner::<C>::metaregion_sound_pred(regions1),
                        i as int,
                    );
                    assert(old(subtree).has_child(i as int));
                    assert(child0.subtree_satisfies(path_i, node_unguarded::<C>(guards0)));
                    assert(guards0.unlocked(child0.value().node().meta_vaddr()));
                    lemma_dfs_child_range(cur_level, cur_node_va, va_range, i as int);
                }
                proof_decl! {
                    let tracked child_obl: DropObligation<usize>;
                }
                // SAFETY: The caller ensures that the node is locked and the new guard is unique.
                let child_node = unsafe {
                    let tracked child_owner = subtree.tracked_borrow_child(i as int).tracked_borrow_value().tracked_borrow_node();
                    #[verus_spec(with Tracked(child_owner), Tracked(guards))]
                    pt.make_guard_unchecked(guard)
                };
                let ghost guards1 = *guards;
                proof {
                    child_obl = child_node.tracked_redeem(guards);
                    assert forall|x: usize| #[trigger] guards.guards.contains(x) == guards0.guards.contains(x) by {
                        if guards0.lock_held(x) {
                            assert(guards1.lock_held(x));
                        } else {
                            assert(guards0.unlocked(x));
                        }
                    }
                    assert(guards.guards =~= guards0.guards);
                    // No node below the child has a guard.
                    assert forall|j: int|
                        0 <= j < NR_ENTRIES && #[trigger] child0.has_child(j) implies child0.child(j).subtree_satisfies(
                        child0.value().path.push_tail(j),
                        node_unguarded::<C>(*guards),
                    ) by {
                        child0.lemma_subtree_satisfies_unroll_once(
                            path_i,
                            node_unguarded::<C>(guards0),
                            j,
                        );
                    }
                    // Below the top level, no entry is borrowed.
                    assert forall|j: int| 0 <= j < NR_ENTRIES implies !(#[trigger] child0.child(j)).value().is_borrowed() by {
                        PageTableOwner(child0).pt_inv_unroll(j);
                    }
                }
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = va_range.start.max(child_node_va);
                let va_end = va_range.end.min(child_node_va_end);
                let ghost c_inst = subtree.child(i as int);
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
                    let tracked c = subtree.tracked_borrow_mut_child(i as int);
                    #[verus_spec(with Tracked(c), Tracked(guards), Tracked(regions), Tracked(child_obl))]
                    dfs_release_lock(guard, child_node, child_node_va, va_start..va_end)
                };
                proof {
                    let ghost c2 = subtree.child(i as int);
                    PageTableOwner::<C>::metaregion_sound_preserved_slot_owners_eq_subtree(
                        t0,
                        root.path,
                        regions1,
                        *regions,
                    );
                    PageTableOwner::<C>::lemma_replace_child(t0, i as int, c2, *regions);
                    assert(*subtree == t0.insert(i as int, c2));
                    assert(subtree.child(i as int) == c2);
                    assert(c2.level() == subtree.level() + 1);
                    assert forall|j: int|
                        #![trigger subtree.child(j)]
                        i <= j < e0 && subtree.child(j).value().is_node() implies {
                            let cva = cur_node_va + j * ps;
                            &&& !subtree.child(j).value().node().is_locked()
                            &&& dfs_unlocked_below(
                                subtree.child(j),
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
                        if j != i {
                            assert(subtree.child(j) == t0.child(j));
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
    // Upstream, `cur_node` is dropped here, which unlocks it.
    let ghost t1 = *subtree;
    {
        let tracked node_owner = subtree.tracked_borrow_mut_value().tracked_borrow_mut_node();
        #[verus_spec(with Tracked(node_owner), Tracked(&*regions), Tracked(obl))]
        cur_node.unlock();
    }
    proof {
        PageTableOwner::<C>::lemma_replace_root_value(t1, *subtree, *regions);
        assert forall|j: int|
            #![trigger subtree.child(j)]
            s0 <= j < e0 && subtree.child(j).value().is_node() implies {
                let cva = cur_node_va + j * ps;
                &&& !subtree.child(j).value().node().is_locked()
                &&& dfs_unlocked_below(
                    subtree.child(j),
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
            assert(subtree.child(j) == t1.child(j));
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
        Tracked(guards): Tracked<&mut Guards<'a>>,
        Ghost(locked_addr): Ghost<usize>,
        Ghost(subtree_mappings_count): Ghost<nat>
    requires
        old(owner).inv(),
        // The locked_addr must be the address that was locked (held in guards)
        old(guards).lock_held(locked_addr),
    ensures
        // The return value equals the number of mappings in the subtree.
        // This connects the physical DFS frame count to the ghost view_rec mappings count.
        res as nat == subtree_mappings_count,
        final(owner).inv(),
        final(owner).guard_level == old(owner).guard_level,
        final(owner).level == old(owner).level,
        final(owner).va == old(owner).va,
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
    let ps = page_size(cur_node_level) as int;
    let start_idx = (va_start - cur_node_va) / ps;
    let end_idx = ceil_div(va_end - cur_node_va, ps);
    (start_idx as usize, end_idx as usize)
}

#[verus_spec(ret =>
    requires
        1 <= cur_node_level <= NR_LEVELS,
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((cur_node_level + 1) as PagingLevel),
        cur_node_va % page_size((cur_node_level + 1) as PagingLevel) == 0,
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
    let ps = page_size(cur_node_level);
    let diff = va_range.end - cur_node_va;

    proof {
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        use vstd::arithmetic::div_mod::*;
        lemma_page_size_ge_page_size(cur_node_level);
        lemma_page_size_spec_values();
        lemma_nr_entries_times_sub_page_size((cur_node_level + 1) as PagingLevel);

        // diff + ps - 1 fits in usize: both <= page_size(5) = 2^48
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
        // diff <= page_size(level+1) = NR_ENTRIES * ps
        // So ceil_div(diff, ps) <= NR_ENTRIES.
        let psu = page_size((cur_node_level + 1) as PagingLevel) as int;
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
