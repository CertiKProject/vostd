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
//! Proof obligations are discharged with `admit()` for now. The
//! specifications record what must be proven once the proof effort starts.
use core::{marker::PhantomData, ops::Range, sync::atomic::Ordering};

use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::array_ptr::*;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use crate::mm::{
    nr_subpage_per_huge, paddr_to_vaddr,
    page_table::{
        load_pte, pte_index, pte_index_spec, ChildRef, PageTable, PageTableConfig,
        PageTableEntryTrait, PageTableGuard, PageTableNodeRef, PagingConstsTrait, PagingLevel,
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
/// Every page-table configuration verified in this tree uses the x86-64
/// paging constants. The generic code is written against `C`, so this is the
/// bridge between `C`'s constants and the concrete ones used by the
/// arithmetic lemmas.
pub proof fn lemma_config_is_x86_64<C: PageTableConfig>()
    ensures
        C::NR_LEVELS() == NR_LEVELS() as PagingLevel,
        C::BASE_PAGE_SIZE() == PAGE_SIZE(),
        nr_subpage_per_huge::<C>() == nr_subpage_per_huge::<PagingConsts>(),
        nr_subpage_per_huge::<C>() == NR_ENTRIES(),
        NR_LEVELS() == 4,
        NR_ENTRIES() == 512,
        PAGE_SIZE() == 4096,
        PagingConsts::NR_LEVELS() == 4,
        PagingConsts::BASE_PAGE_SIZE() == 4096,
{
    admit();
}

/// A range that a cursor may lock: non-empty and page aligned.
pub open spec fn lockable_range(va: Range<Vaddr>) -> bool {
    &&& va.start < va.end
    &&& va.start % PAGE_SIZE() == 0
    &&& va.end % PAGE_SIZE() == 0
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

/// The level recorded in the metadata of the node that `own` owns.
pub open spec fn owner_level<'rcu, C: PageTableConfig>(own: EntryOwner<'rcu, C>) -> PagingLevel {
    own.node_own.meta_perm@.value().level
}

/// Whether the node that `own` owns has been detached from its parent.
pub open spec fn owner_stray<'rcu, C: PageTableConfig>(own: EntryOwner<'rcu, C>) -> bool {
    own.node_own.meta_own.stray@.value()
}

/// The physical address of the node that `own` owns.
pub open spec fn owner_paddr<'rcu, C: PageTableConfig>(own: EntryOwner<'rcu, C>) -> Paddr {
    meta_to_frame(own.slot_perm@.pptr().addr())
}

/// `owners` is a consistent ownership map: every owner is well formed and is
/// filed under the physical address of the node it owns.
pub open spec fn owners_wf<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
) -> bool {
    forall|pa: Paddr| #[trigger]
        owners.contains_key(pa) ==> owners[pa].inv() && owner_paddr(owners[pa]) == pa
}

/// The owner filed under `pa` holds the permission for the guard pointer
/// `guard`, i.e. `pa` is the node that `guard` locks.
pub open spec fn owns_guard<'rcu, C: PageTableConfig>(
    owners: Map<Paddr, EntryOwner<'rcu, C>>,
    pa: Paddr,
    guard: PPtr<PageTableGuard<'rcu, C>>,
) -> bool {
    &&& owners.contains_key(pa)
    &&& owners[pa].guard_perm@.pptr() == guard
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
    &&& !owner_stray(owners[pa])
    &&& 1 <= owner_level(owners[pa]) <= C::NR_LEVELS()
    &&& node_covers_range::<C>(owner_level(owners[pa]), va)
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

// ---------------------------------------------------------------------------
// The protocol.
// ---------------------------------------------------------------------------
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
        lockable_range(*va),
        old(regions).inv(),
        owners_wf(*old(owners)),
        old(owners).contains_key(pt.root.paddr()),
    ensures
        cursor_locked_at(cursor, guard, *va),
        exists|pa: Paddr| #[trigger]
            owns_guard(*owners, pa, cursor.path[cursor.guard_level - 1].unwrap()),
        owners_wf(*owners),
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
            lockable_range(*va),
            regions.inv(),
            owners_wf(*owners),
            owners.contains_key(pt.root.paddr()),
        ensures
            subtree_root_opt is Some,
            subtree_root_opt matches Some(subtree_root) ==> exists|pa: Paddr| #[trigger]
                covering_node_locked(*owners, pa, subtree_root, *va),
            regions.inv(),
            owners_wf(*owners),
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
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
    let tracked root_own = owners.tracked_remove(root_pa);

    assert(regions.slot_owners.contains_key(frame_to_index(root_pa))) by { admit() };
    let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(root_pa));
    assert(root_own.relate_slot_owner(slot_own)) by { admit() };

    let subtree_guard = subtree_root.borrow(Tracked(root_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(slot_own), Tracked(root_own.slot_perm.borrow()), Tracked(root_own.node_own.meta_perm.borrow()))]
    let guard_level = subtree_guard.level();

    proof {
        lemma_page_size_next_level(guard_level);
    }
    assert(page_size((guard_level + 1) as PagingLevel) > 0) by { admit() };
    let cur_node_va = align_down(va.start, page_size((guard_level + 1) as PagingLevel));

    // TODO: the covering node's range contains `va`, and `cur_node_va` is its
    // start; both follow from `covering_node_locked` and `align_down`.
    assert(cur_node_va == node_start_va(va.start, guard_level) && va.end <= cur_node_va + page_size(
        (guard_level + 1) as PagingLevel,
    )) by { admit() };

    #[verus_spec(with Tracked(&root_own), Tracked(owners), Tracked(regions))]
    dfs_acquire_lock(guard, subtree_root, cur_node_va, va.clone());

    proof {
        owners.tracked_insert(root_pa, root_own);
    }
    // TODO: the re-filed owner is well formed and filed under its own address.
    assert(owners_wf(*owners)) by { admit() };

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
    assert(cursor_locked_at(cursor, guard, *va)) by { admit() };
    assert(owns_guard(*owners, root_pa, subtree_root)) by { admit() };
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
        1 <= old(cursor).level <= old(cursor).guard_level <= C::NR_LEVELS(),
        old(cursor).path[old(cursor).guard_level - 1] is Some,
        lockable_range(old(cursor).barrier_va),
        exists|pa: Paddr| #[trigger]
            owns_guard(*old(owners), pa, old(cursor).path[old(cursor).guard_level - 1].unwrap()),
        owners_wf(*old(owners)),
        old(regions).inv(),
    ensures
        forall|i: int| 0 <= i < MAX_NR_LEVELS() ==> cursor.path[i] is None,
        cursor.guard_level == old(cursor).guard_level,
        cursor.barrier_va == old(cursor).barrier_va,
        owners_wf(*owners),
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
        decreases end - i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
        cursor.path.set(i, None);
        i = i + 1;
    }
    let guard_node = match cursor.path[end] {
        Some(guard_node) => guard_node,
        None => unreached(),
    };
    cursor.path.set(end, None);

    proof {
        lemma_page_size_next_level(cursor.guard_level);
    }
    assert(page_size((cursor.guard_level + 1) as PagingLevel) > 0) by { admit() };
    let cur_node_va = align_down(
        cursor.barrier_va.start,
        page_size((cursor.guard_level + 1) as PagingLevel),
    );

    let ghost root_pa = choose|pa: Paddr| owns_guard(*owners, pa, guard_node);
    let tracked root_own = owners.tracked_remove(root_pa);

    // TODO: the guard node is live and covers the barrier range; this is the
    // part of `cursor_locked_at` that the cursor must keep as its invariant.
    assert(!owner_stray(root_own) && 1 <= owner_level(root_own) <= C::NR_LEVELS() && cur_node_va
        == node_start_va(cursor.barrier_va.start, owner_level(root_own)) && cursor.barrier_va.end
        <= cur_node_va + page_size((owner_level(root_own) + 1) as PagingLevel)) by { admit() };

    // A cursor maintains that its corresponding sub-tree is locked.
    #[verus_spec(with Tracked(&root_own), Tracked(owners), Tracked(regions))]
    dfs_release_lock(cursor.rcu_guard, guard_node, cur_node_va, cursor.barrier_va.clone());

    // Dropping the guard node's guard releases its lock.
    #[verus_spec(with Tracked(&root_own))]
    PageTableGuard::<'rcu, C>::unlock(guard_node);

    proof {
        owners.tracked_insert(root_pa, root_own);
    }
    // TODO: the re-filed owner is well formed and filed under its own address.
    assert(owners_wf(*owners)) by { admit() };
    assert(forall|i: int| 0 <= i < MAX_NR_LEVELS() ==> cursor.path[i] is None) by { admit() };
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
        lockable_range(*va),
        old(regions).inv(),
        owners_wf(*old(owners)),
        old(owners).contains_key(pt.root.paddr()),
    ensures
        regions.inv(),
        owners_wf(*owners),
        owners.contains_key(pt.root.paddr()),
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
        let tracked root_own = owners.tracked_borrow(root_pa);
        assert(regions.slot_owners.contains_key(frame_to_index(root_pa))) by { admit() };
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(root_pa));
        assert(root_own.relate_slot_owner(slot_own) && root_own.slot_perm@.pptr() == pt.root.ptr)
            by { admit() };
        #[verus_spec(with Tracked(slot_own), Tracked(root_own.slot_perm.borrow()))]
        let root_paddr = pt.root.start_paddr();
        root_paddr
    };

    // Walk from the top level down to level 1 (`(1..=NR_LEVELS).rev()`).
    let mut cur_level: PagingLevel = C::NR_LEVELS();
    while cur_level >= 1
        invariant
            cur_level <= C::NR_LEVELS(),
            C::NR_LEVELS() == 4,
            nr_subpage_per_huge::<C>() == 512,
            lockable_range(*va),
            regions.inv(),
            owners_wf(*owners),
            owners.contains_key(root_pa),
            root_pa == pt.root.paddr(),
        decreases cur_level,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
        let level = cur_level;
        cur_level = cur_level - 1;

        let start_idx = pte_index::<C>(va.start, level);
        let level_too_high = {
            let end_idx = pte_index::<C>(va.end - 1, level);
            level > 1 && start_idx == end_idx
        };
        if !level_too_high {
            break;
        }
        assert(cur_pt_addr < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()) by { admit() };
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
            cur_pt_addr = cur_pte.paddr();
            cur_node_guard = None;
            continue;
        }
        // In case the child is absent, we should lock and allocate a new page table node.

        let node_pa = cur_pt_addr;
        let pt_guard = match cur_node_guard {
            Some(pt_guard) => pt_guard,
            None => {
                assert(owners.contains_key(node_pa)) by { admit() };
                assert(node_pa % PAGE_SIZE() == 0 && node_pa < MAX_PADDR()
                    && !regions.slots.contains_key(frame_to_index(node_pa))
                    && regions.dropped_slots.contains_key(frame_to_index(node_pa))) by { admit() };
                // SAFETY: The node must be alive for at least `'rcu` since the
                // address is read from the page table node.
                #[verus_spec(with Tracked(regions))]
                let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(node_pa);
                // TODO: `borrow_paddr` does not yet state that it preserves the region invariant.
                assert(regions.inv()) by { admit() };
                let tracked node_own = owners.tracked_borrow(node_pa);
                assert(node_own.guard_perm@.value().inner.inner.ptr == node_ref.inner.ptr) by {
                    admit()
                };
                #[verus_spec(with Tracked(node_own))]
                let locked = node_ref.lock(guard);
                locked
            },
        };

        assert(owners.contains_key(node_pa)) by { admit() };
        let tracked mut cur_own = owners.tracked_remove(node_pa);
        assert(regions.slot_owners.contains_key(frame_to_index(node_pa))) by { admit() };
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(node_pa));
        assert(cur_own.guard_perm@.pptr() == pt_guard && cur_own.relate_slot_owner(slot_own)) by {
            admit()
        };

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
                owners.tracked_insert(node_pa, cur_own);
            }
            // TODO: the re-filed owner is well formed and filed under its own address.
            assert(owners_wf(*owners)) by { admit() };
            return None;
        }
        #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
        let mut cur_entry = PageTableGuard::<'rcu, C>::entry(pt_guard, start_idx);
        if cur_entry.is_none() {
            assert(cur_entry.wf(&cur_own)) by { admit() };
            let tracked mut new_child_own: Option<EntryOwner<'rcu, C>> = None;
            #[verus_spec(with Tracked(&mut cur_own), Tracked(regions), Tracked(&mut new_child_own))]
            let allocated = cur_entry.alloc_if_none(guard);
            match allocated {
                Some(allocated_guard) => {
                    let tracked child_own = new_child_own.tracked_unwrap();
                    let ghost child_pa = owner_paddr(child_own);
                    assert(regions.slot_owners.contains_key(frame_to_index(child_pa))) by { admit()
                    };
                    let tracked child_slot_own = regions.slot_owners.tracked_borrow(
                        frame_to_index(child_pa),
                    );
                    assert(child_own.relate_slot_owner(child_slot_own)) by { admit() };
                    let child_guard = allocated_guard.borrow(
                        Tracked(child_own.guard_perm.borrow()),
                    );
                    #[verus_spec(with Tracked(child_slot_own), Tracked(child_own.slot_perm.borrow()))]
                    let child_paddr = child_guard.start_paddr();
                    cur_pt_addr = child_paddr;
                    cur_node_guard = Some(allocated_guard);
                    proof {
                        owners.tracked_insert(child_pa, child_own);
                    }
                    // TODO: the re-filed owner is well formed and filed under its own address.
                    assert(owners_wf(*owners)) by { admit() };
                },
                None => {
                    // `alloc_if_none` only fails if the entry is present or the
                    // node is a leaf; neither holds here (`is_none` and `level > 1`).
                    proof {
                        admit();
                    }
                    unreached()
                },
            }
        } else {
            assert(cur_entry.wf(&cur_own)) by { admit() };
            #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
            let is_node = cur_entry.is_node();
            if is_node {
                // TODO: `to_ref` asks for the entry's frame bookkeeping.
                assert(cur_entry.pte.paddr() == meta_to_frame(cur_own.slot_perm@.addr())
                    && cur_own.slot_perm@.value().wf(
                    &regions.slot_owners[frame_to_index(cur_entry.pte.paddr())],
                ) && regions.dropped_slots.contains_key(frame_to_index(cur_entry.pte.paddr()))
                    && !regions.slots.contains_key(frame_to_index(cur_entry.pte.paddr()))) by {
                    admit()
                };
                #[verus_spec(with Tracked(&cur_own), Tracked(regions))]
                let child_ref = cur_entry.to_ref();
                // TODO: `to_ref` does not yet state that it preserves the region invariant.
                assert(regions.inv()) by { admit() };
                match child_ref {
                    ChildRef::PageTable(pt_ref) => {
                        let ghost child_pa = pt_ref.inner.paddr();
                        assert(owners.contains_key(child_pa) && regions.slot_owners.contains_key(
                            frame_to_index(child_pa),
                        )) by { admit() };
                        let tracked child_own = owners.tracked_borrow(child_pa);
                        let tracked child_slot_own = regions.slot_owners.tracked_borrow(
                            frame_to_index(child_pa),
                        );
                        assert(child_own.relate_slot_owner(child_slot_own)
                            && child_own.slot_perm@.pptr() == pt_ref.inner.ptr) by { admit() };
                        #[verus_spec(with Tracked(child_slot_own), Tracked(child_own.slot_perm.borrow()))]
                        let child_paddr = pt_ref.start_paddr();
                        cur_pt_addr = child_paddr;
                        cur_node_guard = None;
                    },
                    ChildRef::Frame(_, _, _) | ChildRef::None => {
                        // `is_node` guarantees a page-table child.
                        proof {
                            admit();
                        }
                        unreached()
                    },
                }
            } else {
                // A (huge) page is mapped here: this node is the covering node.
                // Its guard is dropped (unlocked) now and re-acquired below.
                #[verus_spec(with Tracked(&cur_own))]
                PageTableGuard::<'rcu, C>::unlock(pt_guard);
                proof {
                    owners.tracked_insert(node_pa, cur_own);
                }
                // TODO: the re-filed owner is well formed and filed under its own address.
                assert(owners_wf(*owners)) by { admit() };
                break;
            }
        }
        // The guard of the node we came from goes out of scope here, which
        // releases its lock. Only the newly allocated child (if any) stays
        // locked through `cur_node_guard`.
        #[verus_spec(with Tracked(&cur_own))]
        PageTableGuard::<'rcu, C>::unlock(pt_guard);
        proof {
            owners.tracked_insert(node_pa, cur_own);
        }
        // TODO: the re-filed owner is well formed and filed under its own address.
        assert(owners_wf(*owners)) by { admit() };
    }

    let node_pa = cur_pt_addr;
    let pt_guard = match cur_node_guard {
        Some(pt_guard) => pt_guard,
        None => {
            assert(owners.contains_key(node_pa)) by { admit() };
            assert(node_pa % PAGE_SIZE() == 0 && node_pa < MAX_PADDR()
                && !regions.slots.contains_key(frame_to_index(node_pa))
                && regions.dropped_slots.contains_key(frame_to_index(node_pa))) by { admit() };
            // SAFETY: The node must be alive for at least `'rcu` since the
            // address is read from the page table node.
            #[verus_spec(with Tracked(regions))]
            let node_ref = PageTableNodeRef::<'rcu, C>::borrow_paddr(node_pa);
            // TODO: `borrow_paddr` does not yet state that it preserves the region invariant.
            assert(regions.inv()) by { admit() };
            let tracked node_own = owners.tracked_borrow(node_pa);
            assert(node_own.guard_perm@.value().inner.inner.ptr == node_ref.inner.ptr) by { admit()
            };
            #[verus_spec(with Tracked(node_own))]
            let locked = node_ref.lock(guard);
            locked
        },
    };

    assert(owners.contains_key(node_pa)) by { admit() };
    let tracked cur_own = owners.tracked_remove(node_pa);
    assert(regions.slot_owners.contains_key(frame_to_index(node_pa))) by { admit() };
    let tracked slot_own = regions.slot_owners.tracked_borrow(frame_to_index(node_pa));
    assert(cur_own.guard_perm@.pptr() == pt_guard && cur_own.relate_slot_owner(slot_own)) by {
        admit()
    };

    let guard_val = pt_guard.borrow(Tracked(cur_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(&cur_own), Tracked(slot_own))]
    let stray_cell = guard_val.stray_mut();
    let is_stray = *stray_cell.borrow(Tracked(cur_own.node_own.meta_own.stray.borrow()));
    if is_stray {
        #[verus_spec(with Tracked(&cur_own))]
        PageTableGuard::<'rcu, C>::unlock(pt_guard);
        proof {
            owners.tracked_insert(node_pa, cur_own);
        }
        // TODO: the re-filed owner is well formed and filed under its own address.
        assert(owners_wf(*owners)) by { admit() };
        return None;
    }
    proof {
        owners.tracked_insert(node_pa, cur_own);
    }
    // TODO: the re-filed owner is well formed and filed under its own address.
    assert(owners_wf(*owners)) by { admit() };
    // TODO: the node reached is the covering node of `va` (every level above
    // it put both ends of `va` in the same slot, by the loop's exit condition).
    assert(covering_node_locked(*owners, node_pa, pt_guard, *va)) by { admit() };
    Some(pt_guard)
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
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == cur_node,
        !owner_stray(*cur_own),
        1 <= owner_level(*cur_own) <= C::NR_LEVELS(),
        cur_node_va == node_start_va(va_range.start, owner_level(*cur_own)),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((owner_level(*cur_own) + 1) as PagingLevel),
        old(regions).inv(),
        owners_wf(*old(owners)),
    ensures
        regions.inv(),
        owners_wf(*owners),
    decreases owner_level(*cur_own),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    let cur_level = {
        let cur_guard = cur_node.borrow(Tracked(cur_own.guard_perm.borrow()));
        assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit()
        };
        let tracked slot_own = regions.slot_owners.tracked_borrow(
            frame_to_index(owner_paddr(*cur_own)),
        );
        assert(cur_own.relate_slot_owner(slot_own)) by { admit() };
        #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
        let level = cur_guard.level();
        level
    };
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let start = idx_range.start;
    let end = idx_range.end;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            end <= nr_subpage_per_huge::<C>(),
            nr_subpage_per_huge::<C>() == 512,
            1 < cur_level <= 4,
            cur_level == owner_level(*cur_own),
            cur_own.inv(),
            cur_own.guard_perm@.pptr() == cur_node,
            regions.inv(),
            owners_wf(*owners),
        decreases end - i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
        assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit()
        };
        let tracked slot_own = regions.slot_owners.tracked_borrow(
            frame_to_index(owner_paddr(*cur_own)),
        );
        assert(cur_own.relate_slot_owner(slot_own)) by { admit() };
        #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, i);

        // TODO: `to_ref` asks for the entry's frame bookkeeping.
        assert(child.wf(cur_own) && child.pte.paddr() == meta_to_frame(cur_own.slot_perm@.addr())
            && cur_own.slot_perm@.value().wf(
            &regions.slot_owners[frame_to_index(child.pte.paddr())],
        ) && regions.dropped_slots.contains_key(frame_to_index(child.pte.paddr()))
            && !regions.slots.contains_key(frame_to_index(child.pte.paddr()))) by { admit() };
        #[verus_spec(with Tracked(cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        // TODO: `to_ref` does not yet state that it preserves the region invariant.
        assert(regions.inv()) by { admit() };
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                assert(owners.contains_key(child_pa)) by { admit() };
                let tracked child_own = owners.tracked_remove(child_pa);
                assert(child_own.guard_perm@.value().inner.inner.ptr == pt.inner.ptr) by { admit()
                };
                #[verus_spec(with Tracked(&child_own))]
                let pt_guard = pt.lock(guard);

                assert(i * page_size(cur_level) + page_size(cur_level) + cur_node_va <= usize::MAX)
                    by { admit() };
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = if va_range.start > child_node_va {
                    va_range.start
                } else {
                    child_node_va
                };
                let va_end = if va_range.end < child_node_va_end {
                    va_range.end
                } else {
                    child_node_va_end
                };

                // TODO: the child is a live node one level down whose range is
                // `child_node_va..child_node_va_end`, and the clipped range is non-empty.
                assert(!owner_stray(child_own) && owner_level(child_own) == cur_level - 1
                    && child_node_va == node_start_va(va_start, owner_level(child_own)) && va_start
                    < va_end && va_end <= child_node_va + page_size(
                    (owner_level(child_own) + 1) as PagingLevel,
                )) by { admit() };
                #[verus_spec(with Tracked(&child_own), Tracked(owners), Tracked(regions))]
                dfs_acquire_lock(guard, pt_guard, child_node_va, va_start..va_end);

                // The child's guard is forgotten (`ManuallyDrop` in the original):
                // the child stays locked until `dfs_release_lock`.
                proof {
                    owners.tracked_insert(child_pa, child_own);
                }
                // TODO: the re-filed owner is well formed and filed under its own address.
                assert(owners_wf(*owners)) by { admit() };
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
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == cur_node,
        !owner_stray(*cur_own),
        1 <= owner_level(*cur_own) <= C::NR_LEVELS(),
        cur_node_va == node_start_va(va_range.start, owner_level(*cur_own)),
        cur_node_va <= va_range.start,
        va_range.start < va_range.end,
        va_range.end <= cur_node_va + page_size((owner_level(*cur_own) + 1) as PagingLevel),
        old(regions).inv(),
        owners_wf(*old(owners)),
    ensures
        regions.inv(),
        owners_wf(*owners),
    decreases owner_level(*cur_own),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    let cur_level = {
        let cur_guard = cur_node.borrow(Tracked(cur_own.guard_perm.borrow()));
        assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit()
        };
        let tracked slot_own = regions.slot_owners.tracked_borrow(
            frame_to_index(owner_paddr(*cur_own)),
        );
        assert(cur_own.relate_slot_owner(slot_own)) by { admit() };
        #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
        let level = cur_guard.level();
        level
    };
    if cur_level == 1 {
        return;
    }
    let idx_range = dfs_get_idx_range::<C>(cur_level, cur_node_va, &va_range);
    let start = idx_range.start;
    let end = idx_range.end;
    // Reverse order of acquisition.
    let mut i = end;
    while i > start
        invariant
            start <= i <= end,
            end <= nr_subpage_per_huge::<C>(),
            nr_subpage_per_huge::<C>() == 512,
            1 < cur_level <= 4,
            cur_level == owner_level(*cur_own),
            cur_own.inv(),
            cur_own.guard_perm@.pptr() == cur_node,
            regions.inv(),
            owners_wf(*owners),
        decreases i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
        i = i - 1;

        assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit()
        };
        let tracked slot_own = regions.slot_owners.tracked_borrow(
            frame_to_index(owner_paddr(*cur_own)),
        );
        assert(cur_own.relate_slot_owner(slot_own)) by { admit() };
        #[verus_spec(with Tracked(cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'rcu, C>::entry(cur_node, i);

        // TODO: `to_ref` asks for the entry's frame bookkeeping.
        assert(child.wf(cur_own) && child.pte.paddr() == meta_to_frame(cur_own.slot_perm@.addr())
            && cur_own.slot_perm@.value().wf(
            &regions.slot_owners[frame_to_index(child.pte.paddr())],
        ) && regions.dropped_slots.contains_key(frame_to_index(child.pte.paddr()))
            && !regions.slots.contains_key(frame_to_index(child.pte.paddr()))) by { admit() };
        #[verus_spec(with Tracked(cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        // TODO: `to_ref` does not yet state that it preserves the region invariant.
        assert(regions.inv()) by { admit() };
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                assert(owners.contains_key(child_pa)) by { admit() };
                let tracked child_own = owners.tracked_remove(child_pa);
                assert(child_own.guard_perm@.value().inner.inner.ptr == pt.inner.ptr) by { admit()
                };
                // The node is locked (by `dfs_acquire_lock`) and its guard was
                // forgotten, so re-creating the guard is unique.
                #[verus_spec(with Tracked(&child_own))]
                let child_node = pt.make_guard_unchecked(guard);

                assert(i * page_size(cur_level) + page_size(cur_level) + cur_node_va <= usize::MAX)
                    by { admit() };
                let child_node_va = cur_node_va + i * page_size(cur_level);
                let child_node_va_end = child_node_va + page_size(cur_level);
                let va_start = if va_range.start > child_node_va {
                    va_range.start
                } else {
                    child_node_va
                };
                let va_end = if va_range.end < child_node_va_end {
                    va_range.end
                } else {
                    child_node_va_end
                };

                // TODO: see `dfs_acquire_lock`.
                assert(!owner_stray(child_own) && owner_level(child_own) == cur_level - 1
                    && child_node_va == node_start_va(va_start, owner_level(child_own)) && va_start
                    < va_end && va_end <= child_node_va + page_size(
                    (owner_level(child_own) + 1) as PagingLevel,
                )) by { admit() };
                // All the nodes in the sub-tree are locked and all guards are forgotten.
                #[verus_spec(with Tracked(&child_own), Tracked(owners), Tracked(regions))]
                dfs_release_lock(guard, child_node, child_node_va, va_start..va_end);

                // Dropping the re-created guard releases the child's lock.
                #[verus_spec(with Tracked(&child_own))]
                PageTableGuard::<'rcu, C>::unlock(child_node);
                proof {
                    owners.tracked_insert(child_pa, child_own);
                }
                // TODO: the re-filed owner is well formed and filed under its own address.
                assert(owners_wf(*owners)) by { admit() };
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
        old(cur_own).inv(),
        old(cur_own).guard_perm@.pptr() == sub_tree,
        1 <= owner_level(*old(cur_own)) <= C::NR_LEVELS(),
        old(regions).inv(),
        owners_wf(*old(owners)),
    ensures
        cur_own.inv(),
        cur_own.guard_perm@.pptr() == sub_tree,
        owner_level(*cur_own) == owner_level(*old(cur_own)),
        owner_stray(*cur_own),
        regions.inv(),
        owners_wf(*owners),
    decreases owner_level(*old(cur_own)),
{
    proof {
        lemma_config_is_x86_64::<C>();
    }

    assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit() };
    let tracked slot_own = regions.slot_owners.tracked_borrow(
        frame_to_index(owner_paddr(*cur_own)),
    );
    assert(cur_own.relate_slot_owner(slot_own)) by { admit() };

    let sub_tree_val = sub_tree.borrow(Tracked(cur_own.guard_perm.borrow()));
    #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
    let stray_cell = sub_tree_val.stray_mut();
    let _was_stray = stray_cell.replace(
        Tracked(cur_own.node_own.meta_own.stray.borrow_mut()),
        true,
    );

    #[verus_spec(with Tracked(slot_own), Tracked(cur_own.slot_perm.borrow()), Tracked(cur_own.node_own.meta_perm.borrow()))]
    let level = sub_tree_val.level();
    if level == 1 {
        #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
        let nr_children = sub_tree_val.nr_children();
        // Dropping the guard releases the lock.
        #[verus_spec(with Tracked(&*cur_own))]
        PageTableGuard::<'a, C>::unlock(sub_tree);
        assert(cur_own.inv()) by { admit() };
        return nr_children as usize;
    }
    let mut num_frames: usize = 0;

    let end = nr_subpage_per_huge::<C>();
    let mut i: usize = 0;
    while i < end
        invariant
            i <= end,
            end == 512,
            1 < level <= 4,
            level == owner_level(*cur_own),
            owner_level(*cur_own) == owner_level(*old(cur_own)),
            cur_own.inv(),
            cur_own.guard_perm@.pptr() == sub_tree,
            owner_stray(*cur_own),
            regions.inv(),
            owners_wf(*owners),
        decreases end - i,
    {
        proof {
            lemma_config_is_x86_64::<C>();
        }
        assert(regions.slot_owners.contains_key(frame_to_index(owner_paddr(*cur_own)))) by { admit()
        };
        let tracked slot_own = regions.slot_owners.tracked_borrow(
            frame_to_index(owner_paddr(*cur_own)),
        );
        assert(cur_own.relate_slot_owner(slot_own)) by { admit() };
        #[verus_spec(with Tracked(&*cur_own), Tracked(slot_own))]
        let child = PageTableGuard::<'a, C>::entry(sub_tree, i);

        // TODO: `to_ref` asks for the entry's frame bookkeeping.
        assert(child.wf(&*cur_own) && child.pte.paddr() == meta_to_frame(cur_own.slot_perm@.addr())
            && cur_own.slot_perm@.value().wf(
            &regions.slot_owners[frame_to_index(child.pte.paddr())],
        ) && regions.dropped_slots.contains_key(frame_to_index(child.pte.paddr()))
            && !regions.slots.contains_key(frame_to_index(child.pte.paddr()))) by { admit() };
        #[verus_spec(with Tracked(&*cur_own), Tracked(regions))]
        let child_ref = child.to_ref();
        // TODO: `to_ref` does not yet state that it preserves the region invariant.
        assert(regions.inv()) by { admit() };
        match child_ref {
            ChildRef::PageTable(pt) => {
                let ghost child_pa = pt.inner.paddr();
                assert(owners.contains_key(child_pa)) by { admit() };
                let tracked mut child_own = owners.tracked_remove(child_pa);
                assert(child_own.guard_perm@.value().inner.inner.ptr == pt.inner.ptr) by { admit()
                };
                // The node is locked and the new guard is unique.
                #[verus_spec(with Tracked(&child_own))]
                let locked_pt = pt.make_guard_unchecked(rcu_guard);

                // TODO: the child is one level down.
                assert(owner_level(child_own) == level - 1) by { admit() };
                // All the nodes in the sub-tree are locked and all guards are forgotten.
                #[verus_spec(with Tracked(&mut child_own), Tracked(owners), Tracked(regions))]
                let frames_below = dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                assert(num_frames + frames_below <= usize::MAX) by { admit() };
                num_frames = num_frames + frames_below;
                proof {
                    owners.tracked_insert(child_pa, child_own);
                }
                // TODO: the re-filed owner is well formed and filed under its own address.
                assert(owners_wf(*owners)) by { admit() };
            },
            ChildRef::None | ChildRef::Frame(_, _, _) => {},
        }
        i = i + 1;
    }

    // Dropping the guard releases the lock of this node.
    #[verus_spec(with Tracked(&*cur_own))]
    PageTableGuard::<'a, C>::unlock(sub_tree);

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
