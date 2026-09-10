//! A worked example: how the node API composes.
//!
//! Nothing here mirrors a specific function in the real code. It exists to
//! show, in one place, how the pieces of `crate::node` are meant to be used
//! and how the ghost state is threaded through a sequence of calls — which is
//! what `page_table::cursor` does at scale.
//!
//! Read [`descend`] top to bottom: it is the one-step version of a page table
//! walk that creates missing nodes on the way down.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::frame::owners::*;
use crate::node::child::*;
use crate::node::entry_owners::*;
use crate::node::owners::*;
use crate::node::{PageTableGuard, Regions};
use crate::page_prop::PageProperty;
use crate::pte::Pte;

verus! {

/// Descends one level: look at entry `idx` of the locked node `guard`, and if
/// it is absent, allocate a child node there and return its guard.
///
/// The interesting part is the *ghost* argument list. Four tracked objects
/// have to travel alongside the one executable argument:
///
/// * `owner` — what entry `idx` currently is. Mutated in place: it starts
///   `Absent` and ends up `Node`.
/// * `parent_owner` — the permissions for the node being descended from. Its
///   PTE array and `nr_children` both change.
/// * `regions` — the global metadata region, which gains a live slot.
/// * `guards` — the lock ledger, which gains the new node's address.
///
/// Everything the caller needs to keep going down is in the postcondition:
/// the new entry is a node, its guard is returned, and its lock is held.
#[verus_spec(res =>
    with Tracked(owner): Tracked<&mut EntryOwner>,
         Tracked(parent_owner): Tracked<&mut NodeOwner>,
         Tracked(regions): Tracked<&mut Regions>,
         Tracked(guards): Tracked<&mut Guards<'rcu>>,
    requires
        old(regions).inv(),
        old(owner).inv(),
        old(parent_owner).inv(),
        old(parent_owner).relate_guard(*old(guard)),
        old(parent_owner).metaregion_sound_node(*old(regions)),
        old(parent_owner).level == old(owner).parent_level,
        old(owner).match_pte(old(parent_owner).children_perm.value()[idx as int],
            old(owner).parent_level),
        old(owner).metaregion_sound(*old(regions)),
        idx < NR_ENTRIES,
    ensures
        final(parent_owner).metaregion_sound_node(*final(regions)),
        res is Some <==> (old(owner).is_absent() && old(parent_owner).level > 1),
        old(owner).is_absent() && old(parent_owner).level > 1 ==> {
            &&& final(owner).is_node()
            &&& final(owner).node().level == old(parent_owner).level - 1
            &&& final(owner).node().meta_own.nr_children.value() == 0
            &&& final(guards).lock_held(final(owner).node().meta_vaddr())
            &&& final(owner).node().relate_guard(res->0)
        },
)]
pub fn descend<'rcu>(guard: &mut PageTableGuard<'rcu>, idx: usize) -> Option<PageTableGuard<'rcu>> {
    // Borrowing an entry reads the PTE out of the node's page once, and hands
    // back a handle that caches it.
    let mut entry = {
        #[verus_spec(with Tracked(&*parent_owner), Tracked(&*owner), Tracked(&*regions))]
        guard.entry(idx)
    };

    // If the slot is absent, this allocates a node, locks it, publishes the
    // PTE, and bumps `nr_children` — in that order, so the node is never
    // reachable through the page table while unlocked.
    #[verus_spec(with
        Tracked(owner),
        Tracked(parent_owner),
        Tracked(regions),
        Tracked(guards)
    )]
    entry.alloc_if_none()
}

/// Reads entry `idx` without taking ownership of anything, and reports what
/// kind of child it holds.
///
/// Contrast with [`descend`]: because nothing is taken out of the PTE, this
/// needs only `&Regions`, and the region is provably unchanged.
#[verus_spec(res =>
    with Tracked(owner): Tracked<&EntryOwner>,
         Tracked(parent_owner): Tracked<&NodeOwner>,
         Tracked(regions): Tracked<&Regions>,
    requires
        regions.inv(),
        owner.inv(),
        parent_owner.inv(),
        parent_owner.relate_guard(*guard),
        parent_owner.metaregion_sound_node(*regions),
        parent_owner.level == owner.parent_level,
        owner.match_pte(parent_owner.children_perm.value()[idx as int], owner.parent_level),
        owner.metaregion_sound(*regions),
        idx < NR_ENTRIES,
    ensures
        res.invariants(*owner, *regions),
        res is None <==> owner.is_absent(),
        res is PageTable <==> owner.is_node(),
)]
pub fn peek<'a, 'rcu>(guard: &'a mut PageTableGuard<'rcu>, idx: usize) -> ChildRef<'rcu> {
    let entry = {
        #[verus_spec(with Tracked(parent_owner), Tracked(owner), Tracked(regions))]
        guard.entry(idx)
    };
    #[verus_spec(with Tracked(owner), Tracked(parent_owner), Tracked(regions))]
    entry.to_ref()
}

} // verus!
