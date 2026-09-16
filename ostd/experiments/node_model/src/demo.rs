//! A worked example: how the node API composes.
//!
//! Nothing here mirrors a specific function in the real code. It exists to
//! show, in one place, how the pieces of `crate::node` are meant to be used
//! and how ownership is threaded through a sequence of calls — which is what
//! `page_table::cursor` does at scale.
//!
//! The contrast with the pre-fractional version of this file is the point:
//! every operation used to need four tracked arguments (`owner`,
//! `parent_owner`, `regions`, `guards`). Now the parent's ownership rides in
//! the `&mut PageTableGuard` and the child's rides in the `EntryOwner`, so
//! only one tracked argument is left.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::*;
use crate::node::PageTableGuard;
use crate::node::child::*;
use crate::node::entry_owners::*;
use crate::node::frac::*;
use crate::pte::Pte;

verus! {

/// Descends one level: look at entry `idx` of the locked node `guard`, and if
/// it is absent, allocate a child node there and return its guard.
///
/// The returned guard holds the child's `NodeOwner` outright, so the caller
/// may immediately write PTEs into it — and the child's `EntryOwner`, left
/// behind in `owner`, records that its authority is currently lent out.
#[verus_spec(res =>
    with Tracked(owner): Tracked<&mut EntryOwner>,
    requires
        old(entry_at).invariants(*old(owner)),
        old(entry_at).node.owner@.settled(),
    ensures
        final(entry_at).invariants(*final(owner)),
        final(entry_at).node.owner@.settled(),
        res is Some <==> (old(owner).is_absent() && old(entry_at).node.owner@.level > 1),
        old(owner).is_absent() && old(entry_at).node.owner@.level > 1 ==> {
            &&& final(owner).is_node()
            &&& final(owner).node().level() == old(entry_at).node.owner@.level - 1
            &&& res->0.wf()
            &&& res->0@.meta_own.nr_children.value() == 0
            &&& forall|i: int| 0 <= i < NR_ENTRIES
                ==> #[trigger] res->0@.children_perm.value()[i] == Pte::new_absent_spec()
        },
)]
pub fn descend<'a, 'rcu>(entry_at: &mut crate::node::Entry<'a, 'rcu>) -> Option<
    PageTableGuard<'rcu>,
> {
    // Allocates, takes exclusive ownership of the new node, publishes the PTE,
    // and bumps `nr_children` — in that order, so the node is never reachable
    // through the page table while someone else could touch it.
    #[verus_spec(with Tracked(owner))]
    entry_at.alloc_if_none()
}

/// Reads an entry without taking ownership of anything, and reports what kind
/// of child it holds.
///
/// Contrast with [`descend`]: this only *lends* a fraction, so the child stays
/// shared and the caller gets a `ChildRef` it can read through.
#[verus_spec(res =>
    with Tracked(owner): Tracked<&mut EntryOwner>,
    requires
        entry_at.invariants(*old(owner)),
        old(owner).is_node() ==> {
            &&& !old(owner).node().is_lent_out()
            &&& old(owner).node().frac() > 1
        },
    ensures
        res.invariants(*final(owner)),
        res is None <==> final(owner).is_absent(),
        res is PageTable <==> final(owner).is_node(),
)]
pub fn peek<'a, 'rcu>(entry_at: &crate::node::Entry<'a, 'rcu>) -> ChildRef<'rcu> {
    #[verus_spec(with Tracked(owner))]
    entry_at.to_ref()
}

} // verus!
