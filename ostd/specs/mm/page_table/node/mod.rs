pub mod entry_owners;
pub mod owners;

use vstd::prelude::*;
use vstd_extra::{cast_ptr::Repr, drop_tracking::*};

use crate::specs::mm::frame::meta_owners::{
    MetaSlotStorage, PtLockCell, PtLockConst, StoredPageTablePageMeta,
};

use crate::mm::{
    frame::Frame,
    page_table::{PageTableConfig, PageTableGuard, PageTablePageMeta},
};
use core::marker::PhantomData;
pub use entry_owners::*;
pub use owners::*;

verus! {

/// This thread's lock state, as ghost bookkeeping.
///
/// - `guards`: the nodes that have a live [`PageTableGuard`].
/// - `held`: the nodes whose lock cell this thread holds, with each cell's
///   [`LockConst`](vstd_extra::resource::flat_tree::LockConst). A node can be
///   held without a guard: [`dfs_acquire_lock`] forgets the guards of the
///   nodes it locks.
///
/// The cells themselves are tracked elsewhere (by the cursor, or by whoever
/// locked the node), in a map that [`Self::cells_wf`] relates to `held`.
/// Keeping `Guards` purely ghost means that writing to a held cell does not
/// change it, so predicates over `Guards` survive such writes unchanged.
///
/// [`dfs_acquire_lock`]: crate::mm::page_table::cursor::locking
pub tracked struct Guards {
    pub ghost guards: Set<usize>,
    pub ghost held: Map<usize, PtLockConst>,
}

impl Guards {
    pub open spec fn unlocked(self, addr: usize) -> bool {
        !self.guards.contains(addr)
    }

    pub open spec fn lock_held(self, addr: usize) -> bool {
        self.guards.contains(addr)
    }

    /// This thread holds the lock cell of the node at `addr`, whose lock has
    /// constant `k`.
    pub open spec fn holds(self, addr: usize, k: PtLockConst) -> bool {
        &&& self.held.contains_key(addr)
        &&& self.held[addr] == k
    }

    /// `cells` are exactly the held cells, and each is ready to be unlocked.
    pub open spec fn cells_wf(self, cells: Map<usize, PtLockCell>) -> bool {
        &&& cells.dom() == self.held.dom()
        &&& forall|a: usize| #[trigger]
            cells.contains_key(a) ==> {
                &&& cells[a].lock_const() == self.held[a]
                &&& cells[a].inv_cell()
            }
    }

    /// Putting back a held cell, after writing to it, keeps [`Self::cells_wf`].
    pub proof fn lemma_cells_wf_replace(
        self,
        cells: Map<usize, PtLockCell>,
        a: usize,
        c: PtLockCell,
    )
        requires
            self.cells_wf(cells),
            cells.contains_key(a),
            c.lock_const() == cells[a].lock_const(),
            c.inv_cell(),
        ensures
            self.cells_wf(cells.insert(a, c)),
            cells.remove(a).insert(a, c) == cells.insert(a, c),
    {
        assert(cells.insert(a, c).dom() =~= cells.dom());
        assert(cells.remove(a).insert(a, c) =~= cells.insert(a, c));
    }

    /// Adding the cell of a node just locked keeps [`Self::cells_wf`].
    pub proof fn lemma_cells_wf_insert(
        self,
        g1: Guards,
        cells: Map<usize, PtLockCell>,
        a: usize,
        c: PtLockCell,
    )
        requires
            self.cells_wf(cells),
            g1.held == self.held.insert(a, c.lock_const()),
            c.inv_cell(),
        ensures
            g1.cells_wf(cells.insert(a, c)),
    {
        assert(cells.insert(a, c).dom() =~= g1.held.dom());
    }
}

impl<'rcu, C: PageTableConfig> TrackDrop for PageTableGuard<'rcu, C> {
    type State = Guards;

    /// The node address whose lock this guard holds. The token
    /// thus identifies *which* guard it tracks; `drop_requires`'s key
    /// match prevents a guard's obligation from being used to drop a
    /// different guard. The real lock-set ledger is `Guards::guards`;
    /// this trait's discipline lifts the existing state-side discipline
    /// onto the obligation token by carrying the locked address.
    type Obligation = DropObligation<usize>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        s.lock_held(self.inner.slot_vaddr())
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.guards == s0.guards.remove(self.inner.slot_vaddr())
        &&& s1.held == s0.held
        &&& obl.value() == self.inner.slot_vaddr()
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        s.guards = s.guards.remove(self.inner.slot_vaddr());
        DropObligation::tracked_mint(self.inner.slot_vaddr())
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& s.unlocked(self.inner.slot_vaddr())
        &&& obl.value() == self.inner.slot_vaddr()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.guards == s0.guards.insert(self.inner.slot_vaddr())
        &&& s1.held == s0.held
    }
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    /// The lock is well-formed and guards the permissions of this node's metadata cells.
    pub open spec fn lock_wf(self) -> bool {
        &&& self.lock.well_formed()
        &&& self.lock.constant().consts.nr_children_id == self.nr_children.id()
        &&& self.lock.constant().consts.stray_id == self.stray.id()
        &&& self.lock_consts_wf()
        &&& self.lock.constant().consts.is_present == (|r: usize| raw_is_present::<C::E>(r))
    }

    /// The parts of the lock constant used only by `flat_tree` reasoning: the
    /// node's level, its flat-tree depth, and how its PTEs name child nodes.
    /// Opaque, as most proofs about page table metadata do not need them.
    #[verifier::opaque]
    pub open spec fn lock_consts_wf(self) -> bool {
        &&& self.lock.constant().consts.pt_level == self.level
        &&& self.lock.constant().level == crate::specs::arch::NR_LEVELS - self.level
        &&& self.lock.constant().consts.child_of == raw_child_of_fn::<C::E>()
    }

    pub open spec fn into_spec(self) -> StoredPageTablePageMeta {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> StoredPageTablePageMeta
        returns
            self.into_spec(),
    {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl StoredPageTablePageMeta {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> PageTablePageMeta<C>
        returns
            self.into_spec::<C>(),
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

pub uninterp spec fn drop_tree_spec<C: PageTableConfig>(
    _page: Frame<PageTablePageMeta<C>>,
) -> Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> Repr<MetaSlotStorage> for PageTablePageMeta<C> {
    open spec fn wf(r: MetaSlotStorage) -> bool {
        matches!(r, MetaSlotStorage::PTNode(_))
    }

    open spec fn from_repr_spec(r: MetaSlotStorage) -> Self {
        match r {
            MetaSlotStorage::PTNode(node) => node.into::<C>(),
            _ => arbitrary(),
        }
    }

    fn to_repr(self) -> MetaSlotStorage {
        MetaSlotStorage::PTNode(self.into())
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed_mut<'a>(r: &'a mut MetaSlotStorage) -> &'a mut Self {
        unimplemented!()
    }
}

} // verus!
