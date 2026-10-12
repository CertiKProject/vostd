# `dfs_mark_stray_and_unlock`: stray as a postcondition

Date: 2026-10-12. Branch: `jacob/locking-admits`.

This replaces the earlier `parents_stray` precondition (commit `9d30e8c0d`),
which was too strong and passed the wrong ghost state.

## Ghost parameters

Before, the function took the global owner map plus the root's address:

```rust
with Ghost(pa): Ghost<Paddr>,
     Tracked(owners): Tracked<&mut Map<Paddr, EntryOwner<'a, C>>>,
     Tracked(regions): Tracked<&mut MetaRegionOwners>
```

Now it takes the owner *sub-tree* it works on, following the hand-written
branches (`jcob/locking`, `certik/phaseII/verified`), which hand each function
the owner structure of the node it operates on rather than a global map:

```rust
with Tracked(owner): Tracked<&mut OwnerNode<'a, C>>,
     Tracked(regions): Tracked<&mut MetaRegionOwners>
```

`OwnerNode` is the node type of the existing `PageTableOwner` tree,
`Node<OwnerInTree<'rcu, C>, CONST_NR_ENTRIES, CONST_NR_LEVELS>`. Owning the
sub-tree is exclusive by construction, so no uniqueness invariant
(`unique_parent`) and no condition on the rest of the page table is needed.

## Preconditions

Only shape and ownership:

- `subtree_wf(*old(owner), *old(regions), level)`: every node is owned and
  agrees with the region, and child `i` of a node is exactly the sub-tree its
  entry `i` points to, one level down.
- The root's guard permission is the guard being unlocked.
- `config_is_x86_64::<C>()` and `regions.inv()`.

Nothing about stray flags is required. `parents_stray` and
`unique_parent` are gone.

## Postcondition

```rust
node_owner(*owner).is_stray(),
stray_propagates(*owner, level),
subtree_wf(*owner, *regions, level),
```

`stray_propagates(n, lv)`: if the root of `n` is stray, every child is stray
and itself satisfies `stray_propagates`. Together with the root being stray,
this says the whole detached sub-tree is stray: every node marked stray has
its children marked stray. The shape (`subtree_wf`) and the root's guard, slot
permission and level are preserved.

## How it is built: loop invariant

The function marks the root stray first, then iterates `i` over the 512
entries. The invariant splits the children at `i`:

- `j >= i`: `owner.children[j] == old_root.children[j]` (not yet visited).
- `j < i`: the child is present iff it was before, and if present it has the
  right address, is `subtree_wf` one level down, is stray, and satisfies
  `stray_propagates`.

Each iteration takes child `i` out of the tree (`tracked_take_child`),
recurses on it, and puts it back (`tracked_put_child`); the recursive call's
postcondition extends the `j < i` half by one. At `i == 512` the second half
covers all children, which is exactly `stray_propagates` and `subtree_wf` for
the root.

## Supporting additions

- `vstd_extra/src/ghost_tree.rs`: `tracked_borrow_child`, `tracked_take_child`,
  `tracked_put_child`, and path-based `has_path`/`node_at`/`set_at` with
  tracked `borrow_at`/`take_at`/`put_at` and `lemma_set_at`.
- `lemma_owner_frame` in `locking.rs`: the frame facts of a single owner that
  agrees with the region.

## Scope

Only `dfs_mark_stray_and_unlock` moved to the sub-tree interface. The other
protocol functions still thread the owner map; its invariant `owners_wf` no
longer contains `unique_parent`. The caller, `replace_cur_entry`, is
`external_body` and does not yet construct the sub-tree it passes.
