# `node_model` — a tiny model of the page table node layer

A self-contained, fully verified miniature of `ostd/src/mm/page_table/node` +
`ostd/specs/mm/page_table/node`, with the `frame` layer beneath it stubbed out.
It exists to be *read*: ~3000 lines instead of ~5400 of node code sitting on
~16000 lines of dependencies.

```
cargo dv verify --targets node_model     # 99 obligations, 0 errors, ~2s
cargo dv fmt    --targets node_model
```

It is a separate workspace member and is **not** in the `Makefile`'s
`VERIFICATION_TARGETS`, so it does not slow down `make`.

The build emits 45 `#[verus_spec] is likely used inside a verus! block`
warnings. These are expected: the `with Tracked(...)` clause is a
`#[verus_spec]` feature, and the real node code puts its `#[verus_verify] impl`
blocks inside `verus! { ... }` in exactly the same way.

## Ownership model: readers and a writer

The model departs from the real code in one deliberate, load-bearing way: node
ownership is split into **readers** and a **writer**, built on
`vstd_extra::resource::ghost_resource::count_auth` (the same construction
`ostd/src/sync/rwlock.rs` uses in production) and a `vstd` `AtomicInvariant`.

| Token | Who holds it | What it licenses |
| --- | --- | --- |
| [`NodeFrac`] (reader) | a `PageTableNodeRef`, and a `PageTableGuard` | naming the node, reading its level, reading PTEs *up to* `pte_wf` |
| [`NodeWriter`] (writer) | a `PageTableGuard` | writing PTEs and `nr_children`; knowing the node's *exact* contents |
| [`NodeAuth`] (core) | the parent's `EntryOwner` | lending readers; parking the writer while the node is unlocked |

Readers coexist with the writer, as RCU readers coexist with a locked node in
Asterinas. Mutual exclusion between *writers* is just the uniqueness of the
writer token.

A node's ownership is split by how each part changes:

- **`NodeIdentity`** — never changes: the metadata slot's `PointsTo`, the
  level, the slot index, and the PTE array's atomic invariant. This is what
  the reader fractions agree on. Because it is immutable, a write never has to
  be propagated to the readers.
- **`PteArray`**, inside the atomic invariant — the PTE array's `PointsTo`,
  plus one half of a ghost variable mirroring its contents. Readers and the
  writer both open the invariant around a single atomic `load_pte` /
  `store_pte`. The invariant's predicate, `pte_wf`, is all a reader learns:
  every PTE has a valid frame address, an absent PTE above level 1 is not
  marked as a leaf, and there are no leaves at the top level.
- **`NodeWriter`** — the `PCell` permissions for `nr_children` and `stray`,
  and the authoritative half of that ghost variable, which is how a guard
  knows the exact array between openings.

`NodeOwner` survives as the *unpacked* bundle that the frame allocator hands
back for a fresh node; `NodeAuth::alloc` packs it.

Four properties are checked by deliberately breaking them (each reintroduces
exactly one error):

- a guard cannot be formed while the writer is lent out;
- a `ChildRef` cannot be produced when no spare reader fraction exists;
- `write_pte` cannot store a PTE that violates `pte_wf`, because concurrent
  readers are promised it;
- `settled()` genuinely depends on the present-PTE counting lemma.

### What this replaced

The previous design threaded a central `MetaRegionOwners` through every call
and recorded locks in a `Guards` ghost set. That is all gone:

| Removed | Why it is no longer needed |
| --- | --- |
| `MetaRegionOwners`, `MetaSlotOwner` | the slot's `PointsTo` now lives in `NodeOwner` |
| `meta_bridge`, `metaregion_sound_node`, `metaregion_sound` | those clauses are just part of `NodeOwner::inv()` now |
| `PageUsage`, `REF_COUNT_UNUSED`/`MAX` | node/frame distinctness came from these tags; linearity gives it instead |
| `Guards` ghost lock-set | a lock *is* holding the writer |

Two consequences are worth calling out:

- **The parent ≠ child obligation disappeared rather than being re-proved.**
  Under a central region, allocating mutated a shared map, so callers had to
  show the parent's slot was not the one that moved. With permissions held
  locally, allocation simply cannot touch the parent's `NodeOwner` — it is a
  different tracked object.
- **Handing out a reference became a mutation.** `Entry::to_ref` and
  `ChildRef::from_pte` take `&mut EntryOwner`, because lending a fraction
  changes the authority. Under the old design this was a shared read of a
  global map, which is precisely why nothing stopped references appearing from
  nowhere.

The identity resource stays in `NodeAuth` while a guard holds the writer, so
a locked child is still identifiable and its parent's `match_pte` stays
meaningful.

## Why this is a rewrite and not an extraction

A verbatim copy of the node sources is not possible. Their dependency closure
is essentially the whole `mm` tree:

- `specs::mm::page_table::owners::{PageTableOwner, OwnerSubtree, Guards,
  CursorOwner}` and `specs::mm::page_table::cursor::page_size_lemmas` — the
  node layer depends *upward* on cursor-level specs;
- `mm::VmReader` / `specs::mm::io::VmIoOwner` / `specs::mm::virt_mem::MemView`
  plus `ostd_pod` — the whole `PageTablePageMeta::on_drop` byte-walk;
- `frame::meta::{MetaSlot, mapping}` and `specs::mm::frame::*`;
- `page_table::{PageTableConfig, PageTableEntryTrait}` — 1857 lines of trait
  with heavy `pow2` address arithmetic.

## Layout

| Model | Real counterpart |
| --- | --- |
| `arch.rs` | `specs/arch/x86`, `mm::{Paddr, Vaddr, PagingLevel}`, `kspace` |
| `page_prop.rs` | `mm::page_prop` |
| `pte.rs` | `PageTableEntryTrait` (i.e. `C::E`), `load_pte`/`store_pte` |
| `frame/mapping.rs` | `frame::meta::mapping`, `specs::mm::frame::mapping` |
| `frame/mod.rs` | `mm::frame::Frame` — now just a typed address |
| `node/frac.rs` | *(new)* `NodeFrac` / `NodeAuth`, the ownership currency |
| `node/owners.rs` | `specs/mm/page_table/node/owners.rs`, plus `NodeIdentity`, `NodeWriter`, `PteArray`, `pte_wf` |
| `node/entry_owners.rs` | `specs/mm/page_table/node/entry_owners.rs` |
| `node/mod.rs` | `src/.../node/mod.rs` + `specs/.../node/mod.rs` |
| `node/child.rs` | `src/.../node/child.rs` + `specs/.../node/child.rs` |
| `node/entry.rs` | `src/.../node/entry.rs` + `specs/.../node/entry.rs` |
| `demo.rs` | *(new)* worked example of how the API composes |

## What is kept faithfully

- **Three handle types**, with the read/write split now enforced by the types.
- **Lock-free readers.** A `PageTableNodeRef` can read a node that some
  guard holds locked; it just learns less than the guard does.
- **Two-location addressing.** A handle stores the frame's *metadata slot*
  address; a PTE stores its *physical* address. The round-trip lemmas are
  *proven*.
- **`count_present` and its five lemmas**, so the `nr_children ± 1` bookkeeping
  in `replace` is proven not to under/overflow.
- **`wf_for()` vs `settled()`.** `settled()` is *not* in
  `NodeWriter::wf_for()`, because `replace` momentarily breaks it between the
  counter update and the PTE write. A writer parked in `NodeAuth` is always
  settled, so a guard obtained from the core starts settled, and `unlock`
  requires the guard to be settled again.
- **`match_pte`** — the case split relating a PTE to what its owner claims.
- **Lock-before-publish.** `alloc_if_none` allocates, takes the new
  node's writer, *then* writes the PTE.

## What is stubbed, and how

| Dropped | Consequence |
| --- | --- |
| `PageTableConfig` / `PageTableEntryTrait` | Monomorphic. `Pte` is a transparent struct, so the PTE laws are *provable* rather than axiomatised. |
| `vstd_extra::ghost_tree` | `EntryOwner` has no `path`; removes the upward dependency on cursor specs. |
| `PageTablePageMeta::on_drop` | The recursive teardown walk, and with it `VmReader`, `MemView`, `ostd_pod`. |
| `vstd_extra::drop_tracking` | No `frame_obligations` ledger. |
| Atomic refcount, `UniqueFrame`, segments, linked lists, allocator, MMIO | Replaced by the fractional tokens. |
| `EntryOwner::Borrowed` | Meaningless with one page-table configuration. |

Constants keep their real values (`PAGE_SIZE = 4096`, `NR_ENTRIES = 512`,
`NR_LEVELS = 4`, `MAX_PADDR = 0x8000_0000`, `META_SLOT_SIZE = 64`) except the
two region bases, shrunk to keep the SMT arithmetic cheap.

## The four axioms

Down from six: `Frame::from_raw` and `FrameRef::borrow_paddr` are no longer
axioms, because reconstructing a *handle* from an address is pure arithmetic
once the handle carries no authority of its own.

| Site | Why |
| --- | --- |
| `pte.rs` — `load_pte`, `store_pte` | Compile to relaxed/release atomics. Marked `#[verifier::atomic]` so they can run inside the PTE invariant. |
| `node/mod.rs` — `PageTableNode::alloc` | Calls the frame allocator. Notably it can no longer say anything about any *other* node. |
| `node/mod.rs` — `PageTableNodeRef::lock` | The concurrent path; see below. |

There are no `assume(...)` or `admit()` anywhere.

### The one honest gap: `lock`

A thread calling `lock()` does not hold the node's core, so it cannot take the
writer from it. The model therefore offers both routes:

- `PageTableNodeRef::lock` — **axiomatised**, the realistic concurrent API. The
  axiom says the lock protocol hands over the node's unique writer, and that
  the node is settled. It promises nothing about the exact contents beyond
  what the writer then reveals.
- `PageTableNodeRef::into_guard` — **proved**, for when the caller does hold
  the core, as a cursor owning its whole path does. It no longer requires the
  other readers to come home first. `Entry::alloc_if_none` gets the writer
  straight from `NodeAuth::alloc`, so allocating a child and locking it needs
  **no axiom at all**.

Closing the gap properly means storing the writer in an atomic invariant on
the lock word, as `rwlock.rs` does. Then `lock()` takes it out on a
successful compare-and-swap and `unlock()` puts it back on release.

## Where to start reading

1. `node/frac.rs` — `NodeFrac` / `NodeAuth`; the whole ownership story.
2. `node/owners.rs` — `NodeIdentity` / `PteArray` / `NodeWriter`, `pte_wf`,
   and the `wf_for()` / `settled()` split.
3. `node/entry_owners.rs` — `match_pte`, and why the parent entry owns the
   child's authority.
4. `node/child.rs` — `into_pte` / `from_pte`, and why only the *borrowing*
   conversion needs `&mut`.
5. `node/entry.rs` — `replace` and `alloc_if_none`.
6. `demo.rs` — the two composed, the way `cursor` would.

## Known gaps

Modelled from `entry.rs`: `is_none`, `is_node`, `to_ref`, `replace`,
`alloc_if_none`. Not modelled: `protect` / `protect_child`,
`split_if_mapped_huge`, `replace_child`, `alloc_absent_child`,
`replace_absent_with_frame`. `split_if_mapped_huge` remains the one that would
most stress the model, since it splits a huge-page item across 512 child
entries.

### Open issue: RCU reclamation

The model is deliberately **non-RCU**. A node can be freed only once every
reader fraction has been explicitly returned to its authority, and a detached
(`stray`) node simply waits for its readers to hand their fractions back.

Real Asterinas does not work this way. A `PageTableNodeRef<'rcu>` is an RCU
reference: readers never return anything explicitly, and a detached node is
reclaimed only after a grace period has elapsed. Modelling that faithfully
would need a token, or an axiom, standing for "the grace period has passed,
so every outstanding fraction of this node is dead". This is left open.
