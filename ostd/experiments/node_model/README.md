# `node_model` — a tiny model of the page table node layer

A self-contained, fully verified miniature of `ostd/src/mm/page_table/node` +
`ostd/specs/mm/page_table/node`, with the `frame` layer beneath it stubbed out.
It exists to be *read*: ~3000 lines instead of ~5400 of node code sitting on
~16000 lines of dependencies.

```
cargo dv verify --targets node_model     # 100 obligations, 0 errors, ~2s
cargo dv fmt    --targets node_model
```

It is a separate workspace member and is **not** in the `Makefile`'s
`VERIFICATION_TARGETS`, so it does not slow down `make`.

The build emits 45 `#[verus_spec] is likely used inside a verus! block`
warnings. These are expected: the `with Tracked(...)` clause is a
`#[verus_spec]` feature, and the real node code puts its `#[verus_verify] impl`
blocks inside `verus! { ... }` in exactly the same way.

## Ownership model: fractional permissions

The model departs from the real code in one deliberate, load-bearing way: node
ownership is **fractional**, built on
`vstd_extra::resource::ghost_resource::count_auth` (the same construction
`ostd/src/sync/rwlock.rs` uses in production).

| Token | Who holds it | What it licenses |
| --- | --- | --- |
| [`NodeFrac`] | a `PageTableNodeRef` | **reading** the node |
| [`NodeAuth`] | the parent's `EntryOwner` | lending fractions; reclaiming them |
| `NodeOwner` (outright) | a `PageTableGuard` | **writing** a PTE |

A guard is obtainable only via `NodeAuth::into_exclusive`, which requires every
outstanding fraction to have come home. So *"only the guard can write a PTE"*
is a consequence of the ownership algebra, not a convention — and mutual
exclusion is proved rather than asserted wherever the authority is in hand.

Three properties are checked by deliberately breaking them (each reintroduces
exactly one error):

- a guard cannot be formed while a fraction is still outstanding;
- a `ChildRef` cannot be produced when no spare fraction exists;
- `settled()` genuinely depends on the present-PTE counting lemma.

### What this replaced

The previous design threaded a central `MetaRegionOwners` through every call
and recorded locks in a `Guards` ghost set. That is all gone:

| Removed | Why it is no longer needed |
| --- | --- |
| `MetaRegionOwners`, `MetaSlotOwner` | the slot's `PointsTo` now lives in `NodeOwner` |
| `meta_bridge`, `metaregion_sound_node`, `metaregion_sound` | those clauses are just part of `NodeOwner::inv()` now |
| `PageUsage`, `REF_COUNT_UNUSED`/`MAX` | node/frame distinctness came from these tags; linearity gives it instead |
| `Guards` ghost lock-set | a lock *is* holding every fraction |

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

`NodeAuth` keeps the node's `slot_index` and `level` in ghost fields *outside*
the resource, so a node stays identifiable while a guard holds it. Without
that, a locked child would make its parent's `match_pte` meaningless.

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
| `node/owners.rs` | `specs/mm/page_table/node/owners.rs` |
| `node/entry_owners.rs` | `specs/mm/page_table/node/entry_owners.rs` |
| `node/mod.rs` | `src/.../node/mod.rs` + `specs/.../node/mod.rs` |
| `node/child.rs` | `src/.../node/child.rs` + `specs/.../node/child.rs` |
| `node/entry.rs` | `src/.../node/entry.rs` + `specs/.../node/entry.rs` |
| `demo.rs` | *(new)* worked example of how the API composes |

## What is kept faithfully

- **Three handle types**, with the read/write split now enforced by the types.
- **Two-location addressing.** A handle stores the frame's *metadata slot*
  address; a PTE stores its *physical* address. The round-trip lemmas are
  *proven*.
- **`count_present` and its five lemmas**, so the `nr_children ± 1` bookkeeping
  in `replace` is proven not to under/overflow.
- **`inv()` vs `settled()`.** `count_consistent` is *not* in `inv()`, because
  `replace` momentarily breaks it between the counter update and the PTE write.
  Since `inv()` is exactly what a `NodeFrac` carries, keeping it out means a
  fraction never promises something a mid-flight node cannot deliver.
- **`match_pte`** — the case split relating a PTE to what its owner claims.
- **Lock-before-publish.** `alloc_if_none` allocates, takes exclusive
  ownership, *then* writes the PTE.

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
| `pte.rs` — `load_pte`, `store_pte` | Compile to relaxed/release atomics. |
| `node/mod.rs` — `PageTableNode::alloc` | Calls the frame allocator. Notably it can no longer say anything about any *other* node. |
| `node/mod.rs` — `PageTableNodeRef::lock` | The concurrent path; see below. |

There are no `assume(...)` or `admit()` anywhere.

### The one honest gap: `lock`

Building a guard needs every fraction home, but a thread calling `lock()` does
not hold the other references' fractions — re-gathering them is not something
the node layer can do by itself. The model therefore offers both routes:

- `PageTableNodeRef::lock` — **axiomatised**, the realistic concurrent API. The
  axiom is now a statement about *ownership* ("the protocol brought every
  fraction home") rather than about a ghost set.
- `PageTableNodeRef::into_guard` — **proved**, for when the caller does hold
  the authority, as a cursor owning its whole path does. `Entry::alloc_if_none`
  uses this route, so allocating a child and locking it needs **no axiom at
  all** — the old model reached for `lock()` there.

Closing the gap properly means modelling the atomic lock word with an
invariant, as `rwlock.rs` does. That is a substantially larger piece of work
and would pull the whole `vstd` atomic-invariant machinery into a model whose
purpose is to stay small.

## Where to start reading

1. `node/frac.rs` — `NodeFrac` / `NodeAuth`; the whole ownership story.
2. `node/owners.rs` — `NodeOwner`, and the `inv()` / `settled()` split.
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
