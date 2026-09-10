# `node_model` — a tiny model of the page table node layer

A self-contained, fully verified miniature of `ostd/src/mm/page_table/node` +
`ostd/specs/mm/page_table/node`, with the `frame` layer beneath it stubbed out.
It exists to be *read*: ~2900 lines instead of ~5400 of node code sitting on
~16000 lines of dependencies.

```
cargo dv verify --targets node_model     # 85 obligations, 0 errors, ~1.5s
cargo dv fmt    --targets node_model
```

It is a separate workspace member and is **not** in the `Makefile`'s
`VERIFICATION_TARGETS`, so it does not slow down `make`.

The build emits 39 `#[verus_spec] is likely used inside a verus! block`
warnings. These are expected: the `with Tracked(...)` clause is a
`#[verus_spec]` feature, and the real node code puts its `#[verus_verify] impl`
blocks inside `verus! { ... }` in exactly the same way.

## Why this is a rewrite and not an extraction

A verbatim copy of the node sources is not possible. Their dependency closure
is essentially the whole `mm` tree:

- `specs::mm::page_table::owners::{PageTableOwner, OwnerSubtree, Guards,
  CursorOwner}` and `specs::mm::page_table::cursor::page_size_lemmas` — the
  node layer depends *upward* on cursor-level specs (in `alloc`, `lock`, and
  throughout `entry.rs`);
- `mm::VmReader` / `specs::mm::io::VmIoOwner` / `specs::mm::virt_mem::MemView`
  plus `ostd_pod` — the whole `PageTablePageMeta::on_drop` byte-walk, roughly
  300 of `node/mod.rs`'s 1139 lines;
- `frame::meta::{MetaSlot, mapping}` and
  `specs::mm::frame::{meta_owners, meta_region_owners, mapping}`;
- `page_table::{PageTableConfig, PageTableEntryTrait}` — 1857 lines of trait
  with heavy `pow2` address arithmetic.

`vstd_extra` (`ghost_tree`, `array_ptr`, `ownership`, `drop_tracking`) is a
separate workspace crate, so it is available for free; the model uses
`array_ptr` and `ownership` and nothing else from it.

## Layout

The module tree mirrors the real one. `crate::node` is the part you want to
read; everything below it is the stub.

| Model | Real counterpart |
| --- | --- |
| `arch.rs` | `specs/arch/x86`, `mm::{Paddr, Vaddr, PagingLevel}`, `kspace` |
| `page_prop.rs` | `mm::page_prop` |
| `pte.rs` | `PageTableEntryTrait` (i.e. `C::E`), `load_pte`/`store_pte` |
| `frame/mapping.rs` | `frame::meta::mapping`, `specs::mm::frame::mapping` |
| `frame/owners.rs` | `specs::mm::frame::{meta_owners, meta_region_owners}` |
| `frame/mod.rs` | `mm::frame::{Frame, FrameRef}` |
| `node/mod.rs` | `src/mm/page_table/node/mod.rs` + `specs/.../node/mod.rs` |
| `node/owners.rs` | `specs/mm/page_table/node/owners.rs` |
| `node/entry_owners.rs` | `specs/mm/page_table/node/entry_owners.rs` |
| `node/child.rs` | `src/.../node/child.rs` + `specs/.../node/child.rs` |
| `node/entry.rs` | `src/.../node/entry.rs` + `specs/.../node/entry.rs` |
| `demo.rs` | *(new)* worked example of how the API composes |

## What is kept faithfully

The structural facts that make the node layer what it is are all preserved,
with the real names:

- **Three handle types.** `PageTableNode` (owning) / `PageTableNodeRef`
  (borrowed) / `PageTableGuard` (borrowed **and** locked), and only the guard
  can write PTEs.
- **Two-location addressing.** A `Frame` handle stores the frame's *metadata
  slot* address; a PTE stores its *physical* address; `frame_to_meta` /
  `meta_to_frame` convert. This is a constant source of address juggling in the
  real proofs and it is reproduced here — with the round-trip lemmas *proven*,
  not axiomatised.
- **Split permissions.** A node's `nr_children`/`stray` `PCell` permissions
  travel in `NodeOwner::meta_own`, while the permission for the slot's storage
  stays parked in `MetaRegionOwners`, and the node's PTE array is a *third*
  permission (`NodeOwner::children_perm`) at `paddr_to_vaddr(paddr)`.
- **`meta_bridge` vs `metaregion_sound_node`.** The region-dependent invariant
  is split so that `count_consistent` (`nr_children == count_present(ptes)`)
  can be *momentarily false* in the middle of `replace`, between the counter
  update and the PTE write. This is exactly why the real code keeps that clause
  out of `NodeOwner::inv()`, and the model reproduces the split. (The real code
  achieves the same by listing weaker preconditions inline; naming the weaker
  predicate makes the reason visible.)
- **`count_present` and its five lemmas**, so the `nr_children ± 1` bookkeeping
  in `replace` is proven not to under/overflow.
- **`match_pte`** — the case split relating a PTE to what its owner claims, and
  the single point where the encoding meets the ownership story.
- **`usage` as the node/frame discriminator.** `metaregion_sound` requires a
  node's slot to be tagged `PageTable` and a mapped frame's slot not to be;
  together with "a freshly allocated slot was `Unused`" this is what gives
  `alloc_if_none` its parent ≠ child distinctness.
- **Lock-before-publish.** `alloc_if_none` allocates, locks, *then* writes the
  PTE, so the new node is never reachable through the page table while
  unlocked.
- **The `#[verus_spec(with Tracked(...))]` calling convention**, so signatures
  read the same as the real ones.

## What is stubbed, and how

| Dropped | Consequence |
| --- | --- |
| `PageTableConfig` / `PageTableEntryTrait` | The model is monomorphic. `Pte` is a transparent struct instead of a `u64` bit layout, so all the "PTE laws" (`Pte::group_pte_laws`) are *provable* rather than axiomatised — the real `lemma_page_table_entry_properties` is an axiom over the encoding. |
| `vstd_extra::ghost_tree` (`TreePath`, `OwnerSubtree`) | `EntryOwner` has no `path`, and there is no `paths_in_pt` bookkeeping. This is what removes the node layer's upward dependency on cursor specs. |
| `PageTablePageMeta::on_drop` | The recursive teardown walk, and with it `VmReader`, `VmIoOwner`, `MemView`, and `ostd_pod`. `Frame` has no `Drop` in the model. |
| `vstd_extra::drop_tracking` | No `frame_obligations` ledger. `Child::into_pte`/`from_pte` therefore take `&Regions` instead of `&mut`, and provably leave it unchanged. |
| `MetaSlot` type erasure (`MetaSlotStorage` + `Repr`) | `MetaRegionOwners<M>` is generic in the metadata type rather than type-erased. The real `slots`/`slot_owners` split is merged into one map. |
| Atomic refcount, `UniqueFrame`, segments, linked lists, the allocator, MMIO | `MetaSlotOwner::ref_count` is a ghost `u64` with the `UNUSED` sentinel, and nothing in the model ever changes it. |
| `EntryOwner::Borrowed` | The variant for a user PT's kernel-half slots pointing into a *different* configuration's sub-tree; meaningless with one configuration. |
| Spin lock | As in the real development: `lock` is axiomatised, and `Guards` is the only record that a lock was taken. |

Constants keep their real values (`PAGE_SIZE = 4096`, `NR_ENTRIES = 512`,
`NR_LEVELS = 4`, `MAX_PADDR = 0x8000_0000`, `META_SLOT_SIZE = 64`) except the
two region bases, which are shrunk from `0xffff_e000_0000_0000` /
`0xffff_8000_0000_0000` to keep the SMT arithmetic cheap.

## The six axioms

Everything else is proven. `grep -rn external_body src/` gives:

| Site | Why |
| --- | --- |
| `pte.rs` — `load_pte`, `store_pte` | Compile to relaxed/release atomics; axiomatised as an indexed array read/write, exactly as in the real code. |
| `frame/mod.rs` — `Frame::from_raw`, `FrameRef::borrow_paddr` | The real bodies manipulate the atomic refcount. |
| `node/mod.rs` — `PageTableNode::alloc` | Calls the frame allocator. The ensures spell out the shape the node layer relies on: a previously-`Unused` slot becomes a live `PageTable` slot, no other slot moves, and the node comes back empty and unlocked. |
| `node/mod.rs` — `PageTableNodeRef::lock` | No spin lock implementation, as in the real development. |

There are no `assume(...)` or `admit()` anywhere.

## Where to start reading

1. `node/owners.rs` — `NodeOwner`, and the `meta_bridge` /
   `metaregion_sound_node` split.
2. `node/entry_owners.rs` — `EntryOwner::match_pte`, the heart of the
   PTE↔ownership relation.
3. `node/child.rs` — `into_pte` / `from_pte`, where ownership moves in and out
   of a PTE.
4. `node/entry.rs` — `replace` (the `nr_children` bookkeeping) and
   `alloc_if_none` (allocate, lock, publish).
5. `demo.rs` — the two of them composed, the way `cursor` would.

## Known gaps

Modelled from `entry.rs`: `is_none`, `is_node`, `to_ref`, `replace`,
`alloc_if_none`. Not modelled: `protect` / `protect_child`,
`split_if_mapped_huge`, `replace_child`, `alloc_absent_child`,
`replace_absent_with_frame`. `split_if_mapped_huge` in particular is the one
that would most stress the model, since it is where a huge-page item is split
across 512 child entries.
