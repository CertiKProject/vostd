//! The frame ⇄ metadata-slot address mapping.
//!
//! Model of `ostd::mm::frame::meta::mapping` and
//! `ostd::specs::mm::frame::mapping`. The formulas are the real ones (only the
//! base constants are smaller); the lemmas mirror the real `group_page_meta`
//! broadcast group.
//!
//! Every frame in `[0, MAX_PADDR)` has an *index* `paddr / PAGE_SIZE`, a
//! *frame address* `index * PAGE_SIZE`, and a *metadata slot address*
//! `FRAME_METADATA_BASE + index * META_SLOT_SIZE`. The node layer moves
//! between the three constantly: a `Frame` handle stores the **metadata**
//! address, while PTEs store the **frame** address.
use vstd::arithmetic::div_mod::{
    lemma_div_by_multiple, lemma_div_is_ordered, lemma_fundamental_div_mod,
};
use vstd::prelude::*;

use crate::arch::*;

verus! {

/// The metadata-slot index of a frame.
#[verifier::inline]
pub open spec fn frame_to_index(paddr: Paddr) -> int
    recommends
        paddr % PAGE_SIZE == 0,
{
    (paddr / PAGE_SIZE) as int
}

/// The frame address of a metadata-slot index.
#[verifier::inline]
pub open spec fn index_to_frame(index: int) -> Paddr
    recommends
        0 <= index < max_meta_slots(),
{
    (index * PAGE_SIZE) as Paddr
}

/// The metadata-slot address of a metadata-slot index.
pub open spec fn index_to_meta(index: int) -> Vaddr
    recommends
        0 <= index < max_meta_slots(),
{
    (FRAME_METADATA_BASE + index * META_SLOT_SIZE) as Vaddr
}

/// The metadata-slot index of a metadata-slot address.
pub open spec fn meta_to_index(vaddr: Vaddr) -> int {
    (vaddr - FRAME_METADATA_BASE) / META_SLOT_SIZE as int
}

/// A metadata-slot address is in range and correctly aligned.
pub open spec fn valid_meta_vaddr(vaddr: Vaddr) -> bool {
    &&& FRAME_METADATA_BASE <= vaddr
    &&& (vaddr - FRAME_METADATA_BASE) % META_SLOT_SIZE as int == 0
    &&& meta_to_index(vaddr) < max_meta_slots()
}

pub open spec fn frame_to_meta_spec(paddr: Paddr) -> Vaddr {
    index_to_meta(frame_to_index(paddr))
}

/// Converts a frame's physical address to its metadata slot address.
#[verifier::when_used_as_spec(frame_to_meta_spec)]
pub fn frame_to_meta(paddr: Paddr) -> (res: Vaddr)
    requires
        valid_frame_paddr(paddr),
    returns
        frame_to_meta_spec(paddr),
{
    proof {
        lemma_frame_index_in_range(paddr);
    }
    FRAME_METADATA_BASE + (paddr / PAGE_SIZE) * META_SLOT_SIZE
}

pub open spec fn meta_to_frame_spec(vaddr: Vaddr) -> Paddr {
    index_to_frame(meta_to_index(vaddr))
}

/// Converts a metadata slot address back to its frame's physical address.
#[verifier::when_used_as_spec(meta_to_frame_spec)]
pub fn meta_to_frame(vaddr: Vaddr) -> (res: Paddr)
    requires
        valid_meta_vaddr(vaddr),
    returns
        meta_to_frame_spec(vaddr),
{
    proof {
        lemma_meta_index_in_range(vaddr);
    }
    ((vaddr - FRAME_METADATA_BASE) / META_SLOT_SIZE) * PAGE_SIZE
}

// ─── Laws ──────────────────────────────────────────────────────────────────
/// A valid frame address has an in-range index.
pub broadcast proof fn lemma_frame_index_in_range(paddr: Paddr)
    requires
        valid_frame_paddr(paddr),
    ensures
        0 <= #[trigger] frame_to_index(paddr) < max_meta_slots(),
{
    lemma_div_is_ordered(paddr as int, MAX_PADDR as int, PAGE_SIZE as int);
    assert(MAX_PADDR as int / PAGE_SIZE as int == max_meta_slots()) by (compute_only);
    // Division is monotone, so `paddr < MAX_PADDR` gives `<=` on the
    // quotients; equality is impossible because `paddr + PAGE_SIZE <=
    // MAX_PADDR` follows from `paddr` being page aligned.
    if frame_to_index(paddr) == max_meta_slots() {
        lemma_fundamental_div_mod(paddr as int, PAGE_SIZE as int);
        assert(false);
    }
}

/// A valid metadata address has an in-range index.
pub broadcast proof fn lemma_meta_index_in_range(vaddr: Vaddr)
    requires
        valid_meta_vaddr(vaddr),
    ensures
        0 <= #[trigger] meta_to_index(vaddr) < max_meta_slots(),
{
    lemma_div_is_ordered(0, (vaddr - FRAME_METADATA_BASE) as int, META_SLOT_SIZE as int);
}

/// Index → frame address → index is the identity, and yields a valid frame.
pub broadcast proof fn lemma_index_to_frame_biinjective(index: int)
    requires
        0 <= index < max_meta_slots(),
    ensures
        #[trigger] valid_frame_paddr(index_to_frame(index)),
        frame_to_index(index_to_frame(index)) == index,
{
    lemma_div_by_multiple(index, PAGE_SIZE as int);
}

/// Index → metadata address → index is the identity, and yields a valid slot.
pub broadcast proof fn lemma_index_to_meta_biinjective(index: int)
    requires
        0 <= index < max_meta_slots(),
    ensures
        #[trigger] valid_meta_vaddr(index_to_meta(index)),
        meta_to_index(index_to_meta(index)) == index,
{
    lemma_div_by_multiple(index, META_SLOT_SIZE as int);
}

/// Frame address → metadata address → frame address is the identity.
pub broadcast proof fn lemma_frame_to_meta_biinjective(paddr: Paddr)
    requires
        valid_frame_paddr(paddr),
    ensures
        valid_meta_vaddr(#[trigger] frame_to_meta_spec(paddr)),
        meta_to_frame_spec(frame_to_meta_spec(paddr)) == paddr,
{
    lemma_frame_index_in_range(paddr);
    lemma_index_to_meta_biinjective(frame_to_index(paddr));
    lemma_fundamental_div_mod(paddr as int, PAGE_SIZE as int);
}

/// Metadata address → frame address → metadata address is the identity.
pub broadcast proof fn lemma_meta_to_frame_biinjective(vaddr: Vaddr)
    requires
        valid_meta_vaddr(vaddr),
    ensures
        valid_frame_paddr(#[trigger] meta_to_frame_spec(vaddr)),
        frame_to_meta_spec(meta_to_frame_spec(vaddr)) == vaddr,
{
    lemma_meta_index_in_range(vaddr);
    lemma_index_to_frame_biinjective(meta_to_index(vaddr));
    lemma_fundamental_div_mod((vaddr - FRAME_METADATA_BASE) as int, META_SLOT_SIZE as int);
}

/// `frame_to_index` is injective on page-aligned addresses. This is what makes
/// "distinct frames occupy distinct metadata slots" true, which the node layer
/// leans on to know a parent and its child are different slots.
pub broadcast proof fn lemma_frame_to_index_injective(p1: Paddr, p2: Paddr)
    requires
        p1 % PAGE_SIZE == 0,
        p2 % PAGE_SIZE == 0,
        p1 != p2,
    ensures
        #[trigger] frame_to_index(p1) != #[trigger] frame_to_index(p2),
{
    lemma_fundamental_div_mod(p1 as int, PAGE_SIZE as int);
    lemma_fundamental_div_mod(p2 as int, PAGE_SIZE as int);
}

/// `index_to_meta` is injective.
pub broadcast proof fn lemma_index_to_meta_injective(i1: int, i2: int)
    requires
        0 <= i1 < max_meta_slots(),
        0 <= i2 < max_meta_slots(),
        i1 != i2,
    ensures
        #[trigger] index_to_meta(i1) != #[trigger] index_to_meta(i2),
{
}

pub broadcast group group_page_meta {
    lemma_frame_index_in_range,
    lemma_meta_index_in_range,
    lemma_index_to_frame_biinjective,
    lemma_index_to_meta_biinjective,
    lemma_frame_to_meta_biinjective,
    lemma_meta_to_frame_biinjective,
    lemma_index_to_meta_injective,
}

} // verus!
