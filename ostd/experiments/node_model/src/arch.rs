//! Architecture constants and address types.
//!
//! Model of the subset of `ostd::specs::arch` (x86-64) and `ostd::mm` address
//! types that the node layer actually uses. Values match the real ones.
use vstd::prelude::*;

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

/// A physical address.
pub type Paddr = usize;

/// A virtual address.
pub type Vaddr = usize;

/// The level of a page table node. Levels count *up* from the leaves: level 1
/// nodes map base pages, level `NR_LEVELS` is the root.
pub type PagingLevel = u8;

/// Base page size.
pub const PAGE_SIZE: usize = 4096;

/// The number of PTEs in a page table node.
pub const NR_ENTRIES: usize = 512;

/// The number of page table levels.
pub const NR_LEVELS: usize = 4;

/// Parameterized maximum physical address.
pub const MAX_PADDR: usize = 0x8000_0000;

/// Size of one metadata slot, i.e. of the model's `MetaSlot`.
pub const META_SLOT_SIZE: usize = 64;

/// Base of the frame-metadata linear mapping.
///
/// The real kernel uses `0xffff_e000_0000_0000`. The model keeps a small
/// non-zero base: nothing in the node layer depends on the actual value, and a
/// small constant keeps the `frame_to_meta`/`meta_to_frame` arithmetic cheap
/// for the SMT solver.
pub const FRAME_METADATA_BASE: Vaddr = 0x1000_0000;

/// Base of the linear mapping of physical memory.
///
/// Real kernel: `0xffff_8000_0000_0000`. Same reasoning as above.
pub const LINEAR_MAPPING_BASE_VADDR: Vaddr = 0x4000_0000_0000;

/// The number of frames the metadata region can describe.
pub open spec fn max_meta_slots() -> int {
    (MAX_PADDR / PAGE_SIZE) as int
}

/// A physical address names a real, page-aligned frame.
pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    &&& paddr % PAGE_SIZE == 0
    &&& paddr < MAX_PADDR
}

/// The size of a page mapped by a leaf PTE at `level`.
///
/// Level 1 maps `PAGE_SIZE`, each level up multiplies by `NR_ENTRIES`.
pub open spec fn page_size_spec(level: PagingLevel) -> nat
    decreases level,
{
    if level <= 1 {
        PAGE_SIZE as nat
    } else {
        page_size_spec((level - 1) as PagingLevel) * NR_ENTRIES as nat
    }
}

/// Translates a physical address to its address in the linear mapping.
#[verifier::inline]
pub open spec fn paddr_to_vaddr_spec(pa: Paddr) -> Vaddr {
    (pa + LINEAR_MAPPING_BASE_VADDR) as Vaddr
}

#[verifier::when_used_as_spec(paddr_to_vaddr_spec)]
pub fn paddr_to_vaddr(pa: Paddr) -> (res: Vaddr)
    requires
        pa < MAX_PADDR,
    returns
        paddr_to_vaddr_spec(pa),
{
    pa + LINEAR_MAPPING_BASE_VADDR
}

/// `paddr_to_vaddr` is injective, so distinct frames get disjoint page arrays.
pub broadcast proof fn lemma_paddr_to_vaddr_injective(p1: Paddr, p2: Paddr)
    requires
        p1 < MAX_PADDR,
        p2 < MAX_PADDR,
        p1 != p2,
    ensures
        #[trigger] paddr_to_vaddr_spec(p1) != #[trigger] paddr_to_vaddr_spec(p2),
{
}

} // verus!
