//! Page properties.
//!
//! Model of `ostd::mm::page_prop`. The real type carries `PageFlags`,
//! `CachePolicy` and `PrivilegedPageFlags`; the node layer never inspects any
//! of them, it only copies them between PTEs and `Child::Frame`, so the model
//! keeps a single opaque bitfield.
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub struct PageProperty {
    /// R = 0b001, W = 0b010, X = 0b100.
    pub flags: u8,
}

impl PageProperty {
    pub open spec fn new_spec(flags: u8) -> Self {
        PageProperty { flags }
    }

    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(flags: u8) -> (res: Self)
        returns
            Self::new_spec(flags),
    {
        PageProperty { flags }
    }
}

} // verus!
