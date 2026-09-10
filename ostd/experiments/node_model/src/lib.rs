//! A self-contained tiny model of the OSTD page table **node** layer.
//!
//! See `README.md` for what is modelled faithfully and what is stubbed.
#![no_std]
#![feature(nonzero_internals)]
#![feature(sized_hierarchy)]
#![feature(proc_macro_hygiene)]
#![allow(non_snake_case)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(unused_imports)]

extern crate alloc;

pub mod arch;
pub mod demo;
pub mod frame;
pub mod node;
pub mod page_prop;
pub mod pte;
