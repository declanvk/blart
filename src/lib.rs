#![feature(
    maybe_uninit_uninit_array,
    maybe_uninit_slice,
    maybe_uninit_write_slice
)]
#![deny(missing_docs, clippy::missing_safety_doc)]
#![allow(unused_unsafe)]

//! Adaptive radix trie implementation

mod nodes;

pub use nodes::*;
