#![feature(
    maybe_uninit_uninit_array,
    maybe_uninit_slice,
    maybe_uninit_write_slice,
    rustc_attrs
)]
#![deny(missing_docs, clippy::missing_safety_doc)]
#![warn(unsafe_op_in_unsafe_fn, deprecated_in_future)]

//! Adaptive radix trie implementation

mod nodes;

pub use nodes::*;
