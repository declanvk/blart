#![feature(maybe_uninit_uninit_array, maybe_uninit_slice, never_type)]
#![deny(
    missing_docs,
    clippy::missing_safety_doc,
    unsafe_op_in_unsafe_fn,
    deprecated_in_future
)]

//! Adaptive radix trie implementation
//!
//! # References
//!
//!  - Leis, V., Kemper, A., & Neumann, T. (2013, April). The adaptive radix tree: ARTful indexing for main-memory databases. In 2013 IEEE 29th International Conference on Data Engineering (ICDE) (pp. 38-49). IEEE. [Link to PDF](https://www-db.in.tum.de/~leis/papers/ART.pdf)

mod nodes;
pub mod tagged_pointer;

pub use nodes::*;
