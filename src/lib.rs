#![cfg_attr(
    feature = "nightly",
    feature(
        maybe_uninit_uninit_array,
        maybe_uninit_slice,
        nonnull_slice_from_raw_parts,
        slice_ptr_get,
        strict_provenance,
        maybe_uninit_write_slice,
        hasher_prefixfree_extras
    )
)]
#![allow(unstable_name_collisions)]
#![deny(
    missing_docs,
    clippy::missing_safety_doc,
    unsafe_op_in_unsafe_fn,
    deprecated_in_future,
    rustdoc::broken_intra_doc_links,
    rustdoc::bare_urls,
    rustdoc::invalid_codeblock_attributes
)]

//! Adaptive radix trie implementation
//!
//! # References
//!
//!  - Leis, V., Kemper, A., & Neumann, T. (2013, April). The adaptive radix
//!    tree: ARTful indexing for main-memory databases. In 2013 IEEE 29th
//!    International Conference on Data Engineering (ICDE) (pp. 38-49). IEEE.
//!    [Link to PDF][ART paper]
//!
//! [ART paper]: https://www-db.in.tum.de/~leis/papers/ART.pdf

mod collections;
mod nodes;
pub mod tagged_pointer;
#[doc(hidden)]
pub mod tests_common;

pub use collections::*;
pub use nodes::*;

mod nightly_rust_apis;
