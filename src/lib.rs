#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_uninit_array)]
#![feature(maybe_uninit_array_assume_init)]
#![feature(slice_ptr_get)]
#![feature(hasher_prefixfree_extras)]
#![feature(portable_simd)]
#![feature(new_uninit)]
#![feature(impl_trait_in_assoc_type)]
#![feature(core_intrinsics)]
#![feature(is_sorted)]
#![feature(strict_provenance)]
#![allow(unstable_name_collisions, internal_features, clippy::type_complexity)]
#![deny(
    // missing_docs,
    clippy::missing_safety_doc,
    unsafe_op_in_unsafe_fn,
    deprecated_in_future,
    rustdoc::broken_intra_doc_links,
    rustdoc::bare_urls,
    rustdoc::invalid_codeblock_attributes
)]
#![doc(
    html_playground_url = "https://play.rust-lang.org/",
    test(attr(deny(warnings)))
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

mod bytes;
mod collections;
mod nodes;
mod tagged_pointer;

#[doc(hidden)]
pub mod tests_common;

#[cfg(feature = "gen-benches-macro")]
#[doc(hidden)]
pub mod benches_common;

pub use bytes::*;
pub use collections::*;
pub use nodes::{visitor, *};

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
