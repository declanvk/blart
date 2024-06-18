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
#![feature(generic_const_exprs)]
#![allow(unstable_name_collisions, internal_features, clippy::type_complexity)]
#![deny(
    missing_docs,
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

/// ART type for keys with variable length
pub type VariableTreeMap<K, V, const NUM_PREFIX_BYTES: usize> =
    RawTreeMap<K, V, NUM_PREFIX_BYTES, nodes::VariableKeyHeader<NUM_PREFIX_BYTES>>;

/// Standard ART type. The default is for variable key lengths, with 16 byte
/// prefix
pub type TreeMap<K, V> = VariableTreeMap<K, V, 16>;

/// ART type for keys with fixed length
pub type FixedTreeMap<K, V, const NUM_PREFIX_BYTES: usize = { std::mem::size_of::<K>() }> =
    RawTreeMap<K, V, NUM_PREFIX_BYTES, nodes::FixedKeyHeader<NUM_PREFIX_BYTES, K>>;

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
