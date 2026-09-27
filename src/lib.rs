#![no_std]
#![cfg_attr(
    feature = "nightly",
    feature(
        allocator_api,
        hasher_prefixfree_extras,
        impl_trait_in_assoc_type,
        likely_unlikely,
        maybe_uninit_array_assume_init,
        maybe_uninit_slice,
        portable_simd,
        slice_ptr_get,
    )
)]
#![warn(clippy::dbg_macro)]
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
//!  - Leis, V., Kemper, A., & Neumann, T. (2013, April). The adaptive radix tree: ARTful indexing
//!    for main-memory databases. In 2013 IEEE 29th International Conference on Data Engineering
//!    (ICDE) (pp. 38-49). IEEE. [Link to PDF][ART paper]
//!
//! [ART paper]: http://web.archive.org/web/20240508000744/https://db.in.tum.de/~leis/papers/ART.pdf
//!
//! # Crate Features
//!
//!  - **nightly** - Enables internal and public use of nightly APIs in the crate. The most
//!    important features enabled is use of the [`std::simd`] module and the nightly allocator API.
//!  - **allocator-api2** - This feature is an alternative to the *ni*ghtly* fe*ature which allows
//!    customizing the allocators.
//!  - **std** - When enabled, this will cause the crate to use the standard library.
//!  - **testing** - This feature exposes the `testing` module, which contains helper function for
//!    writing tests.
//!  - **_internal** - This feature makes the `raw` module public. The `raw` module contains a lot
//!    of the implementation details of the radix trie. The items within this module do not carry
//!    the same guarantees around SemVer that the rest of the crate does. Additionally, there may be
//!    items in the module which have trie invariants which can cause unsoundness in safe code. This
//!    module is mostly used for experimentation and likely will be entirely private in the future.
//!
//! [`std::simd`]: https://doc.rust-lang.org/stable/std/simd/index.html

#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod allocator;
mod bytes;
mod collections;
mod rust_nightly_apis;
mod tagged_pointer;

#[cfg(feature = "_internal")]
pub mod raw;
#[cfg(not(feature = "_internal"))]
mod raw;

#[cfg(feature = "testing")]
pub mod testing;

pub use bytes::*;
pub use collections::*;
pub use raw::{visitor, OpaqueNodePtr};

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
