#[cfg(all(test, any(feature = "nightly", feature = "allocator-api2")))]
pub(crate) use self::inner::AllocError;
pub(crate) use self::inner::{do_alloc, Allocator, Global};

// Nightly-case.
// Use unstable `allocator_api` feature.
// This is compatible with `allocator-api2` which can be enabled or not.
// This is used when building for `std`.
#[cfg(feature = "nightly")]
mod inner {
    #[cfg(test)]
    pub use alloc::alloc::AllocError;
    use alloc::alloc::Layout;
    pub use alloc::alloc::{Allocator, Global};
    use core::ptr::NonNull;

    pub(crate) fn do_alloc<A: Allocator>(alloc: &A, layout: Layout) -> Result<NonNull<u8>, ()> {
        match alloc.allocate(layout) {
            Ok(ptr) => Ok(ptr.as_non_null_ptr()),
            Err(_) => Err(()),
        }
    }
}

// Basic non-nightly case.
// This uses `allocator-api2` enabled by default.
// If any crate enables "nightly" in `allocator-api2`,
// this will be equivalent to the nightly case,
// since `allocator_api2::alloc::Allocator` would be re-export of
// `core::alloc::Allocator`.
#[cfg(all(not(feature = "nightly"), feature = "allocator-api2"))]
mod inner {
    use alloc::alloc::Layout;
    use core::ptr::NonNull;

    #[cfg(test)]
    pub use allocator_api2::alloc::AllocError;
    pub use allocator_api2::alloc::{Allocator, Global};

    #[expect(clippy::map_err_ignore)]
    pub(crate) fn do_alloc<A: Allocator>(alloc: &A, layout: Layout) -> Result<NonNull<u8>, ()> {
        match alloc.allocate(layout) {
            Ok(ptr) => Ok(ptr.cast()),
            Err(_) => Err(()),
        }
    }
}

// No-defaults case.
// When building with default-features turned off and
// neither `nightly` nor `allocator-api2` is enabled,
// this will be used.
// Making it impossible to use any custom allocator with collections defined
// in this crate.
// Any crate in build-tree can enable `allocator-api2`,
// or `nightly` without disturbing users that don't want to use it.
#[cfg(not(any(feature = "nightly", feature = "allocator-api2")))]
mod inner {
    use alloc::alloc::{alloc, dealloc, Layout};
    use core::ptr::NonNull;

    #[expect(clippy::missing_safety_doc)] // not exposed outside of this crate
    pub unsafe trait Allocator {
        /// Attempts to allocate a block of memory.
        fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, ()>;

        /// Deallocates the memory referenced by `ptr`.
        ///
        /// # Safety
        ///
        /// * `ptr` must denote a block of memory [*currently allocated*] via
        ///   this allocator, and
        /// * `layout` must [*fit*] that block of memory.
        ///
        /// [*currently allocated*]: https://doc.rust-lang.org/std/alloc/trait.Allocator.html#currently-allocated-memory
        /// [*fit*]: https://doc.rust-lang.org/std/alloc/trait.Allocator.html#memory-fitting
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
    }

    /// The global memory allocator.
    #[derive(Copy, Clone)]
    pub struct Global;

    unsafe impl Allocator for Global {
        #[inline]
        fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, ()> {
            unsafe { NonNull::new(alloc(layout)).ok_or(()) }
        }

        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            unsafe { dealloc(ptr.as_ptr(), layout) };
        }
    }

    impl Default for Global {
        #[inline]
        fn default() -> Self {
            Global
        }
    }

    /// Allocate a block of memory that fits the given layout using the given
    /// allocator.
    pub(crate) fn do_alloc<A: Allocator>(alloc: &A, layout: Layout) -> Result<NonNull<u8>, ()> {
        alloc.allocate(layout)
    }
}
