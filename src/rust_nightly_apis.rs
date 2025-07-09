//! Module containing copies of Rust standard library unstable functions for use
//! outside of the nightly distribution.

/// Assuming all the elements are initialized, get a slice to them.
///
/// # Safety
///
/// It is up to the caller to guarantee that the `MaybeUninit<T>` elements
/// really are in an initialized state.
/// Calling this when the content is not yet fully initialized causes
/// undefined behavior.
///
/// See [`assume_init_ref`][std::mem::MaybeUninit::assume_init_ref] for more
/// details and examples.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
#[inline]
pub const unsafe fn maybe_uninit_slice_assume_init_ref<T>(
    slice: &[std::mem::MaybeUninit<T>],
) -> &[T] {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { slice.assume_init_ref() }
    }

    #[cfg(not(feature = "nightly"))]
    {
        // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees
        // that `slice` is initialized, and `MaybeUninit` is guaranteed to have the same
        // layout as `T`. The pointer obtained is valid since it refers to memory owned
        // by `slice` which is a reference and thus guaranteed to be valid for
        // reads.
        unsafe { &*(slice as *const [std::mem::MaybeUninit<T>] as *const [T]) }
    }
}

/// Assuming all the elements are initialized, get a mutable slice to them.
///
/// # Safety
///
/// It is up to the caller to guarantee that the `MaybeUninit<T>` elements
/// really are in an initialized state.
/// Calling this when the content is not yet fully initialized causes
/// undefined behavior.
///
/// See [`assume_init_mut`][std::mem::MaybeUninit::assume_init_mut] for more
/// details and examples.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
#[inline]
pub unsafe fn maybe_uninit_slice_assume_init_mut<T>(
    slice: &mut [std::mem::MaybeUninit<T>],
) -> &mut [T] {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { slice.assume_init_mut() }
    }

    #[cfg(not(feature = "nightly"))]
    {
        // SAFETY: similar to safety notes for `maybe_uninit_slice_assume_init_ref`, but
        // we have a mutable reference which is also guaranteed to be valid for
        // writes.
        unsafe { &mut *(slice as *mut [std::mem::MaybeUninit<T>] as *mut [T]) }
    }
}

/// Writes a length prefix into this hasher, as part of being prefix-free.
///
/// If you're implementing [`Hash`] for a custom collection, call this before
/// writing its contents to this `Hasher`.  That way
/// `(collection![1, 2, 3], collection![4, 5])` and
/// `(collection![1, 2], collection![3, 4, 5])` will provide different
/// sequences of values to the `Hasher`
///
/// The `impl<T> Hash for [T]` includes a call to this method, so if you're
/// hashing a slice (or array or vector) via its `Hash::hash` method,
/// you should **not** call this yourself.
///
/// This method is only for providing domain separation.  If you want to
/// hash a `usize` that represents part of the *data*, then it's important
/// that you pass it to [`Hasher::write_usize`][std::hash::Hasher::write_usize]
/// instead of to this method.
///
/// # Note to Implementers
///
/// If you've decided that your `Hasher` is willing to be susceptible to
/// Hash-DoS attacks, then you might consider skipping hashing some or all
/// of the `len` provided in the name of increased performance.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#96762][issue-96762]**
///
/// [issue-96762]: https://github.com/rust-lang/rust/issues/96762
#[inline]
pub fn hasher_write_length_prefix<H: std::hash::Hasher>(state: &mut H, num_entries: usize) {
    #[cfg(feature = "nightly")]
    {
        <H as std::hash::Hasher>::write_length_prefix(state, num_entries);
    }

    #[cfg(not(feature = "nightly"))]
    {
        state.write_usize(num_entries);
    }
}

/// Constructs a new boxed slice with uninitialized contents.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63291][issue-63291]**
///
/// [issue-63291]: https://github.com/rust-lang/rust/issues/63291
#[inline]
pub fn box_new_uninit_slice<T>(len: usize) -> Box<[std::mem::MaybeUninit<T>]> {
    #[cfg(feature = "nightly")]
    {
        Box::new_uninit_slice(len)
    }

    #[cfg(not(feature = "nightly"))]
    {
        Vec::from_iter((0..len).map(|_| std::mem::MaybeUninit::uninit())).into_boxed_slice()
    }
}

/// Informs the optimizer that a condition is always true.
/// If the condition is false, the behavior is undefined.
///
/// No code is generated for this intrinsic, but the optimizer will try
/// to preserve it (and its condition) between passes, which may interfere
/// with optimization of surrounding code and reduce performance. It should
/// not be used if the invariant can be discovered by the optimizer on its
/// own, or if it does not enable any significant optimizations.
///
/// This intrinsic does not have a stable counterpart.
///
/// **This is a unstable API copied from the Rust standard library**
macro_rules! assume {
    ($b:expr) => {
        debug_assert!($b);
        #[cfg(feature = "nightly")]
        std::intrinsics::assume($b)
    };
}

pub(crate) use assume;

/// Hints to the compiler that branch condition is likely to be true.
/// Returns the value passed to it.
///
/// Any use other than with `if` statements will probably not have an effect.
///
/// Note that, unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block.
/// Therefore, implementations must not require the user to uphold
/// any safety invariants.
///
/// This intrinsic does not have a stable counterpart.
///
/// **This is a unstable API copied from the Rust standard library**
#[cfg(feature = "nightly")]
macro_rules! likely {
    ($b:expr) => {
        std::intrinsics::likely($b)
    };
}

/// Hints to the compiler that branch condition is likely to be true.
/// Returns the value passed to it.
///
/// Any use other than with `if` statements will probably not have an effect.
///
/// Note that, unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block.
/// Therefore, implementations must not require the user to uphold
/// any safety invariants.
///
/// This intrinsic does not have a stable counterpart.
///
/// **This is a unstable API copied from the Rust standard library**
#[cfg(not(feature = "nightly"))]
macro_rules! likely {
    ($b:expr) => {
        $b
    };
}

pub(crate) use likely;

/// Hints to the compiler that branch condition is likely to be false.
/// Returns the value passed to it.
///
/// Any use other than with `if` statements will probably not have an effect.
///
/// Note that, unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block.
/// Therefore, implementations must not require the user to uphold
/// any safety invariants.
///
/// This intrinsic does not have a stable counterpart.
///
/// **This is a unstable API copied from the Rust standard library**
#[cfg(feature = "nightly")]
macro_rules! unlikely {
    ($b:expr) => {
        std::intrinsics::unlikely($b)
    };
}

/// Hints to the compiler that branch condition is likely to be false.
/// Returns the value passed to it.
///
/// Any use other than with `if` statements will probably not have an effect.
///
/// Note that, unlike most intrinsics, this is safe to call;
/// it does not require an `unsafe` block.
/// Therefore, implementations must not require the user to uphold
/// any safety invariants.
///
/// This intrinsic does not have a stable counterpart.
///
/// **This is a unstable API copied from the Rust standard library**
#[cfg(not(feature = "nightly"))]
macro_rules! unlikely {
    ($b:expr) => {
        $b
    };
}

pub(crate) use unlikely;

pub(crate) mod ptr {
    //! This module contains shim functions for strict-provenance stuff related
    //! to pointers

    use std::{num::NonZeroUsize, ptr::NonNull};

    #[inline]
    #[cfg(not(feature = "nightly"))]
    #[expect(clippy::transmutes_expressible_as_ptr_casts)]
    pub fn mut_addr<T>(ptr: *mut T) -> usize {
        // FIXME(strict_provenance_magic): I am magic and should be a compiler
        // intrinsic. SAFETY: Pointer-to-integer transmutes are valid (if you
        // are okay with losing the provenance).
        unsafe { std::mem::transmute(ptr.cast::<()>()) }
    }

    #[inline]
    #[cfg(feature = "nightly")]
    pub fn mut_addr<T>(ptr: *mut T) -> usize {
        ptr.addr()
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn mut_with_addr<T>(ptr: *mut T, addr: usize) -> *mut T {
        let self_addr = mut_addr(ptr) as isize;
        let dest_addr = addr as isize;
        let offset = dest_addr.wrapping_sub(self_addr);

        ptr.wrapping_byte_offset(offset)
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(feature = "nightly")]
    pub fn mut_with_addr<T>(ptr: *mut T, addr: usize) -> *mut T {
        ptr.with_addr(addr)
    }

    #[cfg(test)]
    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn const_addr<T>(ptr: *const T) -> usize {
        // FIXME(strict_provenance_magic): I am magic and should be a compiler
        // intrinsic. SAFETY: Pointer-to-integer transmutes are valid (if you
        // are okay with losing the provenance).
        ptr.cast::<()>() as usize
    }

    #[cfg(test)]
    #[inline]
    #[cfg(feature = "nightly")]
    pub fn const_addr<T>(ptr: *const T) -> usize {
        ptr.addr()
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn nonnull_addr<T>(ptr: NonNull<T>) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(mut_addr(ptr.as_ptr())) }
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(feature = "nightly")]
    pub fn nonnull_addr<T>(ptr: NonNull<T>) -> NonZeroUsize {
        ptr.addr()
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn nonnull_with_addr<T>(ptr: NonNull<T>, addr: NonZeroUsize) -> NonNull<T> {
        unsafe { NonNull::new_unchecked(mut_with_addr(ptr.as_ptr(), addr.get())) }
    }

    #[cfg(all(test, any(feature = "allocator-api2", feature = "nightly")))]
    #[inline]
    #[cfg(feature = "nightly")]
    pub fn nonnull_with_addr<T>(ptr: NonNull<T>, addr: NonZeroUsize) -> NonNull<T> {
        ptr.with_addr(addr)
    }

    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn nonnull_map_addr<T>(
        ptr: NonNull<T>,
        f: impl FnOnce(NonZeroUsize) -> NonZeroUsize,
    ) -> NonNull<T> {
        let ptr = ptr.as_ptr();
        let old_addr = mut_addr(ptr);
        let new_addr = f(unsafe {
            // SAFETY: `ptr` was a `NonNull` pointer, the address was required to be
            // non-zero.
            NonZeroUsize::new_unchecked(old_addr)
        });

        let offset = new_addr.get().wrapping_sub(old_addr);
        // This is the canonical desugaring of this operation
        let new_ptr = ptr.wrapping_byte_offset(offset as isize);

        // SAFETY: The 2 lines of code above are just changing the address of the
        // pointer, while trying to retain the same provenance. Since the `new_addr`
        // returned from `f` is non-zero, then the `new_ptr` must be non-null.
        unsafe { NonNull::new_unchecked(new_ptr) }
    }

    #[inline]
    #[cfg(feature = "nightly")]
    pub fn nonnull_map_addr<T>(
        ptr: NonNull<T>,
        f: impl FnOnce(NonZeroUsize) -> NonZeroUsize,
    ) -> NonNull<T> {
        ptr.map_addr(f)
    }
}
