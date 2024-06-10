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
pub const unsafe fn maybe_uninit_slice_assume_init_ref<T>(
    slice: &[std::mem::MaybeUninit<T>],
) -> &[T] {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { std::mem::MaybeUninit::slice_assume_init_ref(slice) }
    }

    #[cfg(not(feature = "nightly"))]
    {
        // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees
        // that `slice` is initialized, and `MaybeUninit` is guaranteed to have
        // the same layout as `T`. The pointer obtained is valid since it refers
        // to memory owned by `slice` which is a reference and thus guaranteed
        // to be valid for reads.
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
pub unsafe fn maybe_uninit_slice_assume_init_mut<T>(
    slice: &mut [std::mem::MaybeUninit<T>],
) -> &mut [T] {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { std::mem::MaybeUninit::slice_assume_init_mut(slice) }
    }

    #[cfg(not(feature = "nightly"))]
    {
        // SAFETY: similar to safety notes for `slice_get_ref`, but we have a
        // mutable reference which is also guaranteed to be valid for writes.
        unsafe { &mut *(slice as *mut [std::mem::MaybeUninit<T>] as *mut [T]) }
    }
}

/// Gets a pointer to the first element of the array.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
pub fn maybe_uninit_slice_as_ptr<T>(this: &[std::mem::MaybeUninit<T>]) -> *const T {
    #[cfg(feature = "nightly")]
    {
        std::mem::MaybeUninit::slice_as_ptr(this)
    }

    #[cfg(not(feature = "nightly"))]
    {
        this.as_ptr() as *const T
    }
}

/// Returns a raw pointer to an element, without doing bounds checking.
///
/// Calling this method with an out-of-bounds index or when `data` is not
/// dereferenceable is *[undefined behavior]* even if the resulting pointer is
/// not used.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#74265][issue-74265]**
///
/// [issue-74265]: https://github.com/rust-lang/rust/issues/74265
/// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
pub unsafe fn non_null_get_unchecked_mut<T>(
    data: std::ptr::NonNull<[T]>,
    index: usize,
) -> std::ptr::NonNull<T> {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { std::ptr::NonNull::get_unchecked_mut(data, index) }
    }

    #[cfg(not(feature = "nightly"))]
    {
        // SAFETY: the caller ensures that `self` is dereferenceable and `index`
        // in-bounds. As a consequence, the resulting pointer cannot be null.

        unsafe { std::ptr::NonNull::new_unchecked(data.as_ptr().cast::<T>().add(index)) }
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
