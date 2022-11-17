//! Module containing copies of Rust standard library unstable functions for use
//! outside of the nightly distribution.

use std::{
    mem::MaybeUninit,
    ptr::{slice_from_raw_parts_mut, NonNull},
};

/// Assuming all the elements are initialized, get a slice to them.
///
/// # Safety
///
/// It is up to the caller to guarantee that the `MaybeUninit<T>` elements
/// really are in an initialized state.
/// Calling this when the content is not yet fully initialized causes
/// undefined behavior.
///
/// See [`assume_init_ref`] for more details and examples.
///
/// [`assume_init_ref`]: MaybeUninit::assume_init_ref
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
pub const unsafe fn maybe_uninit_slice_assume_init_ref<T>(slice: &[MaybeUninit<T>]) -> &[T] {
    // SAFETY: casting `slice` to a `*const [T]` is safe since the caller guarantees
    // that `slice` is initialized, and `MaybeUninit` is guaranteed to have
    // the same layout as `T`. The pointer obtained is valid since it refers
    // to memory owned by `slice` which is a reference and thus guaranteed
    // to be valid for reads.
    unsafe { &*(slice as *const [MaybeUninit<T>] as *const [T]) }
}

/// Create a new array of `MaybeUninit<T>` items, in an uninitialized state.
///
/// Note: in a future Rust version this method may become unnecessary
/// when Rust allows
/// [inline const expressions](https://github.com/rust-lang/rust/issues/76001).
/// The example below could then use `let mut buf = [const {
/// MaybeUninit::<u8>::uninit() }; 32];`.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#96097][issue-96097]**
///
/// [issue-96097]: https://github.com/rust-lang/rust/issues/96097
pub const fn maybe_uninit_uninit_array<const N: usize, T>() -> [MaybeUninit<T>; N] {
    // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
    unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() }
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
/// See [`assume_init_mut`] for more details and examples.
///
/// [`assume_init_mut`]: MaybeUninit::assume_init_mut
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
pub unsafe fn maybe_uninit_slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: similar to safety notes for `slice_get_ref`, but we have a
    // mutable reference which is also guaranteed to be valid for writes.
    unsafe { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

/// Gets a pointer to the first element of the array.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63569][issue-63569]**
///
/// [issue-63569]: https://github.com/rust-lang/rust/issues/63569
pub fn maybe_uninit_slice_as_ptr<T>(this: &[MaybeUninit<T>]) -> *const T {
    this.as_ptr() as *const T
}

/// Creates a non-null raw slice from a thin pointer and a length.
///
/// The `len` argument is the number of **elements**, not the number of
/// bytes.
///
/// This function is safe, but dereferencing the return value is unsafe.
/// See the documentation of [`std::slice::from_raw_parts`] for slice safety
/// requirements.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#71941][issue-71941]**
///
/// [issue-71941]: https://github.com/rust-lang/rust/issues/71941
pub fn non_null_slice_from_raw_parts<T>(data: NonNull<T>, len: usize) -> NonNull<[T]> {
    // SAFETY: `data` is a `NonNull` pointer which is necessarily non-null
    unsafe { NonNull::<[T]>::new_unchecked(slice_from_raw_parts_mut(data.as_ptr(), len)) }
}
