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
#[inline(always)]
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
#[inline(always)]
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
#[allow(dead_code)]
#[inline(always)]
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
#[allow(dead_code)]
#[inline(always)]
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
#[inline(always)]
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
#[cfg(feature = "nightly")]
#[inline(always)]
pub const fn maybe_uninit_uninit_array<T, const N: usize>() -> [std::mem::MaybeUninit<T>; N] {
    std::mem::MaybeUninit::uninit_array()
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
#[cfg(not(feature = "nightly"))]
#[inline(always)]
pub fn maybe_uninit_uninit_array<T, const N: usize>() -> [std::mem::MaybeUninit<T>; N] {
    std::array::from_fn(|_| std::mem::MaybeUninit::uninit())
}

/// Constructs a new boxed slice with uninitialized contents.
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63291][issue-63291]**
///
/// [issue-63291]: https://github.com/rust-lang/rust/issues/63291
#[inline(always)]
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

/// Converts to `Box<[T], A>`.
///
/// # Safety
///
/// As with [`MaybeUninit::assume_init`],
/// it is up to the caller to guarantee that the values
/// really are in an initialized state.
/// Calling this when the content is not yet fully initialized
/// causes immediate undefined behavior.
///
/// [`MaybeUninit::assume_init`]: std::mem::MaybeUninit::assume_init
///
/// **This is a unstable API copied from the Rust standard library, tracking
/// issue is [#63291][issue-63291]**
///
/// [issue-63291]: https://github.com/rust-lang/rust/issues/63291
#[inline(always)]
pub unsafe fn box_assume_init<T>(b: Box<[std::mem::MaybeUninit<T>]>) -> Box<[T]> {
    #[cfg(feature = "nightly")]
    {
        // SAFETY: Covered by condition of containing function
        unsafe { b.assume_init() }
    }

    #[cfg(not(feature = "nightly"))]
    {
        let raw = Box::into_raw(b);
        // SAFETY: Covered by condition of containing function
        unsafe { Box::from_raw(raw as *mut [T]) }
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
