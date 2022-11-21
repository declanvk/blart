//! A tagged pointer is a pointer (concretely a memory address) with additional
//! data associated with it, such as an indirection bit or reference count. This
//! additional data is often "folded" into the pointer, meaning stored inline in
//! the data representing the address, taking advantage of certain properties of
//! memory addressing.
//!
//! In this case, the tagged pointer will take advantage of the alignment of the
//! pointed-to type, so that it can store several bits of information. For a
//! type with alignment `A`, the number of available bits is `log_2(A)`.

use std::{fmt, mem::align_of, ptr::NonNull};

#[cfg(not(feature = "nightly"))]
use sptr::Strict;

/// A non-null pointer type which carries several bits of metadata.
#[repr(transparent)]
pub struct TaggedPointer<P>(NonNull<P>);

impl<P> TaggedPointer<P> {
    /// The ABI-required minimum alignment of the `P` type.
    ///
    /// The maximum alignment of a rust type is 2^29 according to the
    /// [reference][align-reference]. On 32-bit and 64-bit platforms that means
    /// that it is impossible for the POINTER_MASK to be zero, there must be at
    /// least 3 bit present.
    ///
    /// [align-reference]: https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers
    pub const ALIGNMENT: usize = align_of::<P>();
    /// A mask for data-carrying bits of the pointer.
    pub const DATA_MASK: usize = !Self::POINTER_MASK;
    /// Number of available bits of storage in the pointer.
    pub const NUM_BITS: u32 = Self::ALIGNMENT.trailing_zeros();
    /// A mask for the non-data-carrying bits of the pointer.
    pub const POINTER_MASK: usize = usize::MAX << Self::NUM_BITS;

    /// Create a new tagged pointer from a possibly null pointer.
    ///
    /// If the pointer is null, returns None. Otherwise, returns a tagged
    /// pointer.
    ///
    /// # Panics
    ///
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    //
    // The API can take a raw pointer here because it does not derefence the pointer in the body of
    // the function.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn new(pointer: *mut P) -> Option<TaggedPointer<P>> {
        if pointer.is_null() {
            return None;
        }

        // SAFETY: After checking, this pointer is guaranteed to not be null.
        unsafe { Some(Self::new_unchecked(pointer)) }
    }

    /// Create a new non-null tagged pointer without verifying that it is
    /// non-null.
    ///
    /// # Panics
    ///
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    ///
    /// # Safety
    ///
    ///  - The `pointer` value must not be null.
    pub unsafe fn new_unchecked(pointer: *mut P) -> TaggedPointer<P> {
        // SAFETY: The non-zero safety requirement is defered to the caller of this
        // function, who must provide a non-null (non-zero) pointer. This
        // assumes that null is always a zero value.
        let unchecked_ptr = unsafe { NonNull::new_unchecked(pointer) };

        let ptr_addr = unchecked_ptr.as_ptr().addr();

        // Double-check that there are no existing bits stored in the data-carrying
        // positions
        assert_eq!(
            ptr_addr & Self::DATA_MASK,
            0,
            "this pointer was not aligned"
        );

        // After the assert we know that the pointer has no bits set in the lowest
        // couple bits.
        TaggedPointer(unchecked_ptr)
    }

    /// Create a new tagged pointer and immediately set data on it.
    ///
    /// Returns `None` if the given pointer is null.
    ///
    /// # Panics
    ///
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    pub fn new_with_data(pointer: *mut P, data: usize) -> Option<TaggedPointer<P>> {
        let mut tagged_ptr = TaggedPointer::new(pointer)?;
        tagged_ptr.set_data(data);
        Some(tagged_ptr)
    }

    /// Consume this tagged pointer and produce a raw mutable pointer to the
    /// memory location.
    ///
    /// This pointer is guaranteed to be non-null.
    pub fn to_ptr(self) -> *mut P {
        self.0
            .as_ptr()
            .map_addr(|ptr_addr| ptr_addr & Self::POINTER_MASK)
    }

    /// Consume this tagged pointer and produce the data it carries.
    pub fn to_data(self) -> usize {
        let ptr_addr = self.0.as_ptr().addr();
        ptr_addr & Self::DATA_MASK
    }

    /// Update the data this tagged pointer carries to a new value.
    ///
    /// # Panics
    ///  - Panics if any bits other than the lowest [`Self::NUM_BITS`] are
    ///    non-zero in the new `data` value.
    pub fn set_data(&mut self, data: usize) {
        assert_eq!(
            data & Self::POINTER_MASK,
            0,
            "cannot set more data beyond the lowest NUM_BITS"
        );
        let data = data & Self::DATA_MASK;

        let ptr_with_new_data = self
            .0
            .as_ptr()
            .map_addr(|ptr_addr| (ptr_addr & Self::POINTER_MASK) | data);

        // The `ptr_with_new_data` is guaranteed to be non-null because it's pointer
        // address was derived from a non-null pointer using operations that would not
        // have zeroed out the address.
        //
        // The bit-and operation combining the original pointer address (non-null)
        // combined with the POINTER_MASK would not have produced a zero value because
        // the POINTER_MASK value must have the high bits set.
        self.0 = unsafe { NonNull::new_unchecked(ptr_with_new_data) };
    }

    /// Casts to a [`TaggedPointer`] of another type.
    ///
    /// This function will transfer the data bits from the original pointer to
    /// the new pointer.
    ///
    /// # Errors
    ///
    ///  - This function will error if the alignment of the new type does not
    ///    equal the alignment of the existing type. This is because the number
    ///    of data-carrying bits could be different.
    pub fn cast<Q>(self) -> Result<TaggedPointer<Q>, AlignmentCastError> {
        // TODO: Consider allowing casts from smaller to larger alignment, as the number
        // of data-bits could expand.
        if Self::NUM_BITS != TaggedPointer::<Q>::NUM_BITS {
            return Err(AlignmentCastError {
                input_alignment: Self::ALIGNMENT,
                output_alignment: TaggedPointer::<Q>::ALIGNMENT,
            });
        }

        let data = self.to_data();
        let raw_ptr = self.to_ptr();
        let cast_raw_ptr = raw_ptr.cast::<Q>();

        // SAFETY: The `cast_raw_ptr` is guaranteed to be non-null because it is derived
        // from an existing `TaggedPointer` which carries that guarantee.
        let mut new_tagged = unsafe { TaggedPointer::new_unchecked(cast_raw_ptr) };

        new_tagged.set_data(data);

        Ok(new_tagged)
    }
}

impl<P> From<NonNull<P>> for TaggedPointer<P> {
    fn from(pointer: NonNull<P>) -> Self {
        // SAFETY: The pointer produced from the `NonNull::as_ptr` function is
        // guaranteed to be non-null.
        unsafe { Self::new_unchecked(pointer.as_ptr()) }
    }
}

impl<P> From<TaggedPointer<P>> for NonNull<P> {
    fn from(pointer: TaggedPointer<P>) -> Self {
        // SAFETY: The pointer produced by the `TaggedPointer::to_ptr` is guaranteed to
        // be non-null.
        unsafe { NonNull::new_unchecked(pointer.to_ptr()) }
    }
}

impl<P> From<&mut P> for TaggedPointer<P> {
    fn from(reference: &mut P) -> Self {
        // Safety: The pointer is guaranteed to be non-null because it is derived from a
        // reference.
        //
        // Panics: Further, the pointer produced is guaranteed to be aligned for the
        // underlying type, meaning that we will not have any panics.
        unsafe { Self::new_unchecked(reference as *mut _) }
    }
}

impl<P> std::hash::Hash for TaggedPointer<P> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<P> Ord for TaggedPointer<P> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<P> PartialOrd for TaggedPointer<P> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<P> Eq for TaggedPointer<P> {}

impl<P> PartialEq for TaggedPointer<P> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<P> Clone for TaggedPointer<P> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<P> Copy for TaggedPointer<P> {}

impl<P> fmt::Debug for TaggedPointer<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedPointer")
            .field("pointer", &self.to_ptr())
            .field("data", &self.to_data())
            .finish()
    }
}

impl<P> fmt::Pointer for TaggedPointer<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.to_ptr(), f)
    }
}

/// The error type returned when a [`TaggedPointer::cast`] fails because the
/// alignment of the input type and the alignment of the output type are
/// different.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct AlignmentCastError {
    /// The alignment of the input type.
    pub input_alignment: usize,
    /// The alignment of the output type.
    pub output_alignment: usize,
}

impl fmt::Display for AlignmentCastError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "cannot cast tagged pointer to point to a type with a different alignment. Existing \
             type alignment [{}]. Attempted type alignment [{}].",
            self.input_alignment, self.output_alignment
        )
    }
}

impl std::error::Error for AlignmentCastError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_pointer_set_and_retrieve_data() {
        let raw_pointer = Box::into_raw(Box::new(10));

        let mut p = TaggedPointer::new(raw_pointer).unwrap();
        assert_eq!(p.to_data(), 0);

        p.set_data(1);
        assert_eq!(p.to_data(), 1);
        assert_eq!(unsafe { *p.to_ptr() }, 10);

        p.set_data(3);
        assert_eq!(p.to_data(), 3);
        assert_eq!(unsafe { *p.to_ptr() }, 10);

        unsafe { Box::from_raw(p.to_ptr()) };
    }

    #[test]
    fn create_pointer_with_data_and_retrieve_data() {
        let raw_pointer = Box::into_raw(Box::new(30));

        let mut p = TaggedPointer::new_with_data(raw_pointer, 3).unwrap();
        assert_eq!(p.to_data(), 3);
        assert_eq!(unsafe { *p.to_ptr() }, 30);

        p.set_data(0);
        assert_eq!(unsafe { *p.to_ptr() }, 30);
        assert_eq!(p.to_data(), 0);

        unsafe { Box::from_raw(p.to_ptr()) };
    }

    fn set_data_beyond_capacity<P>(mut val: P, too_large_data: usize) {
        let raw_ptr = &mut val as *mut _;
        let mut p = TaggedPointer::new(raw_ptr).unwrap();

        p.set_data(too_large_data);
    }

    #[test]
    #[should_panic]
    fn set_data_beyond_capacity_u8() {
        set_data_beyond_capacity(0u8, 0b1);
    }

    #[test]
    #[should_panic]
    fn set_data_beyond_capacity_u16() {
        set_data_beyond_capacity(0u16, 0b11);
    }

    #[test]
    #[should_panic]
    fn set_data_beyond_capacity_u32() {
        set_data_beyond_capacity(0u32, 0b111);
    }

    #[test]
    #[should_panic]
    fn set_data_beyond_capacity_u64() {
        set_data_beyond_capacity(0u64, 0b1111);
    }

    #[test]
    fn set_data_different_alignments() {
        let mut p1 = TaggedPointer::new(Box::into_raw(Box::new(()))).unwrap();
        let mut p2 = TaggedPointer::new(Box::into_raw(Box::new(2u8))).unwrap();
        let mut p3 = TaggedPointer::new(Box::into_raw(Box::new(3u16))).unwrap();
        let mut p4 = TaggedPointer::new(Box::into_raw(Box::new(4u32))).unwrap();
        let mut p5 = TaggedPointer::new(Box::into_raw(Box::new(5u64))).unwrap();

        assert_eq!(p1.to_data(), 0);
        assert_eq!(unsafe { *p1.to_ptr() }, ());
        p1.set_data(0);
        assert_eq!(p1.to_data(), 0);
        assert_eq!(unsafe { *p1.to_ptr() }, ());

        assert_eq!(p2.to_data(), 0);
        assert_eq!(unsafe { *p2.to_ptr() }, 2);
        p2.set_data(0);
        assert_eq!(p2.to_data(), 0);
        assert_eq!(unsafe { *p2.to_ptr() }, 2);

        assert_eq!(p3.to_data(), 0);
        assert_eq!(unsafe { *p3.to_ptr() }, 3);
        p3.set_data(1);
        assert_eq!(p3.to_data(), 1);
        assert_eq!(unsafe { *p3.to_ptr() }, 3);

        assert_eq!(p4.to_data(), 0);
        assert_eq!(unsafe { *p4.to_ptr() }, 4);
        p4.set_data(3);
        assert_eq!(p4.to_data(), 3);
        assert_eq!(unsafe { *p4.to_ptr() }, 4);

        assert_eq!(p5.to_data(), 0);
        assert_eq!(unsafe { *p5.to_ptr() }, 5);
        p5.set_data(7);
        assert_eq!(p5.to_data(), 7);
        assert_eq!(unsafe { *p5.to_ptr() }, 5);

        unsafe {
            drop(Box::from_raw(p1.to_ptr()));
            drop(Box::from_raw(p2.to_ptr()));
            drop(Box::from_raw(p3.to_ptr()));
            drop(Box::from_raw(p4.to_ptr()));
            drop(Box::from_raw(p5.to_ptr()));
        }
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_alignment_bits_and_mask_values() {
        assert_eq!(TaggedPointer::<()>::ALIGNMENT, 1);
        assert_eq!(TaggedPointer::<()>::NUM_BITS, 0);
        assert_eq!(
            TaggedPointer::<()>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111usize
        );

        assert_eq!(TaggedPointer::<u8>::ALIGNMENT, 1);
        assert_eq!(TaggedPointer::<u8>::NUM_BITS, 0);
        assert_eq!(
            TaggedPointer::<u8>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111usize
        );

        assert_eq!(TaggedPointer::<u16>::ALIGNMENT, 2);
        assert_eq!(TaggedPointer::<u16>::NUM_BITS, 1);
        assert_eq!(
            TaggedPointer::<u16>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111110usize
        );

        assert_eq!(TaggedPointer::<u32>::ALIGNMENT, 4);
        assert_eq!(TaggedPointer::<u32>::NUM_BITS, 2);
        assert_eq!(
            TaggedPointer::<u32>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111100usize
        );

        assert_eq!(TaggedPointer::<u64>::ALIGNMENT, 8);
        assert_eq!(TaggedPointer::<u64>::NUM_BITS, 3);
        assert_eq!(
            TaggedPointer::<u64>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111000usize
        );

        // Something weird about the representation of u128 on intel architectures:
        // https://github.com/rust-lang/rust/issues/54341
        if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
            assert_eq!(
                TaggedPointer::<u128>::ALIGNMENT,
                8,
                "Target architecture [{}]",
                std::env::consts::ARCH
            );
            assert_eq!(TaggedPointer::<u128>::NUM_BITS, 3);

            assert_eq!(
                TaggedPointer::<u128>::POINTER_MASK,
                0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111000usize
            );
        } else {
            assert_eq!(
                TaggedPointer::<u128>::ALIGNMENT,
                16,
                "Target architecture [{}]",
                std::env::consts::ARCH
            );
            assert_eq!(TaggedPointer::<u128>::NUM_BITS, 4);

            assert_eq!(
                TaggedPointer::<u128>::POINTER_MASK,
                0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11110000usize
            );
        }
    }

    #[test]
    fn cast_checks_alignment() {
        let mut p1 = TaggedPointer::new(Box::into_raw(Box::new(1u64))).unwrap();
        let mut p2 = TaggedPointer::new(Box::into_raw(Box::new(2u32))).unwrap();

        p1.set_data(1);
        p2.set_data(2);

        let p1_i64 = p1.cast::<i64>().unwrap();
        assert_eq!(p1_i64.to_data(), 1);
        assert!(p1.cast::<u32>().is_err());
        assert!(p1.cast::<u16>().is_err());
        assert!(p1.cast::<u8>().is_err());

        let p2_i32 = p2.cast::<i32>().unwrap();
        assert_eq!(p2_i32.to_data(), 2);
        assert!(p2.cast::<u64>().is_err());
        assert!(p2.cast::<u16>().is_err());
        assert!(p2.cast::<u8>().is_err());

        unsafe {
            drop(Box::from_raw(p1.to_ptr()));
            drop(Box::from_raw(p2.to_ptr()));
        }
    }
}
