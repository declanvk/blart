//! A tagged pointer is a pointer (concretely a memory address) with additional
//! data associated with it, such as an indirection bit or reference count. This
//! additional data is often "folded" into the pointer, meaning stored inline in
//! the data representing the address, taking advantage of certain properties of
//! memory addressing.
//!
//! In this case, the tagged pointer will take advantage of the alignment of the
//! pointed-to type, so that it can store several bits of information. For a
//! type with alignment `A`, the number of available bits is `log_2(A)`.

use std::{fmt, mem::align_of, num::NonZeroUsize, ptr::NonNull};

use crate::rust_nightly_apis::ptr;

/// A non-null pointer type which carries several bits of metadata.
///
/// The `MIN_BITS` constant is used to ensure that any type that is used with
/// this pointer will have sufficient alignment to carry the specified number of
/// bits. As a result, we can cast safely because we know that the
/// const-evaluation process & type-checking will ensure that the number of bits
/// is sufficient.
#[repr(transparent)]
pub struct TaggedPointer<P, const MIN_BITS: u32>(NonNull<P>);

impl<P, const MIN_BITS: u32> TaggedPointer<P, MIN_BITS> {
    /// The ABI-required minimum alignment of the `P` type.
    ///
    /// The maximum alignment of a rust type is 2^29 according to the
    /// [reference][align-reference]. On 32-bit and 64-bit platforms that means
    /// that it is impossible for the `POINTER_MASK` to be zero, there must be
    /// at least 3 bit present.
    ///
    /// [align-reference]: https://doc.rust-lang.org/reference/type-layout.html#the-alignment-modifiers
    pub const ALIGNMENT: usize = align_of::<P>();
    /// A mask for data-carrying bits of the pointer.
    pub const DATA_MASK: usize = !Self::POINTER_MASK;
    /// Number of available bits of storage in the pointer.
    pub const NUM_BITS: u32 = {
        let num_bits = Self::ALIGNMENT.trailing_zeros();

        assert!(
            num_bits >= MIN_BITS,
            "need the alignment of the pointed to type to have sufficient bits"
        );

        num_bits
    };
    /// A mask for the non-data-carrying bits of the pointer.
    pub const POINTER_MASK: usize = usize::MAX << Self::NUM_BITS;

    /// Create a new tagged pointer from a possibly null pointer.
    ///
    /// If the pointer is null, returns `None`. Otherwise, returns a tagged
    /// pointer.
    ///
    /// # Panics
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    pub fn new(pointer: *mut P) -> Option<TaggedPointer<P, MIN_BITS>> {
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
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    ///
    /// # Safety
    ///  - The `pointer` value must not be null.
    pub unsafe fn new_unchecked(pointer: *mut P) -> TaggedPointer<P, MIN_BITS> {
        // SAFETY: The non-zero safety requirement is deferred to the caller of this
        // function, who must provide a non-null (non-zero) pointer. This
        // assumes that null is always a zero value.
        let unchecked_ptr = unsafe { NonNull::new_unchecked(pointer) };

        let ptr_addr = ptr::mut_addr(unchecked_ptr.as_ptr());

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
    ///  - Panics if the given `pointer` is not aligned according to the minimum
    ///    alignment required for the `P` type.
    pub fn new_with_data(pointer: *mut P, data: usize) -> Option<TaggedPointer<P, MIN_BITS>> {
        let mut tagged_ptr = TaggedPointer::new(pointer)?;
        tagged_ptr.set_data(data);
        Some(tagged_ptr)
    }

    /// Consume this tagged pointer and produce a raw mutable pointer to the
    /// memory location.
    ///
    /// This pointer is guaranteed to be non-null.
    #[inline]
    pub fn to_ptr(self) -> NonNull<P> {
        ptr::nonnull_map_addr(self.0, |ptr_addr|
            // SAFETY:
            //  1. The `new` function requires that the pointer passed is not null
            //  2. The `new_unchecked` function requires that the pointer is aligned such
            //     that the bottom NUM_BITS are all zero.
            // This means that the rest of the bits must be non-zero for the original
            // non-null condition to hold.
            unsafe { NonZeroUsize::new_unchecked(ptr_addr.get() & Self::POINTER_MASK) })
    }

    /// Consume this tagged pointer and produce the data it carries.
    #[inline]
    pub fn to_data(self) -> usize {
        let ptr_addr = ptr::mut_addr(self.0.as_ptr());
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

        self.0 = ptr::nonnull_map_addr(self.0, |ptr_addr| unsafe {
            // SAFETY: The `ptr_with_new_data` is guaranteed to be non-null because it's
            // pointer address was derived from a non-null pointer using
            // operations that would not have zeroed out the address.
            //
            // The bit-and operation combining the original pointer address (non-null)
            // combined with the POINTER_MASK would not have produced a zero value because
            // the POINTER_MASK value must have the high bits set.
            NonZeroUsize::new_unchecked(ptr_addr.get() & Self::POINTER_MASK) | data
        });
    }
}

impl<P, const MIN_BITS: u32> From<NonNull<P>> for TaggedPointer<P, MIN_BITS> {
    fn from(pointer: NonNull<P>) -> Self {
        // SAFETY: The pointer produced from the `NonNull::as_ptr` function is
        // guaranteed to be non-null.
        unsafe { Self::new_unchecked(pointer.as_ptr()) }
    }
}

impl<P, const MIN_BITS: u32> From<TaggedPointer<P, MIN_BITS>> for NonNull<P> {
    fn from(pointer: TaggedPointer<P, MIN_BITS>) -> Self {
        // SAFETY: The pointer produced by the `TaggedPointer::to_ptr` is guaranteed to
        // be non-null.
        unsafe { NonNull::new_unchecked(pointer.to_ptr().as_ptr()) }
    }
}

impl<P, const MIN_BITS: u32> From<&mut P> for TaggedPointer<P, MIN_BITS> {
    fn from(reference: &mut P) -> Self {
        // Safety: The pointer is guaranteed to be non-null because it is derived from a
        // reference.
        //
        // Panics: Further, the pointer produced is guaranteed to be aligned for the
        // underlying type, meaning that we will not have any panics.
        unsafe { Self::new_unchecked(reference as *mut _) }
    }
}

impl<P, const MIN_BITS: u32> std::hash::Hash for TaggedPointer<P, MIN_BITS> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<P, const MIN_BITS: u32> Ord for TaggedPointer<P, MIN_BITS> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<P, const MIN_BITS: u32> PartialOrd for TaggedPointer<P, MIN_BITS> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<P, const MIN_BITS: u32> Eq for TaggedPointer<P, MIN_BITS> {}

impl<P, const MIN_BITS: u32> PartialEq for TaggedPointer<P, MIN_BITS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<P, const MIN_BITS: u32> Clone for TaggedPointer<P, MIN_BITS> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P, const MIN_BITS: u32> Copy for TaggedPointer<P, MIN_BITS> {}

impl<P, const MIN_BITS: u32> fmt::Debug for TaggedPointer<P, MIN_BITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedPointer")
            .field("pointer", &self.to_ptr())
            .field("data", &self.to_data())
            .finish()
    }
}

impl<P, const MIN_BITS: u32> fmt::Pointer for TaggedPointer<P, MIN_BITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.to_ptr(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn successful_tag() {
        let pointee = "Hello world!";
        let pointer = Box::into_raw(Box::new(pointee));
        let tag_data = 0b101usize;

        let mut tagged_pointer =
            TaggedPointer::<&str, 3>::new_with_data(pointer, tag_data).unwrap();

        assert_eq!(unsafe { *tagged_pointer.to_ptr().as_ptr() }, "Hello world!");
        assert_eq!(tagged_pointer.to_data(), 0b101);

        tagged_pointer.set_data(0b010);

        assert_eq!(unsafe { *tagged_pointer.to_ptr().as_ptr() }, "Hello world!");
        assert_eq!(tagged_pointer.to_data(), 0b010);

        // Collecting the data into `Box` to safely drop it
        unsafe {
            drop(Box::from_raw(tagged_pointer.to_ptr().as_ptr()));
        }
    }

    #[test]
    fn create_pointer_set_and_retrieve_data() {
        let raw_pointer = Box::into_raw(Box::new(10));

        let mut p = TaggedPointer::<_, 2>::new(raw_pointer).unwrap();
        assert_eq!(p.to_data(), 0);

        p.set_data(1);
        assert_eq!(p.to_data(), 1);
        assert_eq!(unsafe { *p.to_ptr().as_ptr() }, 10);

        p.set_data(3);
        assert_eq!(p.to_data(), 3);
        assert_eq!(unsafe { *p.to_ptr().as_ptr() }, 10);

        unsafe {
            let _ = Box::from_raw(p.to_ptr().as_ptr());
        };
    }

    #[test]
    fn create_pointer_with_data_and_retrieve_data() {
        let raw_pointer = Box::into_raw(Box::new(30));

        let mut p = TaggedPointer::<_, 2>::new_with_data(raw_pointer, 3).unwrap();
        assert_eq!(p.to_data(), 3);
        assert_eq!(unsafe { *p.to_ptr().as_ptr() }, 30);

        p.set_data(0);
        assert_eq!(unsafe { *p.to_ptr().as_ptr() }, 30);
        assert_eq!(p.to_data(), 0);

        unsafe {
            let _ = Box::from_raw(p.to_ptr().as_ptr());
        };
    }

    #[test]
    #[should_panic = "cannot set more data beyond the lowest NUM_BITS"]
    fn set_data_beyond_capacity_u8() {
        let mut val = 0u8;
        let raw_ptr = &mut val as *mut _;
        let mut p = TaggedPointer::<_, 0>::new(raw_ptr).unwrap();

        p.set_data(0b1);
    }

    #[test]
    #[should_panic = "cannot set more data beyond the lowest NUM_BITS"]
    fn set_data_beyond_capacity_u16() {
        let mut val = 0u16;
        let raw_ptr = &mut val as *mut _;
        let mut p = TaggedPointer::<_, 1>::new(raw_ptr).unwrap();

        p.set_data(0b11);
    }

    #[test]
    #[should_panic = "cannot set more data beyond the lowest NUM_BITS"]
    fn set_data_beyond_capacity_u32() {
        let mut val = 0u32;
        let raw_ptr = &mut val as *mut _;
        let mut p = TaggedPointer::<_, 2>::new(raw_ptr).unwrap();

        p.set_data(0b111);
    }

    #[test]
    #[should_panic = "cannot set more data beyond the lowest NUM_BITS"]
    fn set_data_beyond_capacity_u64() {
        let mut val = 0u64;
        let raw_ptr = &mut val as *mut _;
        let mut p = TaggedPointer::<_, 3>::new(raw_ptr).unwrap();

        p.set_data(0b1111);
    }

    #[test]
    fn set_data_different_alignments() {
        let mut p0 = TaggedPointer::<_, 0>::new(Box::into_raw(Box::<[u8; 0]>::new([]))).unwrap();
        let mut p1 = TaggedPointer::<_, 0>::new(Box::into_raw(Box::new(false))).unwrap();
        let mut p2 = TaggedPointer::<_, 0>::new(Box::into_raw(Box::new(2u8))).unwrap();
        let mut p3 = TaggedPointer::<_, 1>::new(Box::into_raw(Box::new(3u16))).unwrap();
        let mut p4 = TaggedPointer::<_, 2>::new(Box::into_raw(Box::new(4u32))).unwrap();
        let mut p5 = TaggedPointer::<_, 3>::new(Box::into_raw(Box::new(5u64))).unwrap();

        assert_eq!(p0.to_data(), 0);
        assert_eq!(unsafe { *p0.to_ptr().as_ptr() }.len(), 0);
        p0.set_data(0);
        assert_eq!(unsafe { *p0.to_ptr().as_ptr() }.len(), 0);
        assert_eq!(p0.to_data(), 0);

        assert_eq!(p1.to_data(), 0);
        assert!(unsafe { !*p1.to_ptr().as_ptr() });
        p1.set_data(0);
        assert_eq!(p1.to_data(), 0);
        assert!(unsafe { !*p1.to_ptr().as_ptr() });

        assert_eq!(p2.to_data(), 0);
        assert_eq!(unsafe { *p2.to_ptr().as_ptr() }, 2);
        p2.set_data(0);
        assert_eq!(p2.to_data(), 0);
        assert_eq!(unsafe { *p2.to_ptr().as_ptr() }, 2);

        assert_eq!(p3.to_data(), 0);
        assert_eq!(unsafe { *p3.to_ptr().as_ptr() }, 3);
        p3.set_data(1);
        assert_eq!(p3.to_data(), 1);
        assert_eq!(unsafe { *p3.to_ptr().as_ptr() }, 3);

        assert_eq!(p4.to_data(), 0);
        assert_eq!(unsafe { *p4.to_ptr().as_ptr() }, 4);
        p4.set_data(3);
        assert_eq!(p4.to_data(), 3);
        assert_eq!(unsafe { *p4.to_ptr().as_ptr() }, 4);

        assert_eq!(p5.to_data(), 0);
        assert_eq!(unsafe { *p5.to_ptr().as_ptr() }, 5);
        p5.set_data(7);
        assert_eq!(p5.to_data(), 7);
        assert_eq!(unsafe { *p5.to_ptr().as_ptr() }, 5);

        unsafe {
            drop(Box::from_raw(p1.to_ptr().as_ptr()));
            drop(Box::from_raw(p2.to_ptr().as_ptr()));
            drop(Box::from_raw(p3.to_ptr().as_ptr()));
            drop(Box::from_raw(p4.to_ptr().as_ptr()));
            drop(Box::from_raw(p5.to_ptr().as_ptr()));
        }
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_alignment_bits_and_mask_values() {
        assert_eq!(TaggedPointer::<(), 0>::ALIGNMENT, 1);
        assert_eq!(TaggedPointer::<(), 0>::NUM_BITS, 0);
        assert_eq!(
            TaggedPointer::<(), 0>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_usize
        );

        assert_eq!(TaggedPointer::<u8, 0>::ALIGNMENT, 1);
        assert_eq!(TaggedPointer::<u8, 0>::NUM_BITS, 0);
        assert_eq!(
            TaggedPointer::<u8, 0>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_usize
        );

        assert_eq!(TaggedPointer::<u16, 1>::ALIGNMENT, 2);
        assert_eq!(TaggedPointer::<u16, 1>::NUM_BITS, 1);
        assert_eq!(
            TaggedPointer::<u16, 1>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1110_usize
        );

        assert_eq!(TaggedPointer::<u32, 2>::ALIGNMENT, 4);
        assert_eq!(TaggedPointer::<u32, 2>::NUM_BITS, 2);
        assert_eq!(
            TaggedPointer::<u32, 2>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1100_usize
        );

        assert_eq!(TaggedPointer::<u64, 3>::ALIGNMENT, 8);
        assert_eq!(TaggedPointer::<u64, 3>::NUM_BITS, 3);
        assert_eq!(
            TaggedPointer::<u64, 3>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1000_usize
        );

        // Something weird about the representation of u128 on intel architectures:
        // https://github.com/rust-lang/rust/issues/54341 - This was fixed in 1.77
        assert_eq!(
            TaggedPointer::<u128, 5>::ALIGNMENT,
            16,
            "Target architecture [{}]",
            std::env::consts::ARCH
        );
        assert_eq!(TaggedPointer::<u128, 3>::NUM_BITS, 4);

        assert_eq!(
            TaggedPointer::<u128, 3>::POINTER_MASK,
            0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_0000_usize
        );
    }
}
