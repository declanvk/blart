//! A tagged pointer is a pointer (concretely a memory address) with additional
//! data associated with it, such as an indirection bit or reference count. This
//! additional data is often "folded" into the pointer, meaning stored inline in
//! the data representing the address, taking advantage of certain properties of
//! memory addressing.
//!
//! In this case, the tagged pointer will take advantage of the alignment of the
//! pointed-to type, so that it can store several bits of information. For a
//! type with alignment `A`, the number of available bits is `log_2(A)`.

use std::{fmt, marker::PhantomData, mem::align_of, num::NonZeroUsize, ptr::NonNull};

/// A data-carry non-null pointer type.
#[repr(transparent)]
pub struct TaggedPointer<P>(NonZeroUsize, PhantomData<P>);

impl<P> TaggedPointer<P> {
    /// The ABI-required minimum alignment of the `P` type.
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
        let ptr_val = pointer as usize;
        // Double-check that there are no existing bits stored in the data-carrying
        // positions
        assert_eq!(ptr_val & Self::DATA_MASK, 0);
        // store the pointer value stripped of any values in the data-carrying positions
        let stripped_ptr = ptr_val & Self::POINTER_MASK;

        TaggedPointer(
            // SAFETY: TODO
            unsafe { NonZeroUsize::new_unchecked(stripped_ptr) },
            PhantomData,
        )
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
        let ptr_val = self.0.get() & Self::POINTER_MASK;

        ptr_val as *mut _
    }

    /// Consume this tagged pointer and produce the data it carries.
    pub fn to_data(self) -> usize {
        self.0.get() & Self::DATA_MASK
    }

    /// Update the data this tagged pointer carries to a new value.
    ///
    /// # Panics
    ///  - Panics if any bits other than the lowest [`Self::NUM_BITS`] are
    ///    non-zero.
    pub fn set_data(&mut self, data: usize) {
        assert_eq!(
            data & Self::POINTER_MASK,
            0,
            "cannot set more data beyond the lowest NUM_BITS"
        );
        let data = data & Self::DATA_MASK;

        // clear the data bits and then write the new data
        // SAFETY: TODO
        self.0 = unsafe { NonZeroUsize::new_unchecked((self.0.get() & Self::POINTER_MASK) | data) };
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
        self.1.hash(state);
    }
}

impl<P> Ord for TaggedPointer<P> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0).then(self.1.cmp(&other.1))
    }
}

impl<P> PartialOrd for TaggedPointer<P> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(core::cmp::Ordering::Equal) => {},
            ord => return ord,
        }
        self.1.partial_cmp(&other.1)
    }
}

impl<P> Eq for TaggedPointer<P> {}

impl<P> PartialEq for TaggedPointer<P> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<P> Clone for TaggedPointer<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

impl<P> Copy for TaggedPointer<P> {}

impl<P> fmt::Debug for TaggedPointer<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TaggedPointer")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}

impl<P> fmt::Pointer for TaggedPointer<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.to_ptr(), f)
    }
}

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
            Box::from_raw(p1.to_ptr());
            Box::from_raw(p2.to_ptr());
            Box::from_raw(p3.to_ptr());
            Box::from_raw(p4.to_ptr());
            Box::from_raw(p5.to_ptr());
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

        assert_eq!(TaggedPointer::<u128>::ALIGNMENT, 8);
        assert_eq!(TaggedPointer::<u128>::NUM_BITS, 3);
        assert_eq!(
            TaggedPointer::<u128>::POINTER_MASK,
            0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111000usize
        );
    }
}
