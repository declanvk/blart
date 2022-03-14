use super::*;
use std::{iter::FusedIterator, mem, ops::Range};

/// An iterator all the children of an [`InnerNodeCompressed`].
///
/// # Safety
///
///  - The lifetime of this struct must not overlap with any mutating operations
///    of the node.
//  - All the `NonNull` pointers in this struct are constructed from shared
//    references and must not be used to mutate.
pub struct InnerNodeCompressedIter<V> {
    keys_start: NonNull<u8>,
    keys_end: NonNull<u8>,
    child_pointers_start: NonNull<OpaqueNodePtr<V>>,
    child_pointers_end: NonNull<OpaqueNodePtr<V>>,
}

impl<V> InnerNodeCompressedIter<V> {
    /// Create a new iterator over the children of the given
    /// [`InnerNodeCompressed`].
    ///
    /// # Safety
    ///  - The lifetime new `InnerBlockerNodeIter` must not overlap with any
    ///    operations that mutate the original [`InnerNodeCompressed`].
    pub unsafe fn new<const SIZE: usize>(node: &InnerNodeCompressed<V, SIZE>) -> Self {
        // SAFETY:
        //  - The pointers are guaranteed to be not null since it is derived from a
        //    reference
        //  - The `MaybeUninit::as_ptr` here is safe for a couple reasons:
        //      - The `node.header.num_children`-sized prefix of the `node.keys` and
        //        `node.child_pointers` arrays are guaranteed to be initialized, see
        //        `InnerNodeCompressed` comments.
        //      - We never access the maybe initialized first value (in case of no
        //        children in node) until we verify the number of children, after which
        //        the value is known to be initialized.
        let (keys_start, child_pointers_start) = unsafe {
            (
                NonNull::new_unchecked(MaybeUninit::as_ptr(&node.keys[0]) as *mut _),
                NonNull::new_unchecked(MaybeUninit::as_ptr(&node.child_pointers[0]) as *mut _),
            )
        };

        let (keys_end, child_pointers_end) = unsafe {
            // SAFETY:
            //   - The pointers are known to not be null because they are derived from a
            //     NonNull pointer
            //   - The starting pointer is within the bounds of the original array
            //     allocation
            //   - The ending pointer is less than or equal to start pointer + the number of
            //     initialized children. This is guaranteed to be within the array
            //     allocations or at the very end.
            //   - The offset cannot overflow an isize, because the maximum number of
            //     children in a given node is 256.
            (
                NonNull::new_unchecked(<*mut u8>::add(
                    keys_start.as_ptr(),
                    usize::from(node.header.num_children),
                )),
                NonNull::new_unchecked(<*mut OpaqueNodePtr<V>>::add(
                    child_pointers_start.as_ptr(),
                    usize::from(node.header.num_children),
                )),
            )
        };

        InnerNodeCompressedIter {
            keys_start,
            keys_end,
            child_pointers_start,
            child_pointers_end,
        }
    }

    /// The remaining number of (key, child_pointer) elements in the
    /// iterator.
    fn len(&self) -> usize {
        self.keys_end.as_ptr() as usize - self.keys_start.as_ptr() as usize
    }

    /// Save the value of the iterator start pointers, then increment them.
    /// Return the old value of the iterator start pointers.
    ///
    /// # Safety
    ///
    ///  - The `offset` must be less than or equal to the remaining number of
    ///    elements in the iterator.
    unsafe fn post_inc_start(&mut self, offset: isize) -> (*const u8, *const OpaqueNodePtr<V>) {
        let old_keys_start = self.keys_start.as_ptr();
        let old_child_pointers_start = self.child_pointers_start.as_ptr();

        // SAFETY: the caller guarantees that `offset` doesn't exceed `self.len()`,
        // so this new pointer is inside `self`.
        self.keys_start = unsafe { NonNull::new(self.keys_start.as_ptr().offset(offset)).unwrap() };
        self.child_pointers_start =
            unsafe { NonNull::new(self.child_pointers_start.as_ptr().offset(offset)).unwrap() };

        (old_keys_start, old_child_pointers_start)
    }

    /// Decrement the iterator end pointers by the `offset` value, then
    /// return their new value.
    ///
    /// # Safety
    ///
    ///  - The `offset` must be less than or equal to the remaining number of
    ///    elements in the iterator.
    unsafe fn pre_dec_end(&mut self, offset: isize) -> (*const u8, *const OpaqueNodePtr<V>) {
        // SAFETY: the caller guarantees that `offset` doesn't exceed `self.len()`,
        // which is guaranteed to not overflow an `isize`. Also, the resulting pointer
        // is in bounds of `slice`, which fulfills the other requirements for `offset`.
        // SAFETY: the caller guarantees that `offset` doesn't exceed `self.len()`,
        // so this new pointer is inside `self` and thus guaranteed to be non-null.
        self.keys_end = unsafe { NonNull::new(self.keys_end.as_ptr().offset(-offset)).unwrap() };
        self.child_pointers_end =
            unsafe { NonNull::new(self.child_pointers_end.as_ptr().offset(-offset)).unwrap() };

        (self.keys_end.as_ptr(), self.child_pointers_end.as_ptr())
    }
}

impl<V> Iterator for InnerNodeCompressedIter<V> {
    type Item = (u8, OpaqueNodePtr<V>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.keys_start == self.keys_end {
            return None;
        }

        // SAFETY: By confirming that the start and end pointers are not equal, there is
        // at least 1 element of difference between them, making this offset choice
        // safe.
        let (keys_ptr, child_pointer_ptr) = unsafe { self.post_inc_start(1) };

        Some(
            // SAFETY: Both reads are safe because:
            //  - key byte and child pointer are initialized, see constructor
            //  - key byte and child pointer are derived from a reference, so valid for reads as
            //    long as it is in-bounds (which it is, from the if statement at the start of the
            //    function)
            unsafe { (keys_ptr.read(), child_pointer_ptr.read()) },
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();

        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }
}

impl<V> DoubleEndedIterator for InnerNodeCompressedIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.keys_start == self.keys_end {
            return None;
        }

        // SAFETY: By confirming that the start and end pointers are not equal, there is
        // at least 1 element of difference between them, making this offset choice
        // safe.
        let (keys_ptr, child_pointer_ptr) = unsafe { self.pre_dec_end(1) };

        Some(
            // SAFETY: Both reads are safe because:
            //  - key byte and child pointer are initialized, see constructor
            //  - key byte and child pointer are derived from a reference, so valid for reads as
            //    long as it is in-bounds (which it is, from the if statement at the start of the
            //    function)
            unsafe { (keys_ptr.read(), child_pointer_ptr.read()) },
        )
    }
}

impl<V> FusedIterator for InnerNodeCompressedIter<V> {}

/// An iterator over all the children of a [`InnerNode48`].
// All the `NonNull` pointers in this struct are constructed from shared
// references and must not be used to mutate.
pub struct InnerNode48Iter<V> {
    original_child_indices_start: NonNull<RestrictedNodeIndex<48>>,
    child_indices_range: Range<NonNull<RestrictedNodeIndex<48>>>,
    child_pointers_ptr: NonNull<[OpaqueNodePtr<V>]>,
}

impl<V> InnerNode48Iter<V> {
    /// Create a new iterator over the children of the given [`InnerNode48`].
    ///
    /// # Safety
    ///  - The lifetime new `InnerBlockerNodeIter` must not overlap with any
    ///    operations that mutate the original [`InnerNode48`].
    pub unsafe fn new(node: &InnerNode48<V>) -> Self {
        let child_pointers_ptr = {
            let child_pointers_slice = node.initialized_child_pointers();

            NonNull::slice_from_raw_parts(
                NonNull::new(child_pointers_slice.as_ptr() as *mut _).unwrap(),
                child_pointers_slice.len(),
            )
        };

        let child_indices_range = {
            let slice_range = node.child_indices.as_ptr_range();
            Range {
                start: NonNull::new(slice_range.start as *mut _).unwrap(),
                end: NonNull::new(slice_range.end as *mut _).unwrap(),
            }
        };

        InnerNode48Iter {
            original_child_indices_start: child_indices_range.start,
            child_pointers_ptr,
            child_indices_range,
        }
    }
}

impl<V> Iterator for InnerNode48Iter<V> {
    type Item = (u8, OpaqueNodePtr<V>);

    fn next(&mut self) -> Option<Self::Item> {
        while !self.child_indices_range.is_empty() {
            let next_ptr = {
                let child_indices_start = self.child_indices_range.start.as_ptr();

                // SAFETY: Because we checked the loop condition, we know there is at least 1
                // more element in the iterator. This means that the resulting pointer is within
                // the bounds of the original allocation, and the starting pointer is within the
                // bounds by construction of the iterator.
                self.child_indices_range.start = unsafe {
                    NonNull::new(self.child_indices_range.start.as_ptr().offset(1)).unwrap()
                };

                child_indices_start
            };

            // SAFETY: This read is safe because the old value of the
            // `child_indices_range.start` is initialized (as the `child_indices` array is
            // initialized at creation), valid for reads (the pointers are derived from a
            // shared reference and guaranteed to be in bounds).
            let next_index = unsafe { next_ptr.read() };
            if next_index != RestrictedNodeIndex::<48>::EMPTY {
                // SAFETY:
                //  - The `child_pointers_ptr` is de-referenceable and the `next_index` is
                //    within the bounds of the slice because of the construction of the
                //    `InnerNode48` type.
                //  - The `read` is safe because:
                //      - The pointer is valid for reads, no other exclusive reference is held
                //      - The value is initialized because the original slice is derived from
                //        `initialized_child_pointers`, which returns the initialized portion of
                //        the `child_pointers` array.
                let child_pointer = unsafe {
                    self.child_pointers_ptr
                        .get_unchecked_mut(usize::from(u8::from(next_index)))
                        .as_ptr()
                        .read()
                };

                // SAFETY:
                //  - Both the starting and original pointer are from the same `child_indices`
                //    array and are in-bounds by construction.
                //  - The distance between pointers is a multiple of `RestrictedIndexNodeIndex`
                //    because we have only incremented or decremented the pointer using the
                //    `ptr::offset` function, which maintains the multiple unvariant.
                // PANIC SAFETY:
                //  - This function will not panic because the maximum distance from the start
                //    to the end is 255, which will not overflow a u8.
                let key_byte = unsafe {
                    u8::try_from(next_ptr.offset_from(self.original_child_indices_start.as_ptr()))
                        .unwrap()
                };

                return Some((key_byte, child_pointer));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let max_len = (self.child_indices_range.end.as_ptr() as usize
            - self.child_indices_range.start.as_ptr() as usize)
            / mem::size_of::<RestrictedNodeIndex<48>>();

        (0, Some(max_len))
    }
}

impl<V> DoubleEndedIterator for InnerNode48Iter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.child_indices_range.is_empty() {
            let next_ptr = {
                // SAFETY: Because we checked the loop condition, we know there is at least 1
                // more element in the iterator. This means that the resulting pointer is within
                // the bounds of the original allocation, and the starting pointer is within the
                // bounds by construction of the iterator.
                self.child_indices_range.end = unsafe {
                    NonNull::new(self.child_indices_range.end.as_ptr().offset(-1)).unwrap()
                };

                self.child_indices_range.end.as_ptr()
            };

            // SAFETY: This read is safe because the old value of the
            // `child_indices_range.start` is initialized (as the `child_indices` array is
            // initialized at creation), valid for reads (the pointers are derived from a
            // shared reference and guaranteed to be in bounds).
            let next_index = unsafe { next_ptr.read() };
            if next_index != RestrictedNodeIndex::<48>::EMPTY {
                // SAFETY:
                //  - The `child_pointers_ptr` is de-referenceable and the `next_index` is
                //    within the bounds of the slice because of the construction of the
                //    `InnerNode48` type.
                //  - The `read` is safe because:
                //      - The pointer is valid for reads, no other exclusive reference is held
                //      - The value is initialized because the original slice is derived from
                //        `initialized_child_pointers`, which returns the initialized portion of
                //        the `child_pointers` array.
                let child_pointer = unsafe {
                    self.child_pointers_ptr
                        .get_unchecked_mut(usize::from(u8::from(next_index)))
                        .as_ptr()
                        .read()
                };

                // SAFETY:
                //  - Both the starting and original pointer are from the same `child_indices`
                //    array and are in-bounds by construction.
                //  - The distance between pointers is a multiple of `RestrictedIndexNodeIndex`
                //    because we have only incremented or decremented the pointer using the
                //    `ptr::offset` function, which maintains the multiple unvariant.
                // PANIC SAFETY:
                //  - This function will not panic because the maximum distance from the start
                //    to the end is 255, which will not overflow a u8.
                let key_byte = unsafe {
                    u8::try_from(next_ptr.offset_from(self.original_child_indices_start.as_ptr()))
                        .unwrap()
                };

                return Some((key_byte, child_pointer));
            }
        }

        None
    }
}

impl<V> FusedIterator for InnerNode48Iter<V> {}

/// An iterator over all the children of a [`InnerNode256`].
// All the `NonNull` pointers in this struct are constructed from shared
// references and must not be used to mutate.
pub struct InnerNode256Iter<V> {
    original_child_pointers_start: NonNull<Option<OpaqueNodePtr<V>>>,
    child_pointers_range: Range<NonNull<Option<OpaqueNodePtr<V>>>>,
}

impl<V> InnerNode256Iter<V> {
    /// Create a new iterator over the children of the given [`InnerNode48`].
    ///
    /// # Safety
    ///  - The lifetime new `InnerBlockerNodeIter` must not overlap with any
    ///    operations that mutate the original [`InnerNode48`].
    pub unsafe fn new(node: &InnerNode256<V>) -> Self {
        let child_pointers_range = {
            let slice_range = node.child_pointers.as_ptr_range();
            Range {
                start: NonNull::new(slice_range.start as *mut _).unwrap(),
                end: NonNull::new(slice_range.end as *mut _).unwrap(),
            }
        };

        InnerNode256Iter {
            original_child_pointers_start: child_pointers_range.start,
            child_pointers_range,
        }
    }
}

impl<V> Iterator for InnerNode256Iter<V> {
    type Item = (u8, OpaqueNodePtr<V>);

    fn next(&mut self) -> Option<Self::Item> {
        while !self.child_pointers_range.is_empty() {
            let next_ptr = {
                let child_indices_start = self.child_pointers_range.start.as_ptr();

                // SAFETY: Because we checked the loop condition, we know there is at least 1
                // more element in the iterator. This means that the resulting pointer is within
                // the bounds of the original allocation, and the starting pointer is within the
                // bounds by construction of the iterator.
                self.child_pointers_range.start = unsafe {
                    NonNull::new(self.child_pointers_range.start.as_ptr().offset(1)).unwrap()
                };

                child_indices_start
            };

            let next_child = unsafe { next_ptr.read() };
            if let Some(next_child) = next_child {
                // SAFETY:
                //  - Both the starting and original pointer are from the same `child_indices`
                //    array and are in-bounds by construction.
                //  - The distance between pointers is a multiple of `RestrictedIndexNodeIndex`
                //    because we have only incremented or decremented the pointer using the
                //    `ptr::offset` function, which maintains the multiple unvariant.
                // PANIC SAFETY:
                //  - This function will not panic because the maximum distance from the start
                //    to the end is 255, which will not overflow a u8.
                let key_byte = unsafe {
                    u8::try_from(next_ptr.offset_from(self.original_child_pointers_start.as_ptr()))
                        .unwrap()
                };

                return Some((key_byte, next_child));
            }
        }

        None
    }
}

impl<V> DoubleEndedIterator for InnerNode256Iter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.child_pointers_range.is_empty() {
            let next_ptr = {
                // SAFETY: Because we checked the loop condition, we know there is at least 1
                // more element in the iterator. This means that the resulting pointer is within
                // the bounds of the original allocation, and the starting pointer is within the
                // bounds by construction of the iterator.
                self.child_pointers_range.end = unsafe {
                    NonNull::new(self.child_pointers_range.end.as_ptr().offset(-1)).unwrap()
                };

                self.child_pointers_range.end.as_ptr()
            };

            let next_child = unsafe { next_ptr.read() };
            if let Some(next_child) = next_child {
                // SAFETY:
                //  - Both the starting and original pointer are from the same `child_indices`
                //    array and are in-bounds by construction.
                //  - The distance between pointers is a multiple of `RestrictedIndexNodeIndex`
                //    because we have only incremented or decremented the pointer using the
                //    `ptr::offset` function, which maintains the multiple unvariant.
                // PANIC SAFETY:
                //  - This function will not panic because the maximum distance from the start
                //    to the end is 255, which will not overflow a u8.
                let key_byte = unsafe {
                    u8::try_from(next_ptr.offset_from(self.original_child_pointers_start.as_ptr()))
                        .unwrap()
                };

                return Some((key_byte, next_child));
            }
        }

        None
    }
}

impl<V> FusedIterator for InnerNode256Iter<V> {}
