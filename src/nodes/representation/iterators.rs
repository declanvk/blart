use super::*;
use std::{
    iter::FusedIterator,
    mem,
    ops::{Bound, Range, RangeBounds},
};

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
    /// Create a new iterator over all the children of the given
    /// [`InnerNodeCompressed`].
    ///
    /// # Safety
    ///
    ///  - The lifetime of the new [`InnerNodeCompressedIter`] must not overlap
    ///    with any operations that mutate the original [`InnerNodeCompressed`].
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
                NonNull::new_unchecked(crate::nightly_rust_apis::maybe_uninit_slice_as_ptr(
                    &node.keys,
                ) as *mut _),
                NonNull::new_unchecked(crate::nightly_rust_apis::maybe_uninit_slice_as_ptr(
                    &node.child_pointers,
                ) as *mut _),
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

    /// Create a new iterator of a specific range of the key bytes of the
    /// children in the given [`InnerNodeCompressed`].
    ///
    /// # Safety
    ///
    ///  - The lifetime of the new [`InnerNodeCompressedIter`] must not overlap
    ///    with any operations that mutate the original [`InnerNodeCompressed`].
    pub unsafe fn range<const SIZE: usize, R: RangeBounds<u8>>(
        node: &InnerNodeCompressed<V, SIZE>,
        range: R,
    ) -> Self {
        // SAFETY: Conditions covered by function safety requirements
        let mut iter = unsafe { Self::new(node) };

        // For the `iter.keys_start` pointer, it should point to the next value that it
        // will return from the iterator. If `iter.keys_start` and `iter.keys_end` are
        // equal, then that indicates an empty iterator.
        //
        // This means that for an iterator over the entire range of the node, the
        // `iter.keys_end` pointer will point to the element one past the
        // end of the `keys` array. This is okay since that pointer will never be
        // accessed.
        //
        // What this means for the `range` constructor is that it needs to up the
        // `_start` and `_end` pointers the same way; `_start` at the next element to
        // return, and `_end` one past the last element to return.

        fn modify_iter_start<const SIZE: usize, V>(
            iter: &mut InnerNodeCompressedIter<V>,
            node: &InnerNodeCompressed<V, SIZE>,
            start_bound: Bound<&u8>,
        ) {
            let (keys, _) = node.initialized_portion();
            let start_key_index = match start_bound {
                Bound::Included(min_key_byte) => match keys.binary_search(min_key_byte) {
                    // The `Ok` case is that it found the matching key byte, so we'll start
                    // iteration at that point. The `Err` case is that it did
                    // not found the key byte, but this is this is where the key byte should have
                    // been, meaning that the element in the index is larger. We'll start the
                    // iteration at that point as well.
                    Ok(idx) | Err(idx) => idx,
                },
                Bound::Excluded(min_key_byte_excluded) => {
                    match keys.binary_search(min_key_byte_excluded) {
                        // Same logic for `Ok` and `Err` applies as above. However, we want to
                        // exclude the index we found, so we add 1 so iteration starts at the next
                        // index. Adding 1 here could take us out of bounds of the keys, we have to
                        // check later on to bound the `_start` pointers back into range.
                        //
                        // TODO: Should be worried about overflow?
                        Ok(idx) | Err(idx) => idx + 1,
                    }
                },
                Bound::Unbounded => {
                    // no modification required, the iterator starts with maximum bounds
                    return;
                },
            };

            if start_key_index == 0 {
                // no modification required, the iterator is already at the start
                return;
            }

            if start_key_index >= node.header.num_children() {
                // The range started beyond the last child pointer, iterator should be empty now
                iter.keys_start = iter.keys_end;
                iter.child_pointers_start = iter.child_pointers_end;
                return;
            }

            // SAFETY: Both instance of `NonNull::new_unchecked` are safe because they are
            // taking inputs that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::add` calls are safe because
            //   - the offset (`start_key_index`) is bounded to the `SIZE` const parameter
            //     which is a `usize`. In practice this value is small (4 and 16).
            //
            //   - The `start_key_index` will range in the `0..=SIZE` range, which means
            //     that the result of the `add` call will be in the range
            //     `iter.keys_start..=(iter.keys_start as usize + SIZE)`. At the max value,
            //     it could take on a value of `iter.keys_start + SIZE`, which would make it
            //     a pointer one byte past the boundary of the original `keys` array. This
            //     applies equally to the `child_pointers_{start,end}` pointers as well
            unsafe {
                iter.keys_start = NonNull::new_unchecked(<*mut u8>::add(
                    iter.keys_start.as_ptr(),
                    start_key_index,
                ));
                iter.child_pointers_start = NonNull::new_unchecked(<*mut OpaqueNodePtr<V>>::add(
                    iter.child_pointers_start.as_ptr(),
                    start_key_index,
                ));
            }
        }

        fn modify_iter_end<const SIZE: usize, V>(
            iter: &mut InnerNodeCompressedIter<V>,
            node: &InnerNodeCompressed<V, SIZE>,
            end_bound: Bound<&u8>,
        ) {
            let (keys, _) = node.initialized_portion();
            let end_key_index = match end_bound {
                Bound::Included(min_key_byte) => match keys.binary_search(min_key_byte) {
                    // The `Ok` case is the same as above, we've found the matching key byte and
                    // want to include it in iteration, so we add one (to go one past the end for
                    // the `_end` pointer).
                    //
                    // The `Err` case is different because instead we've found the element that was
                    // larger than the one we were looking for. We don't actually want to include
                    // this value, so we don't need to add one.
                    Ok(idx) => idx + 1,
                    Err(idx) => idx,
                },
                Bound::Excluded(min_key_byte_excluded) => {
                    // `Ok` and `Err` are same as above and we want to exclude the element we found.
                    // Thus, we leave the index alone since setting the `_end` pointer to an element
                    // means it will be excluded.
                    match keys.binary_search(min_key_byte_excluded) {
                        Ok(idx) | Err(idx) => idx,
                    }
                },
                Bound::Unbounded => {
                    // no modification required
                    return;
                },
            };

            if end_key_index >= node.header.num_children() {
                // no modification required, the iterator is already at the end
                return;
            }

            if end_key_index == 0 {
                // The range end is before the first child pointer, iterator should be empty now
                iter.keys_start = iter.keys_end;
                iter.child_pointers_start = iter.child_pointers_end;
                return;
            }

            let diff_from_end = node.header.num_children() - end_key_index;

            // SAFETY: Both instance of `NonNull::new_unchecked` are safe because they are
            // taking inputs that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::sub` calls are safe because
            //   - the offset (`diff_from_end`) is bounded to the `SIZE` const parameter
            //     which is a `usize`. In practice this value is small (4 and 16).
            //
            //   - The `diff_from_end` will range in the `0..=SIZE` range, which means that
            //     the result of the `sub` call will be in the range
            //     `iter.keys_end..=(iter.keys_end as usize + SIZE)`. At the max value,
            //     `diff_from_end` would be equal to `SIZE`/`num_children` and the
            //     `keys_end` value would be reset to the start of the `keys` allocated
            //     array.
            unsafe {
                iter.keys_end =
                    NonNull::new_unchecked(<*mut u8>::sub(iter.keys_end.as_ptr(), diff_from_end));
                iter.child_pointers_end = NonNull::new_unchecked(<*mut OpaqueNodePtr<V>>::sub(
                    iter.child_pointers_end.as_ptr(),
                    diff_from_end,
                ));
            }
        }

        modify_iter_start(&mut iter, node, range.start_bound());
        modify_iter_end(&mut iter, node, range.end_bound());

        // Safety check so that the iterator does not continue on past the end
        if iter.keys_start > iter.keys_end {
            iter.keys_start = iter.keys_end;
            iter.child_pointers_start = iter.child_pointers_end;
        }

        iter
    }

    /// The remaining number of (key, child_pointer) elements in the
    /// iterator.
    fn len(&self) -> usize {
        self.keys_end.as_ptr().addr() - self.keys_start.as_ptr().addr()
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

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
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

impl<V> From<InnerNodeCompressedIter<V>> for InnerNodeIter<V> {
    fn from(src: InnerNodeCompressedIter<V>) -> Self {
        InnerNodeIter::InnerNodeCompressed(src)
    }
}

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
    ///
    ///  - The lifetime new `InnerBlockerNodeIter` must not overlap with any
    ///    operations that mutate the original [`InnerNode48`].
    pub unsafe fn new(node: &InnerNode48<V>) -> Self {
        let child_pointers_ptr = {
            let child_pointers_slice = node.initialized_child_pointers();

            crate::nightly_rust_apis::non_null_slice_from_raw_parts(
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

    /// Create a new iterator of a specific range of the key bytes of the
    /// children in the given [`InnerNode48`].
    ///
    /// # Safety
    ///
    ///  - The lifetime of the new [`InnerNode48Iter`] must not overlap with any
    ///    operations that mutate the original [`InnerNode48`].
    pub unsafe fn range<R: RangeBounds<u8>>(node: &InnerNode48<V>, range: R) -> Self {
        // SAFETY: Covered by safety conditions on function
        let mut iter = unsafe { Self::new(node) };

        fn modify_iter_start<V>(iter: &mut InnerNode48Iter<V>, start_bound: Bound<&u8>) {
            let start_key_index = match start_bound {
                Bound::Included(min_key_byte) => (*min_key_byte) as usize,
                Bound::Excluded(min_key_byte_excluded) => {
                    // We add 1 so that the value at index `min_key_byte_excluded` will be excluded.
                    *min_key_byte_excluded as usize + 1
                },
                Bound::Unbounded => {
                    // no modification required
                    return;
                },
            };

            if start_key_index == 0 {
                // no modification required, the iterator is already at the start
                return;
            }

            // 256 is the size of the child indices array
            if start_key_index >= 256usize {
                // The range started beyond the last child pointer, iterator should be empty now
                iter.child_indices_range.start = iter.child_indices_range.end;
                return;
            }

            // SAFETY: The `NonNull::new_unchecked` call is safe because it is taking inputs
            // that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::add` calls are safe because
            //   - The `start_key_index` will range in the `0..=255` range, which means that
            //     the result of the `add` call will be in the range
            //     `iter.child_indices_range.start..=(iter.child_indices_range.start as
            //     usize + 255)`. At the max value, it could take on a value of
            //     `iter.child_indices_range.start + 255`, which would make it a pointer to
            //     the last element of the original `child_indices` array. The guard a few
            //     lines up on `>= 256` maintains this.
            unsafe {
                iter.child_indices_range.start =
                    NonNull::new_unchecked(<*mut RestrictedNodeIndex<48>>::add(
                        iter.child_indices_range.start.as_ptr(),
                        start_key_index,
                    ));
            }
        }

        fn modify_iter_end<V>(iter: &mut InnerNode48Iter<V>, end_bound: Bound<&u8>) {
            let end_key_index = match end_bound {
                Bound::Included(min_key_byte) => {
                    // Since we want to include the value, we add one so the pointer will be one
                    // past the end of iteration
                    *min_key_byte as usize + 1
                },
                Bound::Excluded(min_key_byte_excluded) => {
                    // Since we want to exclude the value we leave it alone. The end pointer is
                    // always one past the last index of the array.
                    *min_key_byte_excluded as usize
                },
                Bound::Unbounded => {
                    // no modification required
                    return;
                },
            };

            // 256 is the size of the child indices array
            if end_key_index >= 256usize {
                // no modification required, the iterator is already at the end
                return;
            }

            if end_key_index == 0 {
                // The range end is before the first child pointer, iterator should be empty now
                iter.child_indices_range.start = iter.child_indices_range.end;
                return;
            }

            // The length of the `child_indices` array is 256
            let diff_from_end = 256 - end_key_index;

            // SAFETY: The `NonNull::new_unchecked` call is safe because it is taking inputs
            // that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::sub` calls are safe because
            //   - The `diff_from_end` will range in the `0..=256` range, which means that
            //     the result of the `sub` call will be in the range
            //     `iter.child_indices_range.end..=(iter.child_indices_range.end as usize +
            //     256)`. At the max value, it could take on a value of
            //     `iter.child_indices_range.end + 256`, which would make it a pointer one
            //     byte past the boundary of the original `child_indices` array.
            unsafe {
                iter.child_indices_range.end =
                    NonNull::new_unchecked(<*mut RestrictedNodeIndex<48>>::sub(
                        iter.child_indices_range.end.as_ptr(),
                        diff_from_end,
                    ));
            }
        }

        modify_iter_start(&mut iter, range.start_bound());
        modify_iter_end(&mut iter, range.end_bound());

        // Safety check so that the iterator does not continue on past the end
        if iter.child_indices_range.start > iter.child_indices_range.end {
            iter.child_indices_range.start = iter.child_indices_range.end;
        }

        iter
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
        let max_len = (self.child_indices_range.end.as_ptr().addr()
            - self.child_indices_range.start.as_ptr().addr())
            / mem::size_of::<RestrictedNodeIndex<48>>();

        (0, Some(max_len))
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
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

impl<V> From<InnerNode48Iter<V>> for InnerNodeIter<V> {
    fn from(src: InnerNode48Iter<V>) -> Self {
        InnerNodeIter::InnerNode48(src)
    }
}

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
    ///
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

    /// Create a new iterator of a specific range of the key bytes of the
    /// children in the given [`InnerNode256`].
    ///
    /// # Safety
    ///
    ///  - The lifetime of the new [`InnerNode256Iter`] must not overlap with
    ///    any operations that mutate the original [`InnerNode256`].
    pub unsafe fn range<R: RangeBounds<u8>>(node: &InnerNode256<V>, range: R) -> Self {
        // SAFETY: Covered by function safety requirements
        let mut iter = unsafe { Self::new(node) };

        fn modify_iter_start<V>(iter: &mut InnerNode256Iter<V>, start_bound: Bound<&u8>) {
            let start_key_index = match start_bound {
                Bound::Included(min_key_byte) => (*min_key_byte) as usize,
                Bound::Excluded(min_key_byte_excluded) => {
                    // We add 1 so that the value at index `min_key_byte_excluded` will be excluded.
                    *min_key_byte_excluded as usize + 1
                },
                Bound::Unbounded => {
                    // no modification required
                    return;
                },
            };

            if start_key_index == 0 {
                // no modification required, the iterator is already at the start
                return;
            }

            // 256 is the size of the child pointers array
            if start_key_index >= 256usize {
                // The range started beyond the last child pointer, iterator should be empty now
                iter.child_pointers_range.start = iter.child_pointers_range.end;
                return;
            }

            // SAFETY: The `NonNull::new_unchecked` call is safe because it is taking inputs
            // that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::add` calls are safe because
            //   - The `start_key_index` will range in the `0..=255` range, which means that
            //     the result of the `add` call will be in the range
            //     `iter.child_indices_range.end..=(iter.child_indices_range.end as usize +
            //     255)`. At the max value, it could take on a value of
            //     `iter.child_indices_range.end + 255`, which would make it a pointer to
            //     the last slot of the original `child_indices` array. The guard a few
            //     lines up on `>= 256` maintains this.
            unsafe {
                iter.child_pointers_range.start =
                    NonNull::new_unchecked(<*mut Option<OpaqueNodePtr<V>>>::add(
                        iter.child_pointers_range.start.as_ptr(),
                        start_key_index,
                    ));
            }
        }

        fn modify_iter_end<V>(iter: &mut InnerNode256Iter<V>, end_bound: Bound<&u8>) {
            let end_key_index = match end_bound {
                Bound::Included(min_key_byte) => {
                    // Since we want to include the value, we add one so the pointer will be one
                    // past the end of iteration
                    *min_key_byte as usize + 1
                },
                Bound::Excluded(min_key_byte_excluded) => {
                    // Since we want to exclude the value we leave it alone. The end pointer is
                    // always one past the last index of the array.
                    *min_key_byte_excluded as usize
                },
                Bound::Unbounded => {
                    // no modification required
                    return;
                },
            };

            // 256 is the size of the child pointers array
            if end_key_index >= 256usize {
                // no modification required, the iterator is already at the end
                return;
            }

            if end_key_index == 0 {
                // The range end is before the first child pointer, iterator should be empty now
                iter.child_pointers_range.start = iter.child_pointers_range.end;
                return;
            }

            // The length of the `child_indices` array is 256
            let diff_from_end = 256 - end_key_index;

            // SAFETY: The `NonNull::new_unchecked` call is safe because it is taking inputs
            // that are derived from a `NonNull` pointer and only incremented.
            //
            // The `ptr::sub` calls are safe because
            //   - The `diff_from_end` will range in the `0..=255` range, which means that
            //     the result of the `sub` call will be in the range
            //     `iter.child_indices_range.end..=(iter.child_indices_range.end as usize +
            //     255)`. At the max value, it could take on a value of
            //     `iter.child_indices_range.end + 255`, which would make it a pointer one
            //     byte past the boundary of the original `child_indices` array.
            unsafe {
                iter.child_pointers_range.end =
                    NonNull::new_unchecked(<*mut Option<OpaqueNodePtr<V>>>::sub(
                        iter.child_pointers_range.end.as_ptr(),
                        diff_from_end,
                    ));
            }
        }

        modify_iter_start(&mut iter, range.start_bound());
        modify_iter_end(&mut iter, range.end_bound());

        // Safety check so that the iterator does not continue on past the end
        if iter.child_pointers_range.start > iter.child_pointers_range.end {
            iter.child_pointers_range.start = iter.child_pointers_range.end;
        }

        iter
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

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
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
                //    `ptr::offset` function, which maintains the multiple invariant.
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

impl<V> From<InnerNode256Iter<V>> for InnerNodeIter<V> {
    fn from(src: InnerNode256Iter<V>) -> Self {
        InnerNodeIter::InnerNode256(src)
    }
}

/// A generic iterator that uses specific iterators for each [`NodeType`]
/// (excluding leaves) inside.
pub enum InnerNodeIter<V> {
    /// An iterator over the children of an [`InnerNodeCompressed`] node.
    InnerNodeCompressed(InnerNodeCompressedIter<V>),
    /// An iterator over the childen of an [`InnerNode48`] node.
    InnerNode48(InnerNode48Iter<V>),
    /// An iterator over the childen of an [`InnerNode256`] node.
    InnerNode256(InnerNode256Iter<V>),
}

impl<V> Iterator for InnerNodeIter<V> {
    type Item = (u8, OpaqueNodePtr<V>);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            InnerNodeIter::InnerNodeCompressed(ref mut inner) => inner.next(),
            InnerNodeIter::InnerNode48(ref mut inner) => inner.next(),
            InnerNodeIter::InnerNode256(ref mut inner) => inner.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            InnerNodeIter::InnerNodeCompressed(ref inner) => inner.size_hint(),
            InnerNodeIter::InnerNode48(ref inner) => inner.size_hint(),
            InnerNodeIter::InnerNode256(ref inner) => inner.size_hint(),
        }
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        match self {
            InnerNodeIter::InnerNodeCompressed(inner) => inner.last(),
            InnerNodeIter::InnerNode48(inner) => inner.last(),
            InnerNodeIter::InnerNode256(inner) => inner.last(),
        }
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        match self {
            InnerNodeIter::InnerNodeCompressed(inner) => inner.count(),
            InnerNodeIter::InnerNode48(inner) => inner.count(),
            InnerNodeIter::InnerNode256(inner) => inner.count(),
        }
    }
}

impl<V> DoubleEndedIterator for InnerNodeIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            InnerNodeIter::InnerNodeCompressed(ref mut inner) => inner.next_back(),
            InnerNodeIter::InnerNode48(ref mut inner) => inner.next_back(),
            InnerNodeIter::InnerNode256(ref mut inner) => inner.next_back(),
        }
    }
}

impl<V> FusedIterator for InnerNodeIter<V> {}

#[cfg(test)]
mod tests;
