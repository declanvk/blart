use core::{
    iter::FusedIterator,
    mem::{self, ManuallyDrop},
    ptr,
};

use crate::{
    allocator::{Allocator, Global},
    map::DEFAULT_PREFIX_LEN,
    raw::{deallocate_leaves, deallocate_tree_non_leaves, NodePtr, RawIterator},
    TreeMap,
};

/// An owning iterator over the entries of a `TreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on `TreeMap`
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
#[derive(Debug)]
pub struct IntoIter<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
    inner: RawIterator<K, V, PREFIX_LEN>,
    size: usize,
    alloc: A,
}

// SAFETY: This iterator is the unique owner of  the remainder of the `TreeMap`
// it was constructed from and is safe to move across threads, so long as the
// keys and values are as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for IntoIter<K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// threads, so long as the keys and values can be as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for IntoIter<K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Drop for IntoIter<K, V, PREFIX_LEN, A> {
    fn drop(&mut self) {
        // SAFETY:
        //  - The `deallocate_tree_non_leaves` function is called earlier on the trie
        //    (which we have unique access to), so the leaves will still be allocated.
        //  - `self.alloc` was taken from the `TreeMap` and was the same allocator used
        //    to allocate all the nodes of the trie.
        unsafe {
            deallocate_leaves(
                mem::replace(&mut self.inner, RawIterator::empty()),
                &self.alloc,
            )
        }

        // Just to be safe, clear the iterator size
        self.size = 0;
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> IntoIter<K, V, PREFIX_LEN, A> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN, A>) -> Self {
        // We need to inhibit `TreeMap::drop` since it would cause a double-free
        // otherwise.
        let tree = ManuallyDrop::new(tree);
        // SAFETY: Since we're reading from an `&A` that was coerced to a `*const A` we
        // know that the pointer is valid for reads, properly aligned, and properly
        // initialized.
        //
        // Also this is safe from a double-free since we're using `ManuallyDrop` to
        // inhibit the first copy of `A` (in the `tree` value) from doing anything.
        let alloc = unsafe { ptr::read(&tree.alloc) };

        if let Some(state) = &tree.state {
            // SAFETY: By construction (and maintained on insert/delete), the `min_leaf` is
            // always before or equal to `max_leaf` in the leaf node order.
            let inner = unsafe { RawIterator::new(state.min_leaf, state.max_leaf) };

            // SAFETY:
            //  - Since this function takes an owned `TreeMap`, we can assume there is no
            //    concurrent read or modification, that this is a unique handle to the trie.
            //  - `tree.alloc` was used to allocate all the nodes of the tree
            unsafe { deallocate_tree_non_leaves(state.root, &tree.alloc) }

            Self {
                inner,
                size: tree.num_entries,
                alloc,
            }
        } else {
            Self {
                inner: RawIterator::empty(),
                size: 0,
                alloc,
            }
        }
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for IntoIter<K, V, PREFIX_LEN, A> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: By construction of the `IntoIter` we know that we have ownership over
        // the trie, and there will be no other concurrent access (read or write).
        let leaf_ptr = unsafe { self.inner.next() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY:
            //  - This function is only called once for a given `leaf_ptr` since the
            //    iterator will never repeat an element
            //  - `self.alloc` is the same allocator which was used to allocate all the
            //    nodes of the tree, since it was taken from the `TreeMap` value.
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr, &self.alloc) }.into_entry()
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
    for IntoIter<K, V, PREFIX_LEN, A>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        // SAFETY: By construction of the `IntoIter` we know that we have ownership over
        // the trie, and there will be no other concurrent access (read or write).
        let leaf_ptr = unsafe { self.inner.next_back() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY:
            //  - This function is only called once for a given `leaf_ptr` since the
            //    iterator will never repeat an element
            //  - `self.alloc` is the same allocator which was used to allocate all the
            //    nodes of the tree, since it was taken from the `TreeMap` value.
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr, &self.alloc) }.into_entry()
        })
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> ExactSizeIterator
    for IntoIter<K, V, PREFIX_LEN, A>
{
    fn len(&self) -> usize {
        self.size
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> FusedIterator for IntoIter<K, V, PREFIX_LEN, A> {}

/// An owning iterator over the keys of a [`TreeMap`].
///
/// This `struct` is created by the [`crate::TreeMap::into_keys`] method on
/// [`TreeMap`]. See its documentation for more.
pub struct IntoKeys<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>(
    IntoIter<K, V, PREFIX_LEN, A>,
);

impl<K, V, const PREFIX_LEN: usize, A: Allocator> IntoKeys<K, V, PREFIX_LEN, A> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN, A>) -> Self {
        IntoKeys(IntoIter::new(tree))
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for IntoKeys<K, V, PREFIX_LEN, A> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
    for IntoKeys<K, V, PREFIX_LEN, A>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.0)
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> ExactSizeIterator
    for IntoKeys<K, V, PREFIX_LEN, A>
{
}

/// An owning iterator over the values of a [`TreeMap`].
///
/// This `struct` is created by the [`into_values`] method on [`TreeMap`].
/// See its documentation for more.
///
/// [`into_values`]: crate::TreeMap::into_values
pub struct IntoValues<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>(
    IntoIter<K, V, PREFIX_LEN, A>,
);

impl<K, V, const PREFIX_LEN: usize, A: Allocator> IntoValues<K, V, PREFIX_LEN, A> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN, A>) -> Self {
        IntoValues(IntoIter::new(tree))
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for IntoValues<K, V, PREFIX_LEN, A> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
    for IntoValues<K, V, PREFIX_LEN, A>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.1)
    }
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> ExactSizeIterator
    for IntoValues<K, V, PREFIX_LEN, A>
{
}

#[cfg(test)]
mod tests {
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    use crate::{tests_common::swap, AsBytes, NoPrefixesBytes, OrderedBytes};

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn into_iter_is_send<K: Send, V: Send, A: Send + Allocator>() {
            is_send::<IntoIter<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn into_iter_is_sync<K: Sync, V: Sync, A: Sync + Allocator>() {
            is_sync::<IntoIter<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        into_iter_is_send::<[u8; 3], usize, Global>();
        into_iter_is_sync::<[u8; 3], usize, Global>();

        fn into_keys_is_send<K: Send, V: Send, A: Send + Allocator>() {
            is_send::<IntoKeys<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn into_keys_is_sync<K: Sync, V: Sync, A: Sync + Allocator>() {
            is_sync::<IntoKeys<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        into_keys_is_send::<[u8; 3], usize, Global>();
        into_keys_is_sync::<[u8; 3], usize, Global>();

        fn into_values_is_send<K: Send, V: Send, A: Send + Allocator>() {
            is_send::<IntoValues<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn into_values_is_sync<K: Sync, V: Sync, A: Sync + Allocator>() {
            is_sync::<IntoValues<K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        into_values_is_send::<[u8; 3], usize, Global>();
        into_values_is_sync::<[u8; 3], usize, Global>();
    }

    #[derive(Debug)]
    struct DropCounter<T>(Arc<AtomicUsize>, T);

    impl<T> DropCounter<T> {
        fn new(counter: &Arc<AtomicUsize>, value: T) -> Self {
            counter.fetch_add(1, Ordering::Relaxed);
            DropCounter(Arc::clone(counter), value)
        }
    }

    impl<T> Drop for DropCounter<T> {
        fn drop(&mut self) {
            self.0.fetch_sub(1, Ordering::Relaxed);
        }
    }

    impl<T: Ord> Ord for DropCounter<T> {
        fn cmp(&self, other: &Self) -> core::cmp::Ordering {
            self.1.cmp(&other.1)
        }
    }

    impl<T: PartialOrd> PartialOrd for DropCounter<T> {
        fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
            self.1.partial_cmp(&other.1)
        }
    }

    impl<T: Eq> Eq for DropCounter<T> {}

    impl<T: PartialEq> PartialEq for DropCounter<T> {
        fn eq(&self, other: &Self) -> bool {
            self.1 == other.1
        }
    }

    impl<T: AsBytes> AsBytes for DropCounter<T> {
        fn as_bytes(&self) -> &[u8] {
            self.1.as_bytes()
        }
    }

    unsafe impl<T: NoPrefixesBytes> NoPrefixesBytes for DropCounter<T> {}
    unsafe impl<T: OrderedBytes + Ord> OrderedBytes for DropCounter<T> {}

    fn setup_will_deallocate_unconsumed_iter_values(
        drop_counter: &Arc<AtomicUsize>,
    ) -> TreeMap<DropCounter<[u8; 3]>, usize> {
        assert_eq!(drop_counter.load(Ordering::Relaxed), 0);

        [
            [0u8, 0u8, 0u8],
            [0, 0, u8::MAX],
            [0, u8::MAX, 0],
            [0, u8::MAX, u8::MAX],
            [u8::MAX, 0, 0],
            [u8::MAX, 0, u8::MAX],
            [u8::MAX, u8::MAX, 0],
            [u8::MAX, u8::MAX, u8::MAX],
        ]
        .into_iter()
        .map(|arr| DropCounter::new(drop_counter, arr))
        .enumerate()
        .map(swap)
        .collect()
    }

    fn check_will_deallocate_unconsumed_iter_values(
        drop_counter: &Arc<AtomicUsize>,
        mut iter: impl DoubleEndedIterator + ExactSizeIterator,
    ) {
        assert_eq!(drop_counter.load(Ordering::Relaxed), 8);

        assert_eq!(iter.len(), 8);

        assert_eq!(drop_counter.load(Ordering::Relaxed), 8);

        let _ = iter.next().unwrap();
        let _ = iter.next_back().unwrap();

        assert_eq!(drop_counter.load(Ordering::Relaxed), 6);

        drop(iter);

        assert_eq!(drop_counter.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn into_iter_will_deallocate_unconsumed_iter_values() {
        let drop_counter = Arc::new(AtomicUsize::new(0));

        let tree = setup_will_deallocate_unconsumed_iter_values(&drop_counter);

        check_will_deallocate_unconsumed_iter_values(&drop_counter, tree.into_iter());
    }

    #[test]
    fn into_keys_will_deallocate_unconsumed_iter_values() {
        let drop_counter = Arc::new(AtomicUsize::new(0));

        let tree = setup_will_deallocate_unconsumed_iter_values(&drop_counter);

        check_will_deallocate_unconsumed_iter_values(&drop_counter, tree.into_keys());
    }

    #[test]
    fn into_values_will_deallocate_unconsumed_iter_values() {
        let drop_counter = Arc::new(AtomicUsize::new(0));

        let tree = setup_will_deallocate_unconsumed_iter_values(&drop_counter);

        check_will_deallocate_unconsumed_iter_values(&drop_counter, tree.into_values());
    }

    #[test]
    fn empty_tree_empty_iterator() {
        let tree: TreeMap<u8, usize> = TreeMap::new();
        let mut it = tree.into_iter();
        assert_eq!(it.next(), None);
    }
}
