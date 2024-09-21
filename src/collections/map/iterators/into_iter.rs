use std::{
    iter::FusedIterator,
    mem::{self, ManuallyDrop},
};

use crate::{
    deallocate_leaves, deallocate_tree_non_leaves, map::DEFAULT_PREFIX_LEN, NodePtr, RawIterator,
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
pub struct IntoIter<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN> {
    inner: RawIterator<K, V, PREFIX_LEN>,
    size: usize,
}

impl<K, V, const PREFIX_LEN: usize> Drop for IntoIter<K, V, PREFIX_LEN> {
    fn drop(&mut self) {
        // SAFETY: The `deallocate_tree_non_leaves` function is called earlier on the
        // trie (which we have unique access to), so the leaves will still be allocated.
        unsafe { deallocate_leaves(mem::replace(&mut self.inner, RawIterator::empty())) }

        // Just to be safe, clear the iterator size
        self.size = 0;
    }
}

impl<K, V, const PREFIX_LEN: usize> IntoIter<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        // We need to inhibit `TreeMap::drop` since it would cause a double-free
        // otherwise.
        let tree = ManuallyDrop::new(tree);

        if let Some(state) = &tree.state {
            // SAFETY: By construction (and maintained on insert/delete), the `min_leaf` is
            // always before or equal to `max_leaf` in the leaf node order.
            let inner = unsafe { RawIterator::new(state.min_leaf, state.max_leaf) };

            // SAFETY: Since this function takes an owned `TreeMap`, we can assume there is
            // no concurrent read or modification, that this is a unique handle to the trie.
            unsafe { deallocate_tree_non_leaves(state.root) }

            Self {
                inner,
                size: tree.num_entries,
            }
        } else {
            Self {
                inner: RawIterator::empty(),
                size: 0,
            }
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> Iterator for IntoIter<K, V, PREFIX_LEN> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: By construction of the `IntoIter` we know that we have ownership over
        // the trie, and there will be no other concurrent access (read or write).
        let leaf_ptr = unsafe { self.inner.next() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY: This function is only called once for a given `leaf_ptr` since the
            // iterator will never repeat
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr) }.into_entry()
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoIter<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // SAFETY: By construction of the `IntoIter` we know that we have ownership over
        // the trie, and there will be no other concurrent access (read or write).
        let leaf_ptr = unsafe { self.inner.next_back() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY: This function is only called once for a given `leaf_ptr` since the
            // iterator will never repeat
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr) }.into_entry()
        })
    }
}

impl<K, V, const PREFIX_LEN: usize> ExactSizeIterator for IntoIter<K, V, PREFIX_LEN> {
    fn len(&self) -> usize {
        self.size
    }
}

impl<K, V, const PREFIX_LEN: usize> FusedIterator for IntoIter<K, V, PREFIX_LEN> {}

/// An owning iterator over the keys of a [`TreeMap`].
///
/// This `struct` is created by the [`crate::TreeMap::into_keys`] method on
/// [`TreeMap`]. See its documentation for more.
pub struct IntoKeys<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN>(IntoIter<K, V, PREFIX_LEN>);

impl<K, V, const PREFIX_LEN: usize> IntoKeys<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        IntoKeys(IntoIter::new(tree))
    }
}

impl<K, V, const PREFIX_LEN: usize> Iterator for IntoKeys<K, V, PREFIX_LEN> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoKeys<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.0)
    }
}

impl<K, V, const PREFIX_LEN: usize> ExactSizeIterator for IntoKeys<K, V, PREFIX_LEN> {}

/// An owning iterator over the values of a [`TreeMap`].
///
/// This `struct` is created by the [`into_values`] method on [`TreeMap`].
/// See its documentation for more.
///
/// [`into_values`]: crate::TreeMap::into_values
pub struct IntoValues<K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN>(
    IntoIter<K, V, PREFIX_LEN>,
);

impl<K, V, const PREFIX_LEN: usize> IntoValues<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        IntoValues(IntoIter::new(tree))
    }
}

impl<K, V, const PREFIX_LEN: usize> Iterator for IntoValues<K, V, PREFIX_LEN> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoValues<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.1)
    }
}

impl<K, V, const PREFIX_LEN: usize> ExactSizeIterator for IntoValues<K, V, PREFIX_LEN> {}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };

    use crate::{tests_common::swap, AsBytes, NoPrefixesBytes, OrderedBytes};

    use super::*;

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
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.1.cmp(&other.1)
        }
    }

    impl<T: PartialOrd> PartialOrd for DropCounter<T> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
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
