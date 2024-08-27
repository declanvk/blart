use std::mem::ManuallyDrop;

use crate::{deallocate_leaves, deallocate_tree_non_leaves, NodePtr, RawIterator, TreeMap};

/// An owning iterator over the entries of a `TreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on `TreeMap`
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
#[derive(Debug)]
pub struct IntoIter<K, V, const PREFIX_LEN: usize> {
    inner: RawIterator<K, V, PREFIX_LEN>,
    size: usize,
}

impl<K, V, const PREFIX_LEN: usize> Drop for IntoIter<K, V, PREFIX_LEN> {
    fn drop(&mut self) {
        if let Some(next) = unsafe { self.inner.next() } {
            // SAFETY: TODO
            unsafe { deallocate_leaves(next) }
        }

        // Just to be safe, clear the iterator
        self.inner = RawIterator::empty();
        self.size = 0;
    }
}

impl<K, V, const PREFIX_LEN: usize> IntoIter<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        // We need to inhibit `TreeMap::drop` since it would cause a double-free
        // otherwise.
        let tree = ManuallyDrop::new(tree);

        if let Some(state) = &tree.state {
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
        // SAFETY: TODO
        let leaf_ptr = unsafe { self.inner.next() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY: TODO
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr) }.into_entry()
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoIter<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // SAFETY: TODO
        let leaf_ptr = unsafe { self.inner.next_back() };

        leaf_ptr.map(|leaf_ptr| {
            // SAFETY: TODO
            unsafe { NodePtr::deallocate_node_ptr(leaf_ptr) }.into_entry()
        })
    }
}

/// An owning iterator over the keys of a `TreeMap`.
///
/// This `struct` is created by the [`crate::TreeMap::into_keys`] method on
/// `TreeMap`. See its documentation for more.
pub struct IntoKeys<K, V, const PREFIX_LEN: usize>(IntoIter<K, V, PREFIX_LEN>);

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
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoKeys<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.0)
    }
}

/// An owning iterator over the values of a `TreeMap`.
///
/// This `struct` is created by the [`into_values`] method on `TreeMap`.
/// See its documentation for more.
///
/// [`into_values`]: crate::TreeMap::into_values
pub struct IntoValues<K, V, const PREFIX_LEN: usize>(IntoIter<K, V, PREFIX_LEN>);

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
}

impl<K, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoValues<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.1)
    }
}
