use crate::{LeafNode, NodePtr, TreeIterator, TreeMap};
use std::marker::PhantomData;

macro_rules! impl_ref_mut_iterator {
    ($iter_name:ty, $item:ty $(; $flag:tt)?) => {
        impl<'m, K, V: 'm> Iterator for $iter_name {
            type Item = $item;

            fn next(&mut self) -> Option<Self::Item> {
                self.raw_iter.as_mut()?.next().map(|leaf_node_ptr| {
                    self.size -= 1;

                    Self::map_leaf_ptr_to_item(leaf_node_ptr)
                })
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.size, Some(self.size))
            }

            fn last(mut self) -> Option<Self::Item>
            where
                Self: Sized,
            {
                self.next_back()
            }

            $(
                impl_ref_mut_iterator!($flag);
            )?
        }

        impl<'m, K, V: 'm> DoubleEndedIterator for $iter_name {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.raw_iter.as_mut()?.next_back().map(|leaf_node_ptr| {
                    self.size -= 1;

                    Self::map_leaf_ptr_to_item(leaf_node_ptr)
                })
            }
        }
    };

    (items_are_sorted) => {
        fn max(mut self) -> Option<Self::Item>
            where
                Self: Sized,
                Self::Item: Ord,
        {
            self.next()
        }

        fn min(mut self) -> Option<Self::Item>
            where
                Self: Sized,
                Self::Item: Ord,
        {
            self.next_back()
        }

        #[cfg(feature = "nightly")]
        fn is_sorted(self) -> bool
        where
            Self: Sized,
            Self::Item: PartialOrd,
        {
            true
        }
    };
}

/// An iterator over the entries of a `TreeMap` producing shared references to
/// the key and value.
///
/// This `struct` is created by the [`iter`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`iter`]: TreeMap::iter
pub struct Iter<'m, K, V> {
    _marker: PhantomData<&'m TreeMap<K, V>>,
    raw_iter: Option<TreeIterator<K, V>>,
    size: usize,
}

impl<'m, K, V> Iter<'m, K, V> {
    pub(crate) fn new(tree: &'m TreeMap<K, V>) -> Self {
        Self {
            _marker: PhantomData,
            raw_iter: tree.root.map(|root| unsafe {
                // SAFETY: We have an immutable reference to the `TreeMap` which guarantees that
                // there are not mutable references to the same `TreeMap` and no mutating
                // operations on the nodes of this tree.
                TreeIterator::new(root)
            }),
            size: tree.num_entries,
        }
    }

    fn map_leaf_ptr_to_item(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> <Self as Iterator>::Item {
        // SAFETY: The reference pointing to this leaf will be bounded to the
        // lifetime of the iterator, which itself is bounded to the lifetime of
        // the `TreeMap` it is derived from. Further, the original `TreeMap`
        // reference was an immutable reference, meaning that no mutable reference
        //  currently exists, and will not exist while this immutable reference to the
        // leaf is present.
        let (key, value) = unsafe { leaf_node_ptr.as_key_value_ref() };

        (key, value)
    }
}

impl_ref_mut_iterator!(Iter<'m, K, V>, (&'m K, &'m V) ; items_are_sorted);

/// An iterator over the entries of a `TreeMap` producing shared reference to
/// the key and mutable reference to the value.
///
/// This `struct` is created by the [`iter_mut`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`iter_mut`]: TreeMap::iter_mut
pub struct IterMut<'m, K, V> {
    _marker: PhantomData<&'m mut TreeMap<K, V>>,
    raw_iter: Option<TreeIterator<K, V>>,
    size: usize,
}

impl<'m, K, V> IterMut<'m, K, V> {
    pub(crate) fn new(tree: &'m mut TreeMap<K, V>) -> Self {
        Self {
            _marker: PhantomData,
            raw_iter: tree.root.map(|root| unsafe {
                // SAFETY: We have a mutable reference to the `TreeMap` which guarantees that
                // there are no other references (mutable or immutable) to the same `TreeMap`
                // and thus no mutating operations on the nodes of this tree.
                TreeIterator::new(root)
            }),
            size: tree.num_entries,
        }
    }

    fn map_leaf_ptr_to_item(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> <Self as Iterator>::Item {
        // SAFETY: The reference pointing to this leaf will be bounded to the
        // lifetime of the iterator, which itself is bounded to the lifetime of
        // the `TreeMap` it is derived from. Further, the original `TreeMap`
        // reference was a mutable reference, meaning that no other reference
        // (mutable or immutable) currently exists, and will not exist while
        // this mutable reference to the leaf is present.
        let (key, value) = unsafe { leaf_node_ptr.as_key_ref_value_mut() };

        (key, value)
    }
}

impl_ref_mut_iterator!(IterMut<'m, K, V>, (&'m K, &'m mut V) ; items_are_sorted);

/// An iterator over the keys of a `TreeMap`.
///
/// This `struct` is created by the [`keys`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`keys`]: TreeMap::keys
pub struct Keys<'m, K, V> {
    _marker: PhantomData<&'m TreeMap<K, V>>,
    raw_iter: Option<TreeIterator<K, V>>,
    size: usize,
}

impl<'m, K, V> Keys<'m, K, V> {
    pub(crate) fn new(tree: &'m TreeMap<K, V>) -> Self {
        Self {
            _marker: PhantomData,
            raw_iter: tree.root.map(|root| unsafe {
                // SAFETY: We have an immutable reference to the `TreeMap` which guarantees that
                // there are not mutable references to the same `TreeMap` and no mutating
                // operations on the nodes of this tree.
                TreeIterator::new(root)
            }),
            size: tree.num_entries,
        }
    }

    fn map_leaf_ptr_to_item(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> <Self as Iterator>::Item {
        // SAFETY: The reference pointing to this leaf key will be bounded to the
        // lifetime of the iterator, which itself is bounded to the lifetime of
        // the `TreeMap` it is derived from. Further, the original `TreeMap`
        // reference was an immutable reference, meaning that no mutable reference
        //  currently exists, and will not exist while this immutable reference to the
        // leaf key is present.
        let key = unsafe { leaf_node_ptr.as_key_ref() };

        key
    }
}

impl_ref_mut_iterator!(Keys<'m, K, V>, &'m K ; items_are_sorted);

/// An iterator that produces references to the values of a `TreeMap`.
///
/// This `struct` is created by the [`values`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`values`]: TreeMap::values
pub struct Values<'m, K, V> {
    _marker: PhantomData<&'m TreeMap<K, V>>,
    raw_iter: Option<TreeIterator<K, V>>,
    size: usize,
}

impl<'m, K, V> Values<'m, K, V> {
    pub(crate) fn new(tree: &'m TreeMap<K, V>) -> Self {
        Self {
            _marker: PhantomData,
            raw_iter: tree.root.map(|root| unsafe {
                // SAFETY: We have an immutable reference to the `TreeMap` which guarantees that
                // there are not mutable references to the same `TreeMap` and no mutating
                // operations on the nodes of this tree.
                TreeIterator::new(root)
            }),
            size: tree.num_entries,
        }
    }

    fn map_leaf_ptr_to_item(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> <Self as Iterator>::Item {
        // SAFETY: The reference pointing to this leaf value will be bounded to the
        // lifetime of the iterator, which itself is bounded to the lifetime of
        // the `TreeMap` it is derived from. Further, the original `TreeMap`
        // reference was an immutable reference, meaning that no mutable reference
        //  currently exists, and will not exist while this immutable reference to the
        // leaf value is present.
        unsafe { leaf_node_ptr.as_value_ref() }
    }
}

impl_ref_mut_iterator!(Values<'m, K, V>, &'m V);

/// An iterator that produces mutable references to the values of a `TreeMap`.
///
/// This `struct` is created by the [`values_mut`] method on `TreeMap`. See
/// its documentation for more.
///
/// [`values_mut`]: TreeMap::values_mut
pub struct ValuesMut<'m, K, V> {
    _marker: PhantomData<&'m mut TreeMap<K, V>>,
    raw_iter: Option<TreeIterator<K, V>>,
    size: usize,
}

impl<'m, K, V> ValuesMut<'m, K, V> {
    pub(crate) fn new(tree: &'m mut TreeMap<K, V>) -> Self {
        Self {
            _marker: PhantomData,
            raw_iter: tree.root.map(|root| unsafe {
                // SAFETY: We have a mutable reference to the `TreeMap` which guarantees that
                // there are no other references (mutable or immutable) to the same `TreeMap`
                // and thus no mutating operations on the nodes of this tree.
                TreeIterator::new(root)
            }),
            size: tree.num_entries,
        }
    }

    fn map_leaf_ptr_to_item(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> <Self as Iterator>::Item {
        // SAFETY: The reference pointing to this leaf value will be bounded to the
        // lifetime of the iterator, which itself is bounded to the lifetime of
        // the `TreeMap` it is derived from. Further, the original `TreeMap`
        // reference was a mutable reference, meaning that no other reference
        // (mutable or immutable) currently exists, and will not exist while
        // this mutable reference to the leaf value is present.
        unsafe { leaf_node_ptr.as_value_mut() }
    }
}

impl_ref_mut_iterator!(ValuesMut<'m, K, V>, &'m mut V);

/// An iterator over a sub-range of entries in a `TreeMap`.
///
/// This `struct` is created by the [`range`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`range`]: TreeMap::range
pub struct Range<'a, K, V>(PhantomData<(&'a K, &'a V)>);

impl<'a, K, V> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next_back()
    }

    #[cfg(feature = "nightly")]
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// A mutable iterator over a sub-range of entries in a `TreeMap`.
///
/// This `struct` is created by the [`range_mut`] method on `TreeMap`. See
/// its documentation for more.
///
/// [`range_mut`]: TreeMap::range_mut
pub struct RangeMut<'a, K, V>(PhantomData<(&'a K, &'a mut V)>);

impl<'a, K, V> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next_back()
    }

    #[cfg(feature = "nightly")]
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<'a, K, V> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An iterator produced by calling [`drain_filter`] on `TreeMap`. See its
/// documentation for more.
///
/// [`drain_filter`]: TreeMap::range_mut
pub struct DrainFilter<K, V>(PhantomData<(K, V)>);

impl<K, V> Iterator for DrainFilter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next_back()
    }

    #[cfg(feature = "nightly")]
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<K, V> DoubleEndedIterator for DrainFilter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// An owning iterator over the keys of a `TreeMap`.
///
/// This `struct` is created by the [`into_keys`] method on `TreeMap`.
/// See its documentation for more.
///
/// [`into_keys`]: TreeMap::into_keys
pub struct IntoKeys<K, V>(IntoIter<K, V>);

impl<K, V> IntoKeys<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoKeys(IntoIter::new(tree))
    }
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }
}

impl<K, V> DoubleEndedIterator for IntoKeys<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.0)
    }
}

/// An owning iterator over the values of a `TreeMap`.
///
/// This `struct` is created by the [`into_values`] method on `TreeMap`.
/// See its documentation for more.
///
/// [`into_values`]: TreeMap::into_values
pub struct IntoValues<K, V>(IntoIter<K, V>);

impl<K, V> IntoValues<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoValues(IntoIter::new(tree))
    }
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }
}

impl<K, V> DoubleEndedIterator for IntoValues<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.1)
    }
}

/// An owning iterator over the entries of a `TreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on `TreeMap`
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<K, V>(TreeMap<K, V>);

impl<K, V> IntoIter<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoIter(tree)
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO(#19): Optimize `IntoIter` by not maintaining a valid tree throughout
        // iteration
        self.0.pop_first()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len(), Some(self.0.len()))
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}
