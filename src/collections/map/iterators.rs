use crate::{AsBytes, ConcreteNodePtr, InnerNode, NodePtr, OpaqueNodePtr, TreeMap};
use std::{collections::VecDeque, iter::FusedIterator};

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s in a non-singleton tree.
        ///
        /// Non-singleton here means that the tree has at least one `InnerNode`.
        ///
        /// # Safety
        ///
        /// This iterator maintains pointers to internal nodes from the trie. No
        /// mutating operation can occur while this an instance of the iterator is live.
        pub struct $name<'a, K: AsBytes, V> {
            nodes: VecDeque<OpaqueNodePtr<K, V>>,
            size: usize,
            _tree: $tree,
        }

        impl<'a, K: AsBytes, V> $name<'a, K, V> {
            /// Create a new iterator that will visit all leaf nodes descended from the
            /// given node.
            pub fn new(tree: $tree) -> Self {
                Self {
                    nodes: tree.root.into_iter().collect(),
                    size: tree.num_entries,
                    _tree: tree,
                }
            }

            fn push_back_rev_iter<N>(&mut self, inner: NodePtr<N>)
            where
                N: InnerNode<Key = K, Value = V>,
            {
                unsafe {
                    inner
                        .as_ref()
                        .iter()
                        .rev()
                        .for_each(|(_, n)| self.nodes.push_back(n))
                };
            }

            fn push_front<N>(&mut self, inner: NodePtr<N>)
            where
                N: InnerNode<Key = K, Value = V>,
            {
                unsafe {
                    inner
                        .as_ref()
                        .iter()
                        .for_each(|(_, n)| self.nodes.push_front(n))
                };
            }
        }

        impl<'a, K: AsBytes, V> Iterator for $name<'a, K, V> {
            type Item = $ret;

            fn next(&mut self) -> Option<Self::Item> {
                while let Some(node) = self.nodes.pop_back() {
                    match node.to_node_ptr() {
                        ConcreteNodePtr::Node4(inner) => self.push_back_rev_iter(inner),
                        ConcreteNodePtr::Node16(inner) => self.push_back_rev_iter(inner),
                        ConcreteNodePtr::Node48(inner) => self.push_back_rev_iter(inner),
                        ConcreteNodePtr::Node256(inner) => self.push_back_rev_iter(inner),
                        ConcreteNodePtr::LeafNode(inner) => {
                            self.size -= 1;
                            return unsafe { Some(inner.$op()) };
                        },
                    }
                }

                None
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
        }

        impl<'a, K: AsBytes, V> DoubleEndedIterator for $name<'a, K, V> {
            fn next_back(&mut self) -> Option<Self::Item> {
                while let Some(node) = self.nodes.pop_front() {
                    match node.to_node_ptr() {
                        ConcreteNodePtr::Node4(inner) => self.push_front(inner),
                        ConcreteNodePtr::Node16(inner) => self.push_front(inner),
                        ConcreteNodePtr::Node48(inner) => self.push_front(inner),
                        ConcreteNodePtr::Node256(inner) => self.push_front(inner),
                        ConcreteNodePtr::LeafNode(inner) => {
                            self.size -= 1;
                            return unsafe { Some(inner.$op()) };
                        },
                    }
                }

                None
            }
        }

        impl<'a, K: AsBytes, V> FusedIterator for $name<'a, K, V> {}

        impl<'a, K: AsBytes, V> ExactSizeIterator for $name<'a, K, V> {
            fn len(&self) -> usize {
                self.size
            }
        }
    };
}

gen_iter!(
    TreeIterator,
    &'a TreeMap<K, V>,
    (&'a K, &'a V),
    as_key_value_ref
);
gen_iter!(
    TreeIteratorMut,
    &'a mut TreeMap<K, V>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);
gen_iter!(Keys, &'a TreeMap<K, V>, &'a K, as_key_ref);
gen_iter!(Values, &'a TreeMap<K, V>, &'a V, as_value_ref);
gen_iter!(ValuesMut, &'a mut TreeMap<K, V>, &'a mut V, as_value_mut);

/*
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
*/

// /// An iterator produced by calling [`drain_filter`] on `TreeMap`. See its
// /// documentation for more.
// ///
// /// [`drain_filter`]: TreeMap::range_mut
// pub struct ExtractIf<K, V>(PhantomData<(K, V)>);

// impl<K, V> Iterator for ExtractIf<K, V> {
//     type Item = (K, V);

//     fn next(&mut self) -> Option<Self::Item> {
//         todo!()
//     }
// }

/// An owning iterator over the keys of a `TreeMap`.
///
/// This `struct` is created by the [`TreeMap::into_keys`] method on `TreeMap`.
/// See its documentation for more.
pub struct IntoKeys<K: AsBytes, V>(IntoIter<K, V>);

impl<K: AsBytes, V> IntoKeys<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoKeys(IntoIter::new(tree))
    }
}

impl<K: AsBytes, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }
}

impl<K: AsBytes, V> DoubleEndedIterator for IntoKeys<K, V> {
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
pub struct IntoValues<K: AsBytes, V>(IntoIter<K, V>);

impl<K: AsBytes, V> IntoValues<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoValues(IntoIter::new(tree))
    }
}

impl<K: AsBytes, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }
}

impl<K: AsBytes, V> DoubleEndedIterator for IntoValues<K, V> {
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
pub struct IntoIter<K: AsBytes, V>(TreeMap<K, V>);

impl<K: AsBytes, V> IntoIter<K, V> {
    pub(crate) fn new(tree: TreeMap<K, V>) -> Self {
        IntoIter(tree)
    }
}

impl<K: AsBytes, V> Iterator for IntoIter<K, V> {
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

impl<K: AsBytes, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::tests_common::generate_key_fixed_length;

    #[test]
    fn small_tree_iterator_front_and_back() {
        let keys: [Box<[u8]>; 9] = [
            vec![114, 159, 30].into_boxed_slice(),  // 0
            vec![30, 159, 204].into_boxed_slice(),  // 1
            vec![92, 39, 116].into_boxed_slice(),   // 2
            vec![58, 7, 66].into_boxed_slice(),     // 3
            vec![70, 30, 139].into_boxed_slice(),   // 4
            vec![220, 78, 94].into_boxed_slice(),   // 5
            vec![52, 231, 124].into_boxed_slice(),  // 6
            vec![173, 226, 147].into_boxed_slice(), // 7
            vec![6, 193, 187].into_boxed_slice(),   // 8
        ];

        let mut tree = TreeMap::new();
        for (v, k) in keys.into_iter().enumerate() {
            tree.try_insert(k, v).unwrap();
        }

        let mut iter = tree.iter();

        assert_eq!(iter.next(), Some((&[6, 193, 187].into(), &8)));
        assert_eq!(iter.next(), Some((&[30, 159, 204].into(), &1)));
        assert_eq!(iter.next_back(), Some((&[220, 78, 94].into(), &5)));
        assert_eq!(iter.next_back(), Some((&[173, 226, 147].into(), &7)));

        let rest = iter.collect::<Vec<_>>();
        assert_eq!(rest.len(), 5);
        assert_eq!(
            rest,
            vec![
                (&[52, 231, 124].into(), &6),
                (&[58, 7, 66].into(), &3),
                (&[70, 30, 139].into(), &4),
                (&[92, 39, 116].into(), &2),
                (&[114, 159, 30].into(), &0),
            ]
        );
    }

    #[test]
    fn large_fixed_length_key_iterator_front_back() {
        struct TestValues {
            value_stops: u8,
            half_len: usize,
            first_half_last: [u8; 3],
            last_half_last: [u8; 3],
        }

        #[cfg(not(miri))]
        const TEST_PARAMS: TestValues = TestValues {
            value_stops: 5,
            half_len: 108,
            first_half_last: [102, 255, 255],
            last_half_last: [153, 0, 0],
        };
        #[cfg(miri)]
        const TEST_PARAMS: TestValues = TestValues {
            value_stops: 3,
            half_len: 32,
            first_half_last: [85, 255, 255],
            last_half_last: [170, 0, 0],
        };

        let keys = generate_key_fixed_length([TEST_PARAMS.value_stops; 3]);

        let mut tree = TreeMap::new();
        for (v, k) in keys.enumerate() {
            tree.try_insert(k, v).unwrap();
        }

        let mut iter = tree.keys();

        let first_remaining_half = iter.by_ref().take(TEST_PARAMS.half_len).collect::<Vec<_>>();
        let last_remaining_half = iter
            .by_ref()
            .rev()
            .take(TEST_PARAMS.half_len)
            .collect::<Vec<_>>();

        assert!(iter.next().is_none());

        assert_eq!(first_remaining_half.len(), TEST_PARAMS.half_len);
        assert_eq!(last_remaining_half.len(), TEST_PARAMS.half_len);

        assert_eq!(first_remaining_half[0], &[0, 0, 0].into());
        assert_eq!(
            first_remaining_half[first_remaining_half.len() - 1],
            &TEST_PARAMS.first_half_last.into()
        );
        assert_eq!(last_remaining_half[0], &[255, 255, 255].into());
        assert_eq!(
            last_remaining_half[last_remaining_half.len() - 1],
            &TEST_PARAMS.last_half_last.into()
        );
    }
}
