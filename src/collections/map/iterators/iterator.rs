use crate::{AsBytes, ConcreteNodePtr, InnerNode, NodeHeader, NodePtr, OpaqueNodePtr, RawTreeMap};
use std::{collections::VecDeque, iter::FusedIterator};

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s
        pub struct $name<
            'a,
            K: AsBytes,
            V,
            const NUM_PREFIX_BYTES: usize,
            H: NodeHeader<NUM_PREFIX_BYTES>,
        > {
            nodes: VecDeque<OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>>,
            size: usize,
            _tree: $tree,
        }

        impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
            $name<'a, K, V, NUM_PREFIX_BYTES, H>
        {
            /// Create a new iterator that will visit all leaf nodes descended from the
            /// given node.
            pub(crate) fn new(tree: $tree) -> Self {
                Self {
                    nodes: tree.root.into_iter().collect(),
                    size: tree.num_entries,
                    _tree: tree,
                }
            }

            fn push_back_rev_iter<N>(&mut self, inner: NodePtr<NUM_PREFIX_BYTES, N>)
            where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
            {
                unsafe {
                    inner
                        .as_ref()
                        .iter()
                        .rev()
                        .for_each(|(_, n)| self.nodes.push_back(n))
                };
            }

            fn push_front<N>(&mut self, inner: NodePtr<NUM_PREFIX_BYTES, N>)
            where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
            {
                unsafe {
                    inner
                        .as_ref()
                        .iter()
                        .for_each(|(_, n)| self.nodes.push_front(n))
                };
            }
        }

        impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
            Iterator for $name<'a, K, V, NUM_PREFIX_BYTES, H>
        {
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

        impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
            DoubleEndedIterator for $name<'a, K, V, NUM_PREFIX_BYTES, H>
        {
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

        impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
            FusedIterator for $name<'a, K, V, NUM_PREFIX_BYTES, H>
        {
        }

        impl<'a, K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
            ExactSizeIterator for $name<'a, K, V, NUM_PREFIX_BYTES, H>
        {
            fn len(&self) -> usize {
                self.size
            }
        }
    };
}

gen_iter!(
    TreeIterator,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a V),
    as_key_value_ref
);
gen_iter!(
    TreeIteratorMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);
gen_iter!(
    Keys,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a K,
    as_key_ref
);
gen_iter!(
    Values,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a V,
    as_value_ref
);
gen_iter!(
    ValuesMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a mut V,
    as_value_mut
);
