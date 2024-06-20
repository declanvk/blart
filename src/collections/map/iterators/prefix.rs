use crate::{AsBytes, ConcreteNodePtr, InnerNode, NodeHeader, NodePtr, OpaqueNodePtr, RawTreeMap};
use std::{collections::VecDeque, iter::FusedIterator};

macro_rules! gen_add_childs {
    ($name:ident, $f1:ident, $f2:ident) => {
        fn $name<N>(&mut self, inner: NodePtr<NUM_PREFIX_BYTES, N>, current_depth: usize)
        where
            N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
        {
            let inner = unsafe { inner.as_ref() };
            // Given that the invariant of the algorithm is that
            // all nodes prior to the current one make part of
            // the prefix (i.e we are always in the correct path)
            //
            // With that is safe to assume that if the number of
            // bytes used is >= to the prefix len this means that
            // the current node and all of it's children are part
            // of this prefix search
            if current_depth >= self.prefix.len() {
                let prefix_len = inner.header().prefix_len();
                self.$f1(inner, current_depth + prefix_len + 1);
                return;
            }

            // Read the prefix of the current node
            let (prefix, _) = inner.read_full_prefix(current_depth);
            // If the searched prefix is not a prefix of the current node
            // prefix we prune this node and it's children
            //
            // This slice operation is safe since we just checked if the
            // current depth >= prefix len
            let Some(matched_bytes) = Self::is_prefix_of(prefix, &self.prefix[current_depth..])
            else {
                return;
            };

            // In case the searched prefix is a prefix, if the
            // number of matched bytes + depth >= searched prefix
            // len we know that this node and all of it's children
            // are part of this prefix search
            let new_depth = current_depth + matched_bytes;
            if new_depth >= self.prefix.len() {
                self.$f1(inner, new_depth + 1);
                return;
            }

            // If there is some remaning bytes we need to consider
            // the node key that matches the first character of
            // the searched prefix, so we find a children with this
            // key and only consider this one
            //
            // This slice operation is safe sice we just checked if
            // new depth >= searched prefix len, and this also
            // ensures that we have at least one byte in the slice
            let key = *self.prefix[new_depth..].first().unwrap();
            if let Some((_, n)) = inner.iter().find(|(k, _)| *k == key) {
                self.nodes.$f2((n, new_depth + 1));
            }
        }
    };
}

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s with a specific prefix
        pub struct $name<
            'a,
            'b,
            K: AsBytes,
            V,
            const NUM_PREFIX_BYTES: usize,
            H: NodeHeader<NUM_PREFIX_BYTES>,
        > {
            nodes: VecDeque<(OpaqueNodePtr<K, V, NUM_PREFIX_BYTES, H>, usize)>,
            size: usize,
            _tree: $tree,
            prefix: &'b [u8],
        }

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
            gen_add_childs!(add_childs, push_back_rev_iter, push_back);

            gen_add_childs!(add_childs_rev, push_front, push_front);

            /// Create a new iterator that will visit all leaf nodes descended from the
            /// given node.
            pub(crate) fn new(tree: $tree, prefix: &'b [u8]) -> Self {
                Self {
                    nodes: tree.root.into_iter().map(|r| (r, 0)).collect(),
                    size: tree.num_entries,
                    prefix,
                    _tree: tree,
                }
            }

            fn push_back_rev_iter<N>(&mut self, inner: &N, depth: usize)
            where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
            {
                inner
                    .iter()
                    .rev()
                    .for_each(|(_, n)| self.nodes.push_back((n, depth)))
            }

            fn push_front<N>(&mut self, inner: &N, depth: usize)
            where
                N: InnerNode<NUM_PREFIX_BYTES, Key = K, Value = V, Header = H>,
            {
                inner
                    .iter()
                    .for_each(|(_, n)| self.nodes.push_front((n, depth)))
            }

            fn is_prefix_of(a: &[u8], b: &[u8]) -> Option<usize> {
                let min = a.len().min(b.len());
                let matched_bytes = a.iter().zip(b).take_while(|(a, b)| **a == **b).count();

                (min == matched_bytes).then_some(matched_bytes)
            }
        }

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > Iterator for $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
            type Item = $ret;

            fn next(&mut self) -> Option<Self::Item> {
                while let Some((node, current_depth)) = self.nodes.pop_back() {
                    match node.to_node_ptr() {
                        ConcreteNodePtr::Node4(inner) => self.add_childs(inner, current_depth),
                        ConcreteNodePtr::Node16(inner) => self.add_childs(inner, current_depth),
                        ConcreteNodePtr::Node48(inner) => self.add_childs(inner, current_depth),
                        ConcreteNodePtr::Node256(inner) => self.add_childs(inner, current_depth),
                        ConcreteNodePtr::LeafNode(inner) => {
                            if let Some(_) = Self::is_prefix_of(
                                unsafe { inner.as_key_ref().as_bytes() },
                                &self.prefix,
                            ) {
                                self.size -= 1;
                                return unsafe { Some(inner.$op()) };
                            }
                        },
                    }
                }

                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Some(self.size))
            }

            fn last(mut self) -> Option<Self::Item>
            where
                Self: Sized,
            {
                self.next_back()
            }
        }

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > DoubleEndedIterator for $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                while let Some((node, current_depth)) = self.nodes.pop_front() {
                    match node.to_node_ptr() {
                        ConcreteNodePtr::Node4(inner) => self.add_childs_rev(inner, current_depth),
                        ConcreteNodePtr::Node16(inner) => self.add_childs_rev(inner, current_depth),
                        ConcreteNodePtr::Node48(inner) => self.add_childs_rev(inner, current_depth),
                        ConcreteNodePtr::Node256(inner) => {
                            self.add_childs_rev(inner, current_depth)
                        },
                        ConcreteNodePtr::LeafNode(inner) => {
                            self.size -= 1;
                            return unsafe { Some(inner.$op()) };
                        },
                    }
                }

                None
            }
        }

        impl<
                'a,
                'b,
                K: AsBytes,
                V,
                const NUM_PREFIX_BYTES: usize,
                H: NodeHeader<NUM_PREFIX_BYTES>,
            > FusedIterator for $name<'a, 'b, K, V, NUM_PREFIX_BYTES, H>
        {
        }
    };
}

gen_iter!(
    Prefix,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a V),
    as_key_value_ref
);
gen_iter!(
    PrefixMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);
gen_iter!(
    PrefixKeys,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a K,
    as_key_ref
);
gen_iter!(
    PrefixValues,
    &'a RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a V,
    as_value_ref
);
gen_iter!(
    PrefixValuesMut,
    &'a mut RawTreeMap<K, V, NUM_PREFIX_BYTES, H>,
    &'a mut V,
    as_value_mut
);
