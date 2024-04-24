use crate::{
    AsBytes, ConcreteNodePtr, InnerNode, InnerNode256, InnerNode48, InnerNodeCompressedIter,
    LeafNode, NodePtr, OpaqueNodePtr, TreeMap,
};
use std::{
    collections::VecDeque,
    iter::{self, FusedIterator},
    marker::PhantomData,
};

/// An iterator over all the [`LeafNode`]s in a non-singleton tree.
///
/// Non-singleton here means that the tree has at least one [`InnerNode`].
///
/// # Safety
///
/// This iterator maintains pointers to internal nodes from the trie. No
/// mutating operation can occur while this an instance of the iterator is live.
pub struct TreeIterator1<'a, K: AsBytes, V> {
    nodes: VecDeque<OpaqueNodePtr<K, V>>,
    _marker: PhantomData<&'a TreeMap<K, V>>,
}

impl<'a, K: AsBytes, V> TreeIterator1<'a, K, V> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`InnerNodeTreeIterator`].
    pub unsafe fn new(root: OpaqueNodePtr<K, V>) -> Self {
        Self {
            nodes: VecDeque::from([root]),
            _marker: PhantomData,
        }
    }

    fn push_back_rev_iter<N>(&mut self, inner: NodePtr<N>)
    where
        N: InnerNode<Key = K, Value = V> + 'a,
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
        N: InnerNode<Key = K, Value = V> + 'a,
    {
        unsafe {
            inner
                .as_ref()
                .iter()
                .for_each(|(_, n)| self.nodes.push_front(n))
        };
    }
}

impl<'a, K: AsBytes, V> Iterator for TreeIterator1<'a, K, V> {
    type Item = NodePtr<LeafNode<K, V>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.nodes.pop_back() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node16(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node48(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node256(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::LeafNode(inner) => return Some(inner),
            }
        }

        None
    }
}

impl<'a, K: AsBytes, V> DoubleEndedIterator for TreeIterator1<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.nodes.pop_front() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => self.push_front(inner),
                ConcreteNodePtr::Node16(inner) => self.push_front(inner),
                ConcreteNodePtr::Node48(inner) => self.push_front(inner),
                ConcreteNodePtr::Node256(inner) => self.push_front(inner),
                ConcreteNodePtr::LeafNode(inner) => return Some(inner),
            }
        }

        None
    }
}

impl<'a, K: AsBytes, V> FusedIterator for TreeIterator1<'a, K, V> {}

// #[cfg(test)]
// mod tests;
