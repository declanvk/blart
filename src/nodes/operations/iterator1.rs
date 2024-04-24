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
pub struct TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
{
    nodes: VecDeque<OpaqueNodePtr<K, V>>,
    size: usize,
    f: F,
    _marker: PhantomData<&'a TreeMap<K, V>>,
}

impl<'a, K, V, F, R> TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
{
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`InnerNodeTreeIterator`].
    pub unsafe fn new(tree: &TreeMap<K, V>, f: F) -> Self {
        Self {
            nodes: tree.root.into_iter().collect(),
            size: tree.num_entries,
            f,
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

impl<'a, K, V, F, R> Iterator for TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
{
    type Item = R;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.nodes.pop_back() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node16(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node48(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node256(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::LeafNode(inner) => {
                    self.size -= 1;
                    return Some((self.f)(inner));
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

impl<'a, K, V, F, R> DoubleEndedIterator for TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
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
                    return Some((self.f)(inner));
                },
            }
        }

        None
    }
}

impl<'a, K: AsBytes, V, F, R> FusedIterator for TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
{
}

impl<'a, K: AsBytes, V, F, R> ExactSizeIterator for TreeIterator1<'a, K, V, F, R>
where
    K: AsBytes,
    F: Fn(NodePtr<LeafNode<K, V>>) -> R,
{
    fn len(&self) -> usize {
        self.size
    }
}

// #[cfg(test)]
// mod tests;
