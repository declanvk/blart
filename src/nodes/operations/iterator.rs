use crate::{
    ConcreteNodePtr, InnerNode, InnerNode256Iter, InnerNode48Iter, InnerNodeCompressedIter,
    LeafNode, NodePtr, OpaqueNodePtr,
};
use std::{
    collections::VecDeque,
    iter::{self, FusedIterator},
};

/// An iterator over all the leaves in a tree.
///
/// # Safety
///
/// This iterator maintains pointers to internal nodes from the trie. No
/// mutating operation can occur while this an instance of the iterator is live.
pub enum TreeIterator<K, V> {
    /// An iterator over a tree with only a single entry.
    Singleton(iter::Once<NodePtr<LeafNode<K, V>>>),
    /// An iterator over a tree that has at least one [`InnerNode`].
    InnerNode(InnerNodeTreeIterator<K, V>),
}

impl<K, V> TreeIterator<K, V> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`InnerNodeTreeIterator`].
    pub unsafe fn new(root: OpaqueNodePtr<K, V>) -> Self {
        // SAFETY: Safety requirements for `InnerNodeTreeIterator::new` are the same on
        // the containing function
        unsafe {
            match root.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => {
                    TreeIterator::InnerNode(InnerNodeTreeIterator::new(inner))
                },
                ConcreteNodePtr::Node16(inner) => {
                    TreeIterator::InnerNode(InnerNodeTreeIterator::new(inner))
                },
                ConcreteNodePtr::Node48(inner) => {
                    TreeIterator::InnerNode(InnerNodeTreeIterator::new(inner))
                },
                ConcreteNodePtr::Node256(inner) => {
                    TreeIterator::InnerNode(InnerNodeTreeIterator::new(inner))
                },
                ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                    TreeIterator::Singleton(iter::once(leaf_node_ptr))
                },
            }
        }
    }
}

impl<K, V> Iterator for TreeIterator<K, V> {
    type Item = NodePtr<LeafNode<K, V>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TreeIterator::Singleton(ref mut inner) => inner.next(),
            TreeIterator::InnerNode(ref mut inner) => inner.next(),
        }
    }
}

impl<K, V> DoubleEndedIterator for TreeIterator<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            TreeIterator::Singleton(ref mut inner) => inner.next_back(),
            TreeIterator::InnerNode(ref mut inner) => inner.next_back(),
        }
    }
}

impl<K, V> FusedIterator for TreeIterator<K, V> {}

/// An iterator over all the [`LeafNode`]s in a non-singleton tree.
///
/// Non-singleton here means that the tree has at least one [`InnerNode`].
///
/// # Safety
///
/// This iterator maintains pointers to internal nodes from the trie. No
/// mutating operation can occur while this an instance of the iterator is live.
pub struct InnerNodeTreeIterator<K, V> {
    node_iters: VecDeque<InnerNodeIter<K, V>>,
}

impl<K, V> InnerNodeTreeIterator<K, V> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`InnerNodeTreeIterator`].
    pub unsafe fn new<N>(root: NodePtr<N>) -> Self
    where
        N: InnerNode<Key = K, Value = V>,
    {
        let mut trie_full_iter = InnerNodeTreeIterator {
            node_iters: VecDeque::new(),
        };

        trie_full_iter.update_iters_front(root);

        trie_full_iter
    }

    fn update_iters_front<N>(&mut self, inner: NodePtr<N>)
    where
        N: InnerNode<Key = K, Value = V>,
    {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `InnerNodeTreeIterator` type ensure
        // that no other mutation of the tree happens while the iterator is
        // live.
        self.node_iters
            .push_front(unsafe { inner.as_ref().iter().into() })
    }

    fn update_iters_back<N>(&mut self, inner: NodePtr<N>)
    where
        N: InnerNode<Key = K, Value = V>,
    {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `InnerNodeTreeIterator` type ensure
        // that no other mutation of the tree happens while the iterator is
        // live.
        self.node_iters
            .push_back(unsafe { inner.as_ref().iter().into() })
    }
}

impl<K, V> Iterator for InnerNodeTreeIterator<K, V> {
    type Item = NodePtr<LeafNode<K, V>>;

    fn next(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.front_mut().unwrap().next() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(inner);
                    },
                }
            } else {
                self.node_iters.pop_front();
            }
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for InnerNodeTreeIterator<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.back_mut().unwrap().next_back() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(inner);
                    },
                }
            } else {
                self.node_iters.pop_back();
            }
        }

        None
    }
}

impl<K, V> FusedIterator for InnerNodeTreeIterator<K, V> {}

/// A generic iterator that uses specific iterators for each
/// [`NodeType`][crate::NodeType] (excluding leaves) inside.
pub enum InnerNodeIter<K, V> {
    /// An iterator over the children of an
    /// [`InnerNodeCompressed`][crate::InnerNodeCompressed] node.
    InnerNodeCompressed(InnerNodeCompressedIter<K, V>),
    /// An iterator over the childen of an [`InnerNode48`][crate::InnerNode48]
    /// node.
    InnerNode48(InnerNode48Iter<K, V>),
    /// An iterator over the childen of an [`InnerNode256`][crate::InnerNode256]
    /// node.
    InnerNode256(InnerNode256Iter<K, V>),
}

impl<K, V> Iterator for InnerNodeIter<K, V> {
    type Item = (u8, OpaqueNodePtr<K, V>);

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

impl<K, V> DoubleEndedIterator for InnerNodeIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self {
            InnerNodeIter::InnerNodeCompressed(ref mut inner) => inner.next_back(),
            InnerNodeIter::InnerNode48(ref mut inner) => inner.next_back(),
            InnerNodeIter::InnerNode256(ref mut inner) => inner.next_back(),
        }
    }
}

impl<K, V> FusedIterator for InnerNodeIter<K, V> {}

impl<K, V> From<InnerNodeCompressedIter<K, V>> for InnerNodeIter<K, V> {
    fn from(src: InnerNodeCompressedIter<K, V>) -> Self {
        InnerNodeIter::InnerNodeCompressed(src)
    }
}

impl<K, V> From<InnerNode48Iter<K, V>> for InnerNodeIter<K, V> {
    fn from(src: InnerNode48Iter<K, V>) -> Self {
        InnerNodeIter::InnerNode48(src)
    }
}

impl<K, V> From<InnerNode256Iter<K, V>> for InnerNodeIter<K, V> {
    fn from(src: InnerNode256Iter<K, V>) -> Self {
        InnerNodeIter::InnerNode256(src)
    }
}

#[cfg(test)]
mod tests;
