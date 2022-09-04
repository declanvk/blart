use crate::{ConcreteNodePtr, InnerNode, InnerNodeIter, LeafNode, NodePtr, OpaqueNodePtr};
use std::{collections::VecDeque, iter};

/// An iterator over all the entries in a tree.
///
/// # Safety
///
/// This iterator maintains pointers to internal nodes from the trie. No
/// mutating operation can occur while this an instance of the iterator is live.
pub struct TrieRangeFullIter<V> {
    node_iters: VecDeque<InnerNodeIter<V>>,
}

impl<V> TrieRangeFullIter<V> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    ///
    /// # Safety
    ///
    /// See safety requirements on type [`TrieRangeFullIter`].
    pub unsafe fn new(root: OpaqueNodePtr<V>) -> Result<Self, iter::Once<(*const [u8], *const V)>> {
        let mut trie_full_iter = TrieRangeFullIter {
            node_iters: VecDeque::new(),
        };

        match root.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node16(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node48(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::Node256(inner) => {
                trie_full_iter.update_iters_front(inner);
            },
            ConcreteNodePtr::LeafNode(inner) => {
                return Err(iter::once(Self::leaf_to_item(inner)));
            },
        }

        Ok(trie_full_iter)
    }

    fn update_iters_front<N: InnerNode<Value = V>>(&mut self, inner: NodePtr<N>) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the tree happens while the iterator is live.
        self.node_iters
            .push_front(unsafe { inner.as_ref().iter().into() })
    }

    fn update_iters_back<N: InnerNode<Value = V>>(&mut self, inner: NodePtr<N>) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function, during which it is turned into an owned iterator which uses
        // pointers. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the tree happens while the iterator is live.
        self.node_iters
            .push_back(unsafe { inner.as_ref().iter().into() })
    }

    fn leaf_to_item(node: NodePtr<LeafNode<V>>) -> (*const [u8], *const V) {
        // SAFETY: The lifetime of the returned reference is restricted to this
        // function. The safety requirements on the `TrieRangeFullIter` type ensure that
        // no other mutation of the pointers returned from this function happens while
        let leaf = unsafe { node.as_ref() };

        (leaf.key.as_ref() as *const _, (&leaf.value) as *const _)
    }
}

impl<V> Iterator for TrieRangeFullIter<V> {
    type Item = (*const [u8], *const V);

    fn next(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.front_mut().unwrap().next() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_front(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(Self::leaf_to_item(inner));
                    },
                }
            } else {
                self.node_iters.pop_front();
            }
        }

        None
    }
}

impl<V> DoubleEndedIterator for TrieRangeFullIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while !self.node_iters.is_empty() {
            if let Some((_, child)) = self.node_iters.back_mut().unwrap().next_back() {
                match child.to_node_ptr() {
                    ConcreteNodePtr::Node4(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node16(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node48(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::Node256(inner) => self.update_iters_back(inner),
                    ConcreteNodePtr::LeafNode(inner) => {
                        return Some(Self::leaf_to_item(inner));
                    },
                }
            } else {
                self.node_iters.pop_back();
            }
        }

        None
    }
}

#[cfg(test)]
mod tests;
