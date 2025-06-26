use crate::{
    alloc::Allocator,
    collections::map::TreeMap,
    raw::{
        ConcreteNodePtr, DeletePoint, DeleteResult, InnerNode, LeafNode, NodePtr, OpaqueNodePtr,
        ParentNodeChange,
    },
};
use std::{fmt, iter::FusedIterator};

type Node<K, V, const PREFIX_LEN: usize> = (Option<u8>, OpaqueNodePtr<K, V, PREFIX_LEN>);

enum DfsFrame<K, V, const PREFIX_LEN: usize> {
    Node(Node<K, V, PREFIX_LEN>),
    PopAncestor,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for DfsFrame<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Node(arg0) => f.debug_tuple("Node").field(arg0).finish(),
            Self::PopAncestor => write!(f, "PopAncestor"),
        }
    }
}

struct ExtractIfState<K, V, const PREFIX_LEN: usize> {
    /// This stack tracks ancestry of the `current_leaf` all the way to the root
    /// node.
    ancestors: Vec<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    /// This stack tracks the "parent key byte" to the root node.
    ///
    /// The length of this stack will always be one less than the length of
    /// `nodes`, since the root node has no "parent key byte".
    key_bytes: Vec<u8>,
    /// This stack tracks the DFS exploration actions, including when ancestors
    /// should be popped.
    dfs_stack: Vec<DfsFrame<K, V, PREFIX_LEN>>,
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for ExtractIfState<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExtractIfState")
            .field("ancestors", &self.ancestors)
            .field("key_bytes", &self.key_bytes)
            .field("dfs_stack", &self.dfs_stack)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> ExtractIfState<K, V, PREFIX_LEN> {
    fn new(root: Option<OpaqueNodePtr<K, V, PREFIX_LEN>>) -> Self {
        let mut dfs_stack = vec![];
        if let Some(root) = root {
            dfs_stack.push(DfsFrame::Node((None, root)))
        }
        Self {
            ancestors: vec![],
            key_bytes: vec![],
            dfs_stack,
        }
    }

    fn pop(&mut self) -> Option<Node<K, V, PREFIX_LEN>> {
        loop {
            match self.dfs_stack.pop()? {
                DfsFrame::Node(node) => {
                    return Some(node);
                },
                DfsFrame::PopAncestor => self.pop_ancestor(),
            }
        }
    }

    fn pop_ancestor(&mut self) {
        let _ = self
            .ancestors
            .pop()
            .expect("there should not be a mismatched number of ancestors and pop frames");
        let _ = self.key_bytes.pop();
    }

    /// This function corresponds to the
    /// [`DeletePoint::grandparent_ptr_and_parent_key_byte`] field and will
    /// return a value that is correct for that field.
    fn grandparent_ptr_and_parent_key_byte(&self) -> Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)> {
        let [.., grandparent, _] = self.ancestors.as_slice() else {
            return None;
        };

        let [.., parent_key_byte] = self.key_bytes.as_slice() else {
            return None;
        };

        Some((*grandparent, *parent_key_byte))
    }

    /// This function corresponds to the
    /// [`DeletePoint::parent_ptr_and_child_key_byte`] field and will
    /// return a value that is correct for that field.
    fn parent_ptr_and_child_key_byte(
        &self,
        child_key_byte: Option<u8>,
    ) -> Option<(OpaqueNodePtr<K, V, PREFIX_LEN>, u8)> {
        let [.., parent] = self.ancestors.as_slice() else {
            return None;
        };

        let child_key_byte =
            child_key_byte.expect("child key byte should be present if there is a parent node");

        Some((*parent, child_key_byte))
    }

    /// This function will update any pointers in the ancestor path that are now
    /// outdated because of the delete (parent pointers).
    ///
    /// If it returns `true`, then the parent node was compressed out of the
    /// tree and the DFS stack needs to be updated.
    fn fixup_after_delete(&mut self, delete_result: &DeleteResult<K, V, PREFIX_LEN>) {
        let removed_ancestor = match delete_result.parent_node_change {
            Some(ParentNodeChange::NoChange) => {
                // No change in the parent node means that the DFS doesn't need to be fixed
                false
            },
            Some(ParentNodeChange::Shrunk { new_parent_node }) => {
                // Shrunk parent node means that we can just in-place swap it out, without
                // changing the length of the ancestor path

                let parent = self
                    .ancestors
                    .last_mut()
                    .expect("there should be a parent if it was shrunk");
                *parent = new_parent_node;

                // DFS doesn't need any fixup if the number of ancestors remains the same
                false
            },
            Some(ParentNodeChange::SingletonCompressed { child_node_ptr }) => {
                // If we compressed an inner node, that means that there was a single remaining
                // child in the old parent node that was pulled up to be a child of the
                // grandparent node OR the single remaining node was pulled up to be the new
                // root.
                //
                // We need to fixup that node's entry in the DFS stack so that
                // its associated key byte is now the old parent's key byte so that we don't
                // accidentally delete the wrong node later on.
                if let Some((_, parent_key_byte)) = self.grandparent_ptr_and_parent_key_byte() {
                    let child_ptr_frame = self
                        .dfs_stack
                        .iter_mut()
                        .filter_map(|frame| match frame {
                            DfsFrame::Node(node) => Some(node),
                            DfsFrame::PopAncestor => None,
                        })
                        .rfind(|(_, node)| *node == child_node_ptr)
                        // The child node should be present because it was a sibling of a node that
                        // was deleted, and all siblings are pushed onto the
                        // DFS stack at the same time
                        .expect("new child node ptr should be present in the DFS stack");
                    child_ptr_frame.0 = Some(parent_key_byte);
                }

                debug_assert!(
                    !self.ancestors.is_empty(),
                    "there should be a parent node on the stack before removal"
                );
                self.pop_ancestor();

                // Since we're removing a key byte and parent node, we should fixup the DFS
                // stack as well and remove the most recently occuring `PopAncestor` frame.
                true
            },
            None => {
                // `None` indicates that the previous root node was deleted and the tree is now
                // empty
                self.key_bytes.clear();
                let had_parent_nodes = !self.ancestors.is_empty();
                self.ancestors.clear();
                had_parent_nodes
            },
        };

        if removed_ancestor {
            // Need to remove the top-most `PopAncestor` frame so that the number of
            // ancestors and the number of ancestor frames don't go out of sync
            let (top_pop_idx, _) = self
                .dfs_stack
                .iter()
                .enumerate()
                .rfind(|(_, f)| matches!(f, DfsFrame::PopAncestor))
                .expect("there should be a `PopAncestor` frame in the stack");

            let _ = self.dfs_stack.remove(top_pop_idx);
        }
    }

    /// Add a new ancestor to the path and their children to the DFS stack.
    ///
    /// If the new ancestor is the tree root, the `key_byte` argument should
    /// be `None`. Otherwise, it must be `Some(_)`.
    ///
    /// # Safety
    ///
    /// The inner node must not be concurrently mutated and there must not be an
    /// existing mutable reference to the inner node.
    unsafe fn extend_back<N>(&mut self, inner_ptr: NodePtr<PREFIX_LEN, N>, key_byte: Option<u8>)
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        // !self.key_bytes.is_empty() -> key_byte.is_some()
        // key_byte.is_none() -> self.key_bytes.is_empty()
        // A -> B === !A || B
        debug_assert!(self.key_bytes.is_empty() || key_byte.is_some());

        // SAFETY: Covered by function caller requirements. Additionally, the created
        // reference is bounded to this function call.
        let inner = unsafe { inner_ptr.as_ref() };

        self.dfs_stack.push(DfsFrame::PopAncestor);
        // Extend reversed so that the first child is on top of the DFS stack
        self.dfs_stack.extend(
            inner
                .iter()
                .rev()
                .map(|(key_byte, node)| DfsFrame::Node((Some(key_byte), node))),
        );

        self.ancestors.push(inner_ptr.to_opaque());
        if let Some(key_byte) = key_byte {
            self.key_bytes.push(key_byte);
        }
    }
}

/// An iterator which uses a closure to determine if an element should be
/// removed.
///
/// This struct is created by the [`extract_if`][TreeMap::extract_if] method
/// on [`TreeMap`]. See its documentation for more.
#[derive(Debug)]
pub struct ExtractIf<'a, K, V, F, const PREFIX_LEN: usize, A: Allocator> {
    map: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    pred: F,
    // The stack tracks the current ancestor chain
    state: ExtractIfState<K, V, PREFIX_LEN>,
    size: usize,
    // This field tracks the next leaf to be returned by the iterator.
    //
    // If `None`, then the iterator is exhausted.
    current_leaf: Option<(Option<u8>, NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>)>,
}

impl<'a, K, V, F, const PREFIX_LEN: usize, A> ExtractIf<'a, K, V, F, PREFIX_LEN, A>
where
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    pub(crate) fn new(map: &'a mut TreeMap<K, V, PREFIX_LEN, A>, pred: F) -> Self {
        let size = map.len();
        let state = ExtractIfState::new(map.state.as_ref().map(|s| s.root));

        let mut iter = Self {
            map,
            pred,
            state,
            current_leaf: None,
            size,
        };

        iter.current_leaf = iter.find_next_leaf();

        iter
    }

    #[inline]
    fn extend_back(
        &mut self,
        inner_node: NodePtr<PREFIX_LEN, impl InnerNode<PREFIX_LEN, Key = K, Value = V>>,
        key_byte: Option<u8>,
    ) {
        // SAFETY: We have a mutable reference to the overall tree, so there should be
        // no concurrent modification or any other existing mutable references to the
        // inner node.
        unsafe { self.state.extend_back(inner_node, key_byte) };
    }

    fn find_next_leaf(
        &mut self,
    ) -> Option<(Option<u8>, NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>)> {
        while let Some((key_byte, node)) = self.state.pop() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner_node) => self.extend_back(inner_node, key_byte),
                ConcreteNodePtr::Node16(inner_node) => self.extend_back(inner_node, key_byte),
                ConcreteNodePtr::Node48(inner_node) => self.extend_back(inner_node, key_byte),
                ConcreteNodePtr::Node256(inner_node) => self.extend_back(inner_node, key_byte),
                ConcreteNodePtr::LeafNode(leaf_node) => {
                    return Some((key_byte, leaf_node));
                },
            }
        }

        None
    }
}

impl<'a, K, V, F, const PREFIX_LEN: usize, A> Iterator for ExtractIf<'a, K, V, F, PREFIX_LEN, A>
where
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key_byte, leaf_node_ptr)) = self.current_leaf.take() {
            self.size -= 1;

            let should_remove = {
                // SAFETY: The leaf node lifetime is scoped to this block and we don't have any
                // other reference to this leaf. Also, we hold a mutable reference to the
                // overall tree, so no concurrent modification or access to the tree is
                // possible.
                let leaf_node = unsafe { leaf_node_ptr.as_mut() };
                let (k, v) = leaf_node.entry_mut();
                (self.pred)(k, v)
            };

            if !should_remove {
                self.current_leaf = self.find_next_leaf();
                continue;
            }

            let grandparent_ptr_and_parent_key_byte =
                self.state.grandparent_ptr_and_parent_key_byte();
            let parent_ptr_and_child_key_byte = self.state.parent_ptr_and_child_key_byte(key_byte);

            let delete_point = DeletePoint {
                grandparent_ptr_and_parent_key_byte,
                parent_ptr_and_child_key_byte,
                leaf_node_ptr,
            };

            // The danger of this method is that during application, the parent node may be
            // deallocated and reallocated at a different size. We need to make sure to
            // fixup the ancestor chain entry and cleanup the DFS stack.
            //
            // SAFETY: The `ExtractIfState` contains a bunch of pointers into the tree, some
            // of which are going to be invalidated by the delete. The `fixup_after_delete`
            // method should fix all the invalidated pointers.
            let delete_result = unsafe { self.map.apply_delete_point(delete_point) };

            self.state.fixup_after_delete(&delete_result);

            self.current_leaf = self.find_next_leaf();

            return Some(delete_result.deleted_leaf.into_entry());
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

impl<K, V, F, const PREFIX_LEN: usize, A> FusedIterator for ExtractIf<'_, K, V, F, PREFIX_LEN, A>
where
    F: FnMut(&K, &mut V) -> bool,
    A: Allocator,
{
}

// TODO: Make it DoubleEndedIterator using VecDeque

#[cfg(test)]
mod tests {
    use crate::{
        tests_common::{generate_key_fixed_length, swap},
        TreeMap,
    };

    #[test]
    fn extract_if_simple() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(|_k, v| *v % 2 == 0).collect();

        assert_eq!(drained.len(), 5);
        assert_eq!(map.len(), 5);
        assert_eq!(drained, vec![(0, 0), (2, 2), (4, 4), (6, 6), (8, 8)]);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(1, 1), (3, 3), (5, 5), (7, 7), (9, 9)]
        );
    }

    #[test]
    fn extract_if_all() {
        let first_width = if cfg!(miri) { 15 } else { u8::MAX };
        let mut map: TreeMap<_, usize> = generate_key_fixed_length([first_width, 1])
            .enumerate()
            .map(swap)
            .collect();

        let drained: Vec<_> = map.extract_if(|_, _| true).collect();
        let expected_len = if cfg!(miri) { 32 } else { 512 };
        assert_eq!(drained.len(), expected_len);
        assert!(map.is_empty());
    }

    #[test]
    fn extract_if_none() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map.extract_if(|_, _| false).collect();

        assert!(drained.is_empty());
        assert_eq!(map.len(), 10);
    }

    #[test]
    fn extract_if_mutate() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let drained: Vec<_> = map
            .extract_if(|_k, v| {
                if *v % 2 == 0 {
                    true
                } else {
                    *v *= 2;
                    false
                }
            })
            .collect();

        assert_eq!(drained.len(), 5);
        assert_eq!(map.len(), 5);
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            vec![(1, 2), (3, 6), (5, 10), (7, 14), (9, 18)]
        );
    }

    #[test]
    fn extract_if_size_hint_none_removed() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let initial_len = map.len();
        let mut iter = map.extract_if(|_k, _v| false); // Predicate removes none

        assert_eq!(iter.size_hint(), (0, Some(10)));
        // A single iterator step will empty it, since it doesn't remove any elements
        assert!(iter.next().is_none());
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(map.len(), initial_len);
    }

    #[test]
    fn extract_if_size_hint_mixed_removed() {
        let mut map: TreeMap<i32, i32> = (0..10).map(|i| (i, i)).collect();
        let initial_len = map.len();
        let mut iter = map.extract_if(|k, _v| k % 2 == 0); // Predicate removes evens
        let mut processed_count = 1;

        for _ in 0..(initial_len / 2) {
            assert!(iter.next().is_some());
            assert_eq!(iter.size_hint(), (0, Some(initial_len - processed_count)));
            processed_count += 2;
        }
        // This behavior seemed a bit odd to me at first, since I would expect that
        // `Some(1)` means that there is one more element in the iterator. But it
        // actually indicates that there is **at most** one more element in the
        // iterator. And in this case it turns out there are no more elements in the
        // iterator.
        assert_eq!(iter.size_hint(), (0, Some(1)));
        assert!(iter.next().is_none()); // clear out last odd value
        assert_eq!(iter.size_hint(), (0, Some(0)));

        // After the iterator is dropped, we can check the final map length
        let expected_remaining = initial_len - (initial_len / 2); // 10 - 5 = 5
        assert_eq!(map.len(), expected_remaining);
    }
}
