use crate::raw::{ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

/// Search for the leaf with the minimum key, by lexicographic ordering.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline]
pub unsafe fn minimum_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>> {
    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().min().1 },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return inner_node;
            },
        }
    }
}

/// Search for the leaf with the maximum key, by lexicographic ordering.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
#[inline]
pub unsafe fn maximum_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
) -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>> {
    let mut current_node = root;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node16(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node48(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::Node256(inner_node) => unsafe { inner_node.as_ref().max().1 },
            ConcreteNodePtr::LeafNode(inner_node) => {
                return inner_node;
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alloc::Global,
        raw::{
            deallocate_tree, maximum_unchecked, minimum_unchecked, LeafNode, NodePtr, OpaqueNodePtr,
        },
        tests_common::{generate_key_fixed_length, generate_keys_skewed, insert_unchecked},
    };

    #[test]
    fn leaf_tree_min_max_same() {
        let root: OpaqueNodePtr<Box<[i32; 4]>, String, 16> = NodePtr::allocate_node_ptr(
            LeafNode::with_no_siblings(Box::new([1, 2, 3, 4]), "1234".to_string()),
            &Global,
        )
        .to_opaque();

        let min_leaf = unsafe { minimum_unchecked(root) };
        let max_leaf = unsafe { maximum_unchecked(root) };

        assert_eq!(min_leaf, max_leaf);

        unsafe {
            deallocate_tree(root, &Global);
        }
    }

    #[test]
    fn large_tree_same_length_keys_min_max() {
        #[cfg(not(miri))]
        const VALUE_STOPS: u8 = 5;
        #[cfg(miri)]
        const VALUE_STOPS: u8 = 2;

        let mut keys = generate_key_fixed_length([VALUE_STOPS; 3]);
        let mut root: OpaqueNodePtr<[u8; 3], usize, 16> = NodePtr::allocate_node_ptr(
            LeafNode::with_no_siblings(keys.next().unwrap(), 0),
            &Global,
        )
        .to_opaque();

        for (idx, key) in keys.enumerate() {
            root = unsafe { insert_unchecked(root, key, idx + 1).unwrap().new_root };
        }

        let min_leaf = unsafe { minimum_unchecked(root) };
        let max_leaf = unsafe { maximum_unchecked(root) };

        assert_ne!(min_leaf, max_leaf);
        let min_leaf = min_leaf.read();
        let max_leaf = max_leaf.read();
        assert!(min_leaf.key_ref() < max_leaf.key_ref());
        assert_eq!(min_leaf.key_ref().as_ref(), &[0, 0, 0]);
        if cfg!(miri) {
            assert_eq!(max_leaf.key_ref().as_ref(), &[2, 2, 2]);
        } else {
            assert_eq!(max_leaf.key_ref().as_ref(), &[5, 5, 5]);
        }

        unsafe {
            deallocate_tree(root, &Global);
        }
    }

    #[test]
    fn skewed_tree_min_max() {
        let mut keys = generate_keys_skewed(12);

        let mut root: OpaqueNodePtr<Box<[u8]>, usize, 16> = NodePtr::allocate_node_ptr(
            LeafNode::with_no_siblings(keys.next().unwrap(), 0),
            &Global,
        )
        .to_opaque();

        for (idx, key) in keys.enumerate() {
            root = unsafe { insert_unchecked(root, key, idx + 1).unwrap().new_root };
        }

        let min_leaf = unsafe { minimum_unchecked(root) };
        let max_leaf = unsafe { maximum_unchecked(root) };

        assert_ne!(min_leaf, max_leaf);
        let min_leaf = min_leaf.read();
        let max_leaf = max_leaf.read();
        assert!(min_leaf.key_ref() < max_leaf.key_ref());
        assert_eq!(
            min_leaf.key_ref().as_ref(),
            &[
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MIN,
                u8::MAX
            ]
        );
        assert_eq!(max_leaf.key_ref().as_ref(), &[u8::MAX]);

        unsafe {
            deallocate_tree(root, &Global);
        }
    }
}
