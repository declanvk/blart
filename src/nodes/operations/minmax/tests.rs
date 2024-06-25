use crate::{
    deallocate_tree, maximum_unchecked, minimum_unchecked,
    tests_common::{generate_key_fixed_length, generate_keys_skewed, insert_unchecked},
    LeafNode, NodePtr, OpaqueNodePtr,
};

#[test]
fn leaf_tree_min_max_same() {
    let root: OpaqueNodePtr<Box<[i32; 4]>, String, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()))
            .to_opaque();

    let min_leaf = unsafe { minimum_unchecked(root) };
    let max_leaf = unsafe { maximum_unchecked(root) };

    assert_eq!(min_leaf, max_leaf);

    unsafe { deallocate_tree(root) }
}

#[test]
fn large_tree_same_length_keys_min_max() {
    #[cfg(not(miri))]
    const VALUE_STOPS: u8 = 5;
    #[cfg(miri)]
    const VALUE_STOPS: u8 = 2;

    let mut keys = generate_key_fixed_length([VALUE_STOPS; 3]);
    let mut root: OpaqueNodePtr<Box<[u8]>, usize, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        root = unsafe { insert_unchecked(root, key, idx + 1).unwrap().new_root };
    }

    let min_leaf = unsafe { minimum_unchecked(root) };
    let max_leaf = unsafe { maximum_unchecked(root) };

    assert_ne!(min_leaf, max_leaf);
    let min_leaf = min_leaf.read();
    let max_leaf = max_leaf.read();
    assert!(min_leaf.key_ref() < max_leaf.key_ref());
    assert_eq!(min_leaf.key_ref().as_ref(), &[u8::MIN, u8::MIN, u8::MIN]);
    assert_eq!(max_leaf.key_ref().as_ref(), &[u8::MAX, u8::MAX, u8::MAX]);

    unsafe { deallocate_tree(root) }
}

#[test]
fn skewed_tree_min_max() {
    let mut keys = generate_keys_skewed(12);

    let mut root: OpaqueNodePtr<Box<[u8]>, usize, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

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

    unsafe { deallocate_tree(root) }
}
