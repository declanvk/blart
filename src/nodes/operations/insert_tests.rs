use std::iter::once;

use super::*;
use crate::NodeType;

#[test]
fn insert_to_small_trees() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let new_leaf = LeafNode::new(Box::new([1, 2, 5, 6]), "1256".to_string());

    let mut tree = first_leaf.to_opaque();
    tree = unsafe { insert(tree, new_leaf).unwrap() };

    assert_eq!(tree.read().node_type, NodeType::Node4);

    let new_root = tree.cast::<InnerNode4<String>>().unwrap();

    {
        let root = new_root.read();

        assert_eq!(root.header.read_prefix(), &[1, 2]);
        assert!(root.lookup_child(5).is_some());
        assert_eq!(root.lookup_child(3), Some(first_leaf.to_opaque()));
        assert_eq!(root.lookup_child(1), None);
    }
    assert_eq!(
        unsafe { search(new_root.to_opaque(), &[1, 2, 5, 6]).unwrap() },
        "1256"
    );
    assert_eq!(
        unsafe { search(new_root.to_opaque(), &[1, 2, 3, 4]).unwrap() },
        "1234"
    );
    assert_eq!(unsafe { search(new_root.to_opaque(), &[1, 2, 5, 7]) }, None);
    assert_eq!(unsafe { search(new_root.to_opaque(), &[1, 2, 3, 5]) }, None);

    unsafe { deallocate_tree(new_root.to_opaque()) };
}

#[test]
fn insert_into_left_skewed_tree_deallocate() {
    #[cfg(not(miri))]
    const KEY_LENGTH_LIMIT: usize = u8::MAX as usize;

    #[cfg(miri)]
    const KEY_LENGTH_LIMIT: usize = 16usize;

    let first_leaf = NodePtr::allocate_node(LeafNode::new(Box::new([0, u8::MAX]), 1));
    let mut current_root = first_leaf.to_opaque();

    for key_size in 2..KEY_LENGTH_LIMIT {
        let key = (0..key_size)
            .chain(once(u8::MAX as usize))
            .map(|byte| (byte % (u8::MAX as usize + 1)) as u8)
            .collect::<Vec<_>>();

        current_root = unsafe {
            insert(
                current_root,
                LeafNode::new(key.into_boxed_slice(), key_size),
            )
            .unwrap()
        };
    }

    for key_size in 1..KEY_LENGTH_LIMIT {
        let key = (0..key_size)
            .chain(once(u8::MAX as usize))
            .map(|byte| (byte % (u8::MAX as usize + 1)) as u8)
            .collect::<Vec<_>>();

        let search_result = unsafe { search(current_root, key.as_ref()) };

        assert_eq!(search_result.copied(), Some(key_size));
    }

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_prefix_key_errors() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let new_leaf = LeafNode::new(Box::new([1, 2]), "12".to_string());
    let tree = first_leaf.to_opaque();
    let result = unsafe { insert(tree, new_leaf) };

    assert_eq!(result, Err(InsertError::PrefixKey(Box::new([1, 2]))));

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_prefix_key_with_existing_prefix_errors() {
    let first_leaf = NodePtr::allocate_node(LeafNode::new(Box::new([1, 2]), "12".to_string()));

    let new_leaf = LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string());
    let tree = first_leaf.to_opaque();
    let result = unsafe { insert(tree, new_leaf) };

    assert_eq!(result, Err(InsertError::PrefixKey(Box::new([1, 2, 3, 4]))));

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_empty_key_errors() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));
    let new_leaf = LeafNode::new(Box::new([]), "1256".to_string());

    let tree = first_leaf.to_opaque();
    let result = unsafe { insert(tree, new_leaf) };

    assert_eq!(result, Err(InsertError::EmptyKey));

    unsafe { deallocate_tree(tree) }
}
