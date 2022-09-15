use crate::{
    deallocate_tree, insert_unchecked, search_unchecked, tests_common::generate_keys_skewed,
    InnerNode, InnerNode4, InsertPrefixError, LeafNode, NodePtr, NodeType,
};

#[test]
fn insert_to_small_trees() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let mut tree = first_leaf.to_opaque();
    tree = unsafe { insert_unchecked(tree, Box::new([1, 2, 5, 6]), "1256".to_string()).unwrap() };

    assert_eq!(tree.node_type(), NodeType::Node4);

    let new_root = tree.cast::<InnerNode4<String>>().unwrap();

    {
        let root = new_root.read();

        assert_eq!(root.header.read_prefix(), &[1, 2]);
        assert!(root.lookup_child(5).is_some());
        assert_eq!(root.lookup_child(3), Some(first_leaf.to_opaque()));
        assert_eq!(root.lookup_child(1), None);
    }
    assert_eq!(
        unsafe {
            &search_unchecked(new_root.to_opaque(), &[1, 2, 5, 6])
                .unwrap()
                .read()
                .value
        },
        "1256"
    );
    assert_eq!(
        unsafe {
            &search_unchecked(new_root.to_opaque(), &[1, 2, 3, 4])
                .unwrap()
                .read()
                .value
        },
        "1234"
    );
    assert!(unsafe { search_unchecked(new_root.to_opaque(), &[1, 2, 5, 7]).is_none() });
    assert!(unsafe { search_unchecked(new_root.to_opaque(), &[1, 2, 3, 5]).is_none() });

    unsafe { deallocate_tree(new_root.to_opaque()) };
}

#[test]
fn insert_into_left_skewed_tree_deallocate() {
    #[cfg(not(miri))]
    const KEY_LENGTH_LIMIT: usize = u8::MAX as usize;

    #[cfg(miri)]
    const KEY_LENGTH_LIMIT: usize = 16usize;

    let mut keys = generate_keys_skewed(KEY_LENGTH_LIMIT);
    let mut current_root =
        NodePtr::allocate_node(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        current_root = unsafe { insert_unchecked(current_root, key, idx + 1).unwrap() };
    }

    for (value, key) in generate_keys_skewed(KEY_LENGTH_LIMIT).enumerate() {
        let search_result = unsafe { search_unchecked(current_root, key.as_ref()) };

        assert_eq!(search_result.unwrap().read().value, value);
    }

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_prefix_key_errors() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let tree = first_leaf.to_opaque();
    let result = unsafe { insert_unchecked(tree, Box::new([1, 2]), "12".to_string()) };

    assert_eq!(result, Err(InsertPrefixError(Box::new([1, 2]))));

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_prefix_key_with_existing_prefix_errors() {
    let first_leaf = NodePtr::allocate_node(LeafNode::new(Box::new([1, 2]), "12".to_string()));

    let tree = first_leaf.to_opaque();
    let result = unsafe { insert_unchecked(tree, Box::new([1, 2, 3, 4]), "1234".to_string()) };

    assert_eq!(result, Err(InsertPrefixError(Box::new([1, 2, 3, 4]))));

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_key_with_long_prefix_then_split() {
    let first_leaf = NodePtr::allocate_node(LeafNode::new(
        Box::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 255]),
        0,
    ));

    let mut tree = first_leaf.to_opaque();
    tree =
        unsafe { insert_unchecked(tree, Box::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 255]), 1).unwrap() };

    tree = unsafe { insert_unchecked(tree, Box::new([1, 1, 255]), 2).unwrap() };

    assert_eq!(
        unsafe {
            search_unchecked(tree, &[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 255])
                .unwrap()
                .read()
                .value
        },
        0
    );
    assert_eq!(
        unsafe {
            search_unchecked(tree, &[1, 1, 1, 1, 1, 1, 1, 1, 1, 255])
                .unwrap()
                .read()
                .value
        },
        1
    );
    assert_eq!(
        unsafe { search_unchecked(tree, &[1, 1, 255]).unwrap().read().value },
        2
    );

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_split_prefix_at_implicit_byte() {
    const KEYS: [[u8; 12]; 3] = [
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 51],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0],
    ];

    let mut keys = KEYS.iter().map(|k| Box::<[u8]>::from(&k[..]));

    let mut current_root =
        NodePtr::allocate_node(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        current_root = unsafe { insert_unchecked(current_root, key, idx + 1).unwrap() };
    }

    for (value, key) in KEYS.iter().map(|k| &k[..]).enumerate() {
        let search_result = unsafe { search_unchecked(current_root, key.as_ref()) };

        assert_eq!(search_result.unwrap().read().value, value);
    }

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_fails_new_key_prefix_of_existing_entry() {
    let mut current_root =
        NodePtr::allocate_node(LeafNode::new(Box::<[u8]>::from(&[1, 2, 3, 4][..]), 0)).to_opaque();
    current_root = unsafe {
        insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..]), 1).unwrap()
    };

    let insert_result =
        unsafe { insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8][..]), 2) };

    let insert_err =
        insert_result.expect_err("expected insert call to fail because key was prefix");
    assert_eq!(
        insert_err,
        InsertPrefixError(Box::<[u8]>::from(&[5, 6, 7, 8][..]))
    );

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_fails_existing_key_prefixed() {
    let mut current_root =
        NodePtr::allocate_node(LeafNode::new(Box::<[u8]>::from(&[1, 2, 3, 4][..]), 0)).to_opaque();
    current_root =
        unsafe { insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8][..]), 1).unwrap() };

    let insert_result =
        unsafe { insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..]), 2) };

    let insert_err =
        insert_result.expect_err("expected insert call to fail because existing key was prefix");
    assert_eq!(
        insert_err,
        InsertPrefixError(Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..]))
    );

    unsafe { deallocate_tree(current_root) };
}
