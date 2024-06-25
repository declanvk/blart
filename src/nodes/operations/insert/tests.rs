use crate::{
    deallocate_tree, search_unchecked,
    tests_common::{generate_keys_skewed, insert_unchecked, setup_tree_from_entries},
    AsBytes, InnerNode, InnerNode4, InnerNodeCompressed, InsertPrefixError, LeafNode, NodePtr,
    NodeType, OpaqueNodePtr,
};

#[test]
fn insert_to_small_trees() {
    let first_leaf: NodePtr<16, LeafNode<Box<_>, String, 16>> =
        NodePtr::allocate_node_ptr(LeafNode::new(Box::from([1, 2, 3, 4]), "1234".to_string()));

    let mut tree = first_leaf.to_opaque();
    tree = unsafe {
        insert_unchecked(tree, Box::from([1, 2, 5, 6]), "1256".to_string())
            .unwrap()
            .new_root
    };

    assert_eq!(tree.node_type(), NodeType::Node4);

    let new_root: NodePtr<16, InnerNodeCompressed<Box<[u8]>, String, 16, 4>> =
        tree.cast::<InnerNode4<Box<[u8]>, String, 16>>().unwrap();

    {
        let root = new_root.read();

        assert_eq!(root.header.read_prefix(), &[1, 2]);
        assert!(root.lookup_child(5).is_some());
        assert_eq!(root.lookup_child(3), Some(first_leaf.to_opaque()));
        assert_eq!(root.lookup_child(1), None);
    }
    assert_eq!(
        unsafe {
            &search_unchecked(new_root.to_opaque(), [1, 2, 5, 6].as_ref())
                .unwrap()
                .read()
                .value_ref()
        },
        &"1256"
    );
    assert_eq!(
        unsafe {
            &search_unchecked(new_root.to_opaque(), [1, 2, 3, 4].as_ref())
                .unwrap()
                .read()
                .value_ref()
        },
        &"1234"
    );
    assert!(unsafe { search_unchecked(new_root.to_opaque(), [1, 2, 5, 7].as_ref()).is_none() });
    assert!(unsafe { search_unchecked(new_root.to_opaque(), [1, 2, 3, 5].as_ref()).is_none() });

    unsafe { deallocate_tree(new_root.to_opaque()) };
}

#[test]
fn insert_into_left_skewed_tree_deallocate() {
    #[cfg(not(miri))]
    const KEY_LENGTH_LIMIT: usize = u8::MAX as usize;

    #[cfg(miri)]
    const KEY_LENGTH_LIMIT: usize = 16usize;

    let mut keys = generate_keys_skewed(KEY_LENGTH_LIMIT);
    let mut current_root: OpaqueNodePtr<Box<[u8]>, usize, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        current_root = unsafe {
            insert_unchecked(current_root, key, idx + 1)
                .unwrap()
                .new_root
        };
    }

    for (value, key) in generate_keys_skewed(KEY_LENGTH_LIMIT).enumerate() {
        let search_result = unsafe { search_unchecked(current_root, &key) };

        assert_eq!(*search_result.unwrap().read().value_ref(), value);
    }

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_prefix_key_errors() {
    let first_leaf: NodePtr<16, LeafNode<Box<[u8]>, String, 16>> = NodePtr::allocate_node_ptr(
        LeafNode::<Box<[u8]>, _, 16>::new(Box::from([1, 2, 3, 4]), "1234".to_string()),
    );

    let tree = first_leaf.to_opaque();
    let result = unsafe { insert_unchecked(tree, Box::from([1, 2]), "12".to_string()) };

    assert_eq!(
        result.unwrap_err(),
        InsertPrefixError {
            byte_repr: Box::from([1, 2])
        }
    );

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_prefix_key_with_existing_prefix_errors() {
    let first_leaf: NodePtr<16, LeafNode<Box<[u8]>, String, 16>> = NodePtr::allocate_node_ptr(
        LeafNode::<Box<[u8]>, _, 16>::new(Box::from([1, 2]), "12".to_string()),
    );

    let tree = first_leaf.to_opaque();
    let result = unsafe { insert_unchecked(tree, Box::from([1, 2, 3, 4]), "1234".to_string()) };

    assert_eq!(
        result.unwrap_err(),
        InsertPrefixError {
            byte_repr: Box::from([1, 2, 3, 4])
        }
    );

    unsafe { deallocate_tree(tree) }
}

#[test]
fn insert_key_with_long_prefix_then_split() {
    let first_leaf: NodePtr<16, LeafNode<Box<[u8]>, i32, 16>> = NodePtr::allocate_node_ptr(
        LeafNode::<Box<[u8]>, _, 16>::new(Box::from([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 255]), 0),
    );

    let mut tree = first_leaf.to_opaque();
    tree = unsafe {
        insert_unchecked(tree, Box::from([1, 1, 1, 1, 1, 1, 1, 1, 1, 255]), 1)
            .unwrap()
            .new_root
    };

    tree = unsafe {
        insert_unchecked(tree, Box::from([1, 1, 255]), 2)
            .unwrap()
            .new_root
    };

    assert_eq!(
        unsafe {
            search_unchecked(tree, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 255].as_ref())
                .unwrap()
                .read()
                .value_ref()
        },
        &0
    );
    assert_eq!(
        unsafe {
            search_unchecked(tree, [1, 1, 1, 1, 1, 1, 1, 1, 1, 255].as_ref())
                .unwrap()
                .read()
                .value_ref()
        },
        &1
    );
    assert_eq!(
        unsafe {
            search_unchecked(tree, [1, 1, 255].as_ref())
                .unwrap()
                .read()
                .value_ref()
        },
        &2
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

    let mut current_root: OpaqueNodePtr<Box<[u8]>, usize, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        current_root = unsafe {
            insert_unchecked(current_root, key, idx + 1)
                .unwrap()
                .new_root
        };
    }

    for (value, key) in KEYS.iter().map(|k| &k[..]).enumerate() {
        let search_result = unsafe { search_unchecked(current_root, key) };

        assert_eq!(search_result.unwrap().read().value_ref(), &value);
    }

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_fails_new_key_prefix_of_existing_entry() {
    let mut current_root: OpaqueNodePtr<Box<[u8]>, i32, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(Box::<[u8]>::from(&[1, 2, 3, 4][..]), 0))
            .to_opaque();
    current_root = unsafe {
        insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..]), 1)
            .unwrap()
            .new_root
    };

    let insert_result =
        unsafe { insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8][..]), 2) };

    let insert_err =
        insert_result.expect_err("expected insert call to fail because key was prefix");
    assert_eq!(
        insert_err,
        InsertPrefixError {
            byte_repr: Box::<[u8]>::from(&[5, 6, 7, 8][..])
        }
    );

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_fails_existing_key_prefixed() {
    let mut current_root: OpaqueNodePtr<Box<[u8]>, i32, 16> =
        NodePtr::allocate_node_ptr(LeafNode::new(Box::<[u8]>::from(&[1, 2, 3, 4][..]), 0))
            .to_opaque();
    current_root = unsafe {
        insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8][..]), 1)
            .unwrap()
            .new_root
    };

    let insert_result =
        unsafe { insert_unchecked(current_root, Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..]), 2) };

    let insert_err =
        insert_result.expect_err("expected insert call to fail because existing key was prefix");
    assert_eq!(
        insert_err,
        InsertPrefixError {
            byte_repr: Box::<[u8]>::from(&[5, 6, 7, 8, 9, 10][..])
        }
    );

    unsafe { deallocate_tree(current_root) };
}

#[test]
fn insert_existing_key_overwrite() {
    const ENTRIES: &[(&[u8], char)] = &[
        (&[1, 2, 3, 4, 5, 6], 'A'),
        (&[2, 4, 6, 8, 10, 12], 'B'),
        (&[1, 2, 3, 4, 7, 8], 'C'),
        (&[1, 2, 3, 4, 5, 9], 'D'),
    ];

    let entries_it = ENTRIES
        .iter()
        .copied()
        .map(|(key, value)| (Box::<[u8]>::from(key), value));

    let current_root: OpaqueNodePtr<Box<[u8]>, char, 16> = setup_tree_from_entries(entries_it);

    unsafe fn get_value<K: AsBytes, V: Copy, const NUM_PREFIX_BYTES: usize>(
        n: NodePtr<NUM_PREFIX_BYTES, LeafNode<K, V, NUM_PREFIX_BYTES>>,
    ) -> V {
        unsafe { *n.as_ref().value_ref() }
    }

    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 5, 6].as_ref()).unwrap()) },
        'A'
    );
    assert_eq!(
        unsafe {
            get_value(search_unchecked(current_root, [2, 4, 6, 8, 10, 12].as_ref()).unwrap())
        },
        'B'
    );
    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 7, 8].as_ref()).unwrap()) },
        'C'
    );
    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 5, 9].as_ref()).unwrap()) },
        'D'
    );

    let insert_result = unsafe {
        insert_unchecked(
            current_root,
            Box::<[u8]>::from(&[1, 2, 3, 4, 5, 9][..]),
            'W',
        )
        .unwrap()
    };
    assert_eq!(insert_result.new_root, current_root);
    assert_eq!(insert_result.existing_leaf.unwrap().value_ref(), &'D');

    let insert_result = unsafe {
        insert_unchecked(
            current_root,
            Box::<[u8]>::from(&[1, 2, 3, 4, 7, 8][..]),
            'X',
        )
        .unwrap()
    };
    assert_eq!(insert_result.new_root, current_root);
    assert_eq!(insert_result.existing_leaf.unwrap().value_ref(), &'C');

    let insert_result = unsafe {
        insert_unchecked(
            current_root,
            Box::<[u8]>::from(&[2, 4, 6, 8, 10, 12][..]),
            'Y',
        )
        .unwrap()
    };
    assert_eq!(insert_result.new_root, current_root);
    assert_eq!(insert_result.existing_leaf.unwrap().value_ref(), &'B');

    let insert_result = unsafe {
        insert_unchecked(
            current_root,
            Box::<[u8]>::from(&[1, 2, 3, 4, 5, 6][..]),
            'Z',
        )
        .unwrap()
    };
    assert_eq!(insert_result.new_root, current_root);
    assert_eq!(insert_result.existing_leaf.unwrap().value_ref(), &'A');

    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 5, 6].as_ref()).unwrap()) },
        'Z'
    );
    assert_eq!(
        unsafe {
            get_value(search_unchecked(current_root, [2, 4, 6, 8, 10, 12].as_ref()).unwrap())
        },
        'Y'
    );
    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 7, 8].as_ref()).unwrap()) },
        'X'
    );
    assert_eq!(
        unsafe { get_value(search_unchecked(current_root, [1, 2, 3, 4, 5, 9].as_ref()).unwrap()) },
        'W'
    );

    unsafe { deallocate_tree(current_root) }
}
