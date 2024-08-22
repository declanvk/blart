use super::*;
use crate::{deallocate_tree, search_unchecked, tests_common::setup_tree_from_entries, NodeType};

#[test]
fn delete_singleton_tree_leaf() {
    let first_leaf = NodePtr::allocate_node_ptr(LeafNode::<Box<[u8]>, _, 16>::new(
        Box::from([1, 2, 3, 4]),
        "1234".to_string(),
    ));

    let root: OpaqueNodePtr<Box<[u8]>, String, 16> = first_leaf.to_opaque();

    unsafe {
        assert!(search_for_delete_point(root, [1, 2, 3, 5].as_ref()).is_none());
        assert!(search_for_delete_point(root, [1, 2, 3].as_ref()).is_none());
        assert!(search_for_delete_point(root, [].as_ref()).is_none());
        assert!(search_for_delete_point(root, [1, 2, 3, 4, 5, 6].as_ref()).is_none());

        let delete_result = search_for_delete_point(root, [1, 2, 3, 4].as_ref())
            .unwrap()
            .apply(root);
        assert!(delete_result.new_root.is_none());
        assert_eq!(delete_result.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4]);
        assert_eq!(delete_result.deleted_leaf.value_ref(), &"1234");
    }
}

#[test]
fn delete_entire_small_tree() {
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

    let mut root: OpaqueNodePtr<Box<[u8]>, char, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node4);

    unsafe {
        assert!(search_for_delete_point(root, [1, 2, 3, 4, 5, 6, 7].as_ref()).is_none());
        assert!(search_for_delete_point(root, [1, 2, 3, 4, 5, 7].as_ref()).is_none());
        assert!(search_for_delete_point(root, [1, 2, 55, 4, 5, 6].as_ref()).is_none());

        let delete_result = search_for_delete_point(root, [1, 2, 3, 4, 7, 8].as_ref())
            .unwrap()
            .apply(root);
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[1, 2, 3, 4, 7, 8]
        );
        assert_eq!(delete_result.deleted_leaf.value_ref(), &'C');
        let new_root = delete_result.new_root.unwrap();
        assert_eq!(new_root, root);
        root = new_root;

        for (key, value) in ENTRIES.iter().copied() {
            let search_result = search_unchecked(root, key);

            if value == 'C' {
                assert!(search_result.is_none());
            } else {
                assert_eq!(search_result.unwrap().read().value_ref(), &value);
            }
        }

        let delete_result = search_for_delete_point(root, [1, 2, 3, 4, 5, 9].as_ref())
            .unwrap()
            .apply(root);
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[1, 2, 3, 4, 5, 9]
        );
        assert_eq!(delete_result.deleted_leaf.value_ref(), &'D');
        let new_root = delete_result.new_root.unwrap();
        assert_eq!(new_root, root);
        root = new_root;

        let delete_result = search_for_delete_point(root, [2, 4, 6, 8, 10, 12].as_ref())
            .unwrap()
            .apply(root);
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[2, 4, 6, 8, 10, 12]
        );
        assert_eq!(delete_result.deleted_leaf.value_ref(), &'B');
        let new_root = delete_result.new_root.unwrap();
        assert_ne!(new_root, root);
        root = new_root;
        assert_eq!(root.node_type(), NodeType::Leaf);

        let delete_result = search_for_delete_point(root, [1, 2, 3, 4, 5, 6].as_ref())
            .unwrap()
            .apply(root);
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[1, 2, 3, 4, 5, 6]
        );
        assert_eq!(delete_result.deleted_leaf.value_ref(), &'A');
        assert!(delete_result.new_root.is_none());
    }
}

#[test]
fn delete_one_entry_n16_remains() {
    const ENTRIES: &[(&[u8], char)] = &[
        (&[1, 2, 3, 5, 5, 6], 'A'),
        (&[1, 2, 3, 6, 10, 12], 'B'),
        (&[1, 2, 3, 7, 7, 8], 'C'),
        (&[1, 2, 3, 8, 5, 9], 'D'),
        (&[1, 2, 3, 9, 5, 6], 'E'),
        (&[1, 2, 3, 10, 10, 12], 'F'),
        (&[1, 2, 3, 11, 7, 8], 'G'),
        (&[1, 2, 3, 12, 5, 9], 'H'),
        (&[1, 2, 3, 13, 5, 6], 'I'),
    ];

    let entries_it = ENTRIES
        .iter()
        .copied()
        .map(|(key, value)| (Box::<[u8]>::from(key), value));

    let mut root: OpaqueNodePtr<Box<[u8]>, char, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node16);

    unsafe {
        let delete_result = search_for_delete_point(root, [1, 2, 3, 9, 5, 6].as_ref())
            .unwrap()
            .apply(root);
        assert_eq!(delete_result.new_root.unwrap(), root);
        assert_eq!(delete_result.deleted_leaf.value_ref(), &'E');
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[1, 2, 3, 9, 5, 6]
        );

        root = delete_result.new_root.unwrap();
        assert_eq!(root.node_type(), NodeType::Node16);

        deallocate_tree(root);
    }
}

#[test]
fn delete_one_entry_n48_shrinks() {
    let entries_it = (1..=17).map(|value| (Box::<[u8]>::from(&[1, 2, 3, value, 5, 6][..]), value));

    let mut root: OpaqueNodePtr<Box<[u8]>, u8, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node48);

    unsafe {
        let delete_result = search_for_delete_point(root, [1, 2, 3, 9, 5, 6].as_ref())
            .unwrap()
            .apply(root);

        assert_ne!(delete_result.new_root.unwrap(), root);
        assert_eq!(delete_result.deleted_leaf.value_ref(), &9);
        assert_eq!(
            delete_result.deleted_leaf.key_ref().as_ref(),
            &[1, 2, 3, 9, 5, 6]
        );

        root = delete_result.new_root.unwrap();
        assert_eq!(root.node_type(), NodeType::Node16);

        deallocate_tree(root);
    }
}

#[test]
fn delete_one_entry_n256_shrinks() {
    let entries_it = (1..=49).map(|value| (Box::<[u8]>::from(&[1, 2, 3, value, 5, 6][..]), value));

    let mut root: OpaqueNodePtr<Box<[u8]>, u8, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node256);

    let delete = unsafe {
        search_for_delete_point(root, [1, 2, 3, 24, 5, 6].as_ref())
            .unwrap()
            .apply(root)
    };

    assert_ne!(delete.new_root.unwrap(), root);
    assert_eq!(delete.deleted_leaf.value_ref(), &24);
    assert_eq!(delete.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 24, 5, 6]);

    root = delete.new_root.unwrap();
    assert_eq!(root.node_type(), NodeType::Node48);

    unsafe { deallocate_tree(root) };
}

#[test]
fn delete_minimum_singleton_tree() {
    let first_leaf: NodePtr<16, LeafNode<Box<[u8]>, String, 16>> = NodePtr::allocate_node_ptr(
        LeafNode::<Box<[u8]>, _, 16>::new(Box::from([1, 2, 3, 4]), "1234".to_string()),
    );

    let root = first_leaf.to_opaque();

    let delete_result = unsafe { find_minimum_to_delete(root).apply(root) };
    assert!(delete_result.new_root.is_none());
    assert_eq!(delete_result.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4]);
    assert_eq!(delete_result.deleted_leaf.value_ref(), &"1234");
}

#[test]
fn delete_minimum_entire_small_tree() {
    const ENTRIES: &[(&[u8], char)] = &[
        (&[1, 2, 3, 4, 5, 6], 'A'),
        (&[1, 2, 3, 4, 5, 9], 'D'),
        (&[1, 2, 3, 4, 7, 8], 'C'),
        (&[2, 4, 6, 8, 10, 12], 'B'),
    ];

    let entries_it = ENTRIES
        .iter()
        .copied()
        .map(|(key, value)| (Box::<[u8]>::from(key), value));

    let mut root: OpaqueNodePtr<Box<[u8]>, char, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node4);

    let d1 = unsafe { find_minimum_to_delete(root).apply(root) };
    assert_eq!(d1.deleted_leaf.value_ref(), &'A');
    assert_eq!(d1.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 5, 6]);

    let new_root = d1.new_root.unwrap();
    assert_eq!(new_root, root);
    root = new_root;

    for (key, value) in ENTRIES.iter().copied() {
        let search_result = unsafe { search_unchecked(root, key) };

        if value == 'A' {
            assert!(search_result.is_none());
        } else {
            assert_eq!(search_result.unwrap().read().value_ref(), &value);
        }
    }

    let d2 = unsafe { find_minimum_to_delete(root).apply(root) };
    assert_eq!(d2.deleted_leaf.value_ref(), &'D');
    assert_eq!(d2.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 5, 9]);
    let new_root = d2.new_root.unwrap();
    assert_eq!(new_root, root);
    root = new_root;

    let d3 = unsafe { find_minimum_to_delete(root).apply(root) };
    assert_eq!(d3.deleted_leaf.value_ref(), &'C');
    assert_eq!(d3.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 7, 8]);
    let new_root = d3.new_root.unwrap();
    assert_ne!(new_root, root);
    root = new_root;
    assert_eq!(root.node_type(), NodeType::Leaf);

    let d4 = unsafe { find_minimum_to_delete(root).apply(root) };
    assert_eq!(d4.deleted_leaf.value_ref(), &'B');
    assert_eq!(d4.deleted_leaf.key_ref().as_ref(), &[2, 4, 6, 8, 10, 12]);
    assert!(d4.new_root.is_none());
}

#[test]
fn delete_maximum_singleton_tree() {
    let first_leaf: NodePtr<16, LeafNode<Box<[u8]>, String, 16>> = NodePtr::allocate_node_ptr(
        LeafNode::<Box<[u8]>, _, 16>::new(Box::from([1, 2, 3, 4]), "1234".to_string()),
    );

    let root = first_leaf.to_opaque();

    let delete_result = unsafe { find_maximum_to_delete(root).apply(root) };
    assert!(delete_result.new_root.is_none());
    assert_eq!(delete_result.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4]);
    assert_eq!(delete_result.deleted_leaf.value_ref(), &"1234");
}

#[test]
fn delete_maximum_entire_small_tree() {
    const ENTRIES: &[(&[u8], char)] = &[
        (&[2, 4, 6, 8, 10, 12], 'B'),
        (&[1, 2, 3, 4, 7, 8], 'C'),
        (&[1, 2, 3, 4, 5, 9], 'D'),
        (&[1, 2, 3, 4, 5, 6], 'A'),
    ];

    let entries_it = ENTRIES
        .iter()
        .copied()
        .map(|(key, value)| (Box::<[u8]>::from(key), value));

    let mut root: OpaqueNodePtr<Box<[u8]>, char, 16> = setup_tree_from_entries(entries_it);

    assert_eq!(root.node_type(), NodeType::Node4);

    let d1 = unsafe { find_maximum_to_delete(root).apply(root) };
    assert_eq!(d1.deleted_leaf.value_ref(), &'B');
    assert_eq!(d1.deleted_leaf.key_ref().as_ref(), &[2, 4, 6, 8, 10, 12]);

    let new_root = d1.new_root.unwrap();
    // root moved
    assert_ne!(new_root, root);
    root = new_root;

    for (key, value) in ENTRIES.iter().copied() {
        let search_result = unsafe { search_unchecked(root, key) };

        if value == 'B' {
            assert!(search_result.is_none());
        } else {
            assert_eq!(search_result.unwrap().read().value_ref(), &value);
        }
    }

    let d2 = unsafe { find_maximum_to_delete(root).apply(root) };
    assert_eq!(d2.deleted_leaf.value_ref(), &'C');
    assert_eq!(d2.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 7, 8]);
    let new_root = d2.new_root.unwrap();
    // root moved again
    assert_ne!(new_root, root);
    root = new_root;

    let d3 = unsafe { find_maximum_to_delete(root).apply(root) };
    assert_eq!(d3.deleted_leaf.value_ref(), &'D');
    assert_eq!(d3.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 5, 9]);
    let new_root = d3.new_root.unwrap();
    assert_ne!(new_root, root);
    root = new_root;
    assert_eq!(root.node_type(), NodeType::Leaf);

    let d4 = unsafe { find_maximum_to_delete(root).apply(root) };
    assert_eq!(d4.deleted_leaf.value_ref(), &'A');
    assert_eq!(d4.deleted_leaf.key_ref().as_ref(), &[1, 2, 3, 4, 5, 6]);
    assert!(d4.new_root.is_none());
}
