use crate::{
    deallocate_tree, tests_common::{generate_key_fixed_length, insert_unchecked}, LeafNode, NodePtr,
    TreeIterator,
};

fn map_item_to_ref<'a, K, V>(leaf_node_ptr: NodePtr<LeafNode<K, V>>) -> (&'a K, &'a V) {
    let (key, value) = unsafe { leaf_node_ptr.as_key_value_ref() };
    (key, value)
}

#[test]
fn small_tree_iterator_front_and_back() {
    let keys: [Box<[u8]>; 9] = [
        vec![114, 159, 30].into_boxed_slice(),  // 0
        vec![30, 159, 204].into_boxed_slice(),  // 1
        vec![92, 39, 116].into_boxed_slice(),   // 2
        vec![58, 7, 66].into_boxed_slice(),     // 3
        vec![70, 30, 139].into_boxed_slice(),   // 4
        vec![220, 78, 94].into_boxed_slice(),   // 5
        vec![52, 231, 124].into_boxed_slice(),  // 6
        vec![173, 226, 147].into_boxed_slice(), // 7
        vec![6, 193, 187].into_boxed_slice(),   // 8
    ];

    let root = {
        let mut keys = keys.into_iter().enumerate();
        let mut root =
            NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap().1, 0)).to_opaque();

        for (idx, key) in keys {
            root = unsafe { insert_unchecked(root, key, idx).unwrap().new_root };
        }

        root
    };

    let mut trie_iter = unsafe { TreeIterator::new(root) };

    assert_eq!(
        trie_iter.next().map(map_item_to_ref),
        Some((&[6, 193, 187].into(), &8))
    );
    assert_eq!(
        trie_iter.next().map(map_item_to_ref),
        Some((&[30, 159, 204].into(), &1))
    );
    assert_eq!(
        trie_iter.next_back().map(map_item_to_ref),
        Some((&[220, 78, 94].into(), &5))
    );
    assert_eq!(
        trie_iter.next_back().map(map_item_to_ref),
        Some((&[173, 226, 147].into(), &7))
    );

    let rest = trie_iter.map(map_item_to_ref).collect::<Vec<_>>();
    assert_eq!(rest.len(), 5);
    assert_eq!(
        rest,
        vec![
            (&[52, 231, 124].into(), &6),
            (&[58, 7, 66].into(), &3),
            (&[70, 30, 139].into(), &4),
            (&[92, 39, 116].into(), &2),
            (&[114, 159, 30].into(), &0),
        ]
    );

    unsafe { deallocate_tree(root) };
}

#[test]
fn large_fixed_length_key_iterator_front_back() {
    struct TestValues {
        value_stops: u8,
        half_len: usize,
        first_half_last: [u8; 3],
        last_half_last: [u8; 3],
    }

    #[cfg(not(miri))]
    const TEST_PARAMS: TestValues = TestValues {
        value_stops: 5,
        half_len: 108,
        first_half_last: [102, 255, 255],
        last_half_last: [153, 0, 0],
    };
    #[cfg(miri)]
    const TEST_PARAMS: TestValues = TestValues {
        value_stops: 3,
        half_len: 32,
        first_half_last: [85, 255, 255],
        last_half_last: [170, 0, 0],
    };

    let mut keys = generate_key_fixed_length([TEST_PARAMS.value_stops; 3]);
    let mut root = NodePtr::allocate_node_ptr(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        root = unsafe { insert_unchecked(root, key, idx + 1).unwrap().new_root };
    }

    let mut trie_iter = unsafe { TreeIterator::new(root) }
        .map(map_item_to_ref)
        .map(|(key, _)| key);

    let first_remaining_half = trie_iter
        .by_ref()
        .take(TEST_PARAMS.half_len)
        .collect::<Vec<_>>();
    let last_remaining_half = trie_iter
        .by_ref()
        .rev()
        .take(TEST_PARAMS.half_len)
        .collect::<Vec<_>>();

    assert!(trie_iter.next().is_none());

    assert_eq!(first_remaining_half.len(), TEST_PARAMS.half_len);
    assert_eq!(last_remaining_half.len(), TEST_PARAMS.half_len);

    assert_eq!(first_remaining_half[0], &[0, 0, 0].into());
    assert_eq!(
        first_remaining_half[first_remaining_half.len() - 1],
        &TEST_PARAMS.first_half_last.into()
    );
    assert_eq!(last_remaining_half[0], &[255, 255, 255].into());
    assert_eq!(
        last_remaining_half[last_remaining_half.len() - 1],
        &TEST_PARAMS.last_half_last.into()
    );

    unsafe { deallocate_tree(root) }
}
