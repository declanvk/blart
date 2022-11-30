use super::*;
use std::mem;

#[cfg(not(feature = "nightly"))]
use sptr::Strict;

#[test]
fn opaque_node_ptr_is_correct() {
    let mut n4 = InnerNode4::<usize>::empty();
    let mut n16 = InnerNode16::<usize>::empty();
    let mut n48 = InnerNode48::<usize>::empty();
    let mut n256 = InnerNode256::<usize>::empty();

    let n4_ptr = NodePtr::from(&mut n4).to_opaque();
    let n16_ptr = NodePtr::from(&mut n16).to_opaque();
    let n48_ptr = NodePtr::from(&mut n48).to_opaque();
    let n256_ptr = NodePtr::from(&mut n256).to_opaque();

    assert!(n4_ptr.is::<InnerNode4<usize>>());
    assert!(n16_ptr.is::<InnerNode16<usize>>());
    assert!(n48_ptr.is::<InnerNode48<usize>>());
    assert!(n256_ptr.is::<InnerNode256<usize>>());
}

#[test]
#[cfg(target_pointer_width = "64")]
fn node_sizes() {
    let expected_header_size = if cfg!(any(miri, feature = "nightly")) {
        40
    } else {
        32
    };

    assert_eq!(mem::size_of::<Header>(), expected_header_size);
    // key map: 4 * (1 byte) = 4 bytes
    // child map: 4 * (8 bytes (on 64-bit platform)) = 32
    //
    // 4 bytes of padding are inserted after the `keys` field to align the field to
    // an 8 byte boundary.
    assert_eq!(
        mem::size_of::<InnerNode4<usize>>(),
        expected_header_size + 40
    );
    // key map: 16 * (1 byte) = 16 bytes
    // child map: 16 * (8 bytes (on 64-bit platform)) = 128
    assert_eq!(
        mem::size_of::<InnerNode16<usize>>(),
        expected_header_size + 144
    );
    // key map: 256 * (1 byte) = 256 bytes
    // child map: 48 * (8 bytes (on 64-bit platform)) = 384
    assert_eq!(
        mem::size_of::<InnerNode48<usize>>(),
        expected_header_size + 640
    );
    // child & key map: 256 * (8 bytes (on 64-bit platform)) = 2048
    assert_eq!(
        mem::size_of::<InnerNode256<usize>>(),
        expected_header_size + 2048
    );

    // Assert that pointer is expected size and has non-null optimization
    assert_eq!(mem::size_of::<Option<OpaqueNodePtr<()>>>(), 8);
    assert_eq!(mem::size_of::<OpaqueNodePtr<()>>(), 8);
}

#[test]
fn node_alignment() {
    assert_eq!(mem::align_of::<InnerNode4<u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode16<u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode48<u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode256<u8>>(), 8);
    assert_eq!(mem::align_of::<LeafNode<u8>>(), 8);
    assert_eq!(mem::align_of::<Header>(), 8);

    assert_eq!(
        mem::align_of::<InnerNode4<u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode16<u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode48<u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode256<u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<LeafNode<u8>>(),
        mem::align_of::<OpaqueValue>()
    );

    let n4 = InnerNode4::<()>::empty();
    let n16 = InnerNode4::<()>::empty();
    let n48 = InnerNode4::<()>::empty();
    let n256 = InnerNode4::<()>::empty();

    let n4_ptr = (&n4 as *const InnerNode4<()>).addr();
    let n16_ptr = (&n16 as *const InnerNode4<()>).addr();
    let n48_ptr = (&n48 as *const InnerNode4<()>).addr();
    let n256_ptr = (&n256 as *const InnerNode4<()>).addr();

    // Ensure that there are 3 bits of unused space in the node pointer because of
    // the alignment.
    assert!(n4_ptr.trailing_zeros() >= 3);
    assert!(n16_ptr.trailing_zeros() >= 3);
    assert!(n48_ptr.trailing_zeros() >= 3);
    assert!(n256_ptr.trailing_zeros() >= 3);
}

fn inner_node_write_child_test(mut node: impl InnerNode<Value = ()>, num_children: usize) {
    let mut leaves = vec![LeafNode::new(vec![].into(), ()); num_children];

    assert!(!node.is_full());
    {
        let leaf_pointers = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect::<Vec<_>>();

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
        }

        for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
            assert_eq!(
                node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }
    }
    assert!(node.is_full());
}

fn inner_node_remove_child_test(mut node: impl InnerNode<Value = ()>, num_children: usize) {
    let mut leaves = vec![LeafNode::new(vec![].into(), ()); num_children];

    assert!(!node.is_full());
    {
        let leaf_pointers = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect::<Vec<_>>();

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
        }

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            assert_eq!(
                node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            assert_eq!(
                node.remove_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );

            assert_eq!(node.lookup_child(u8::try_from(idx).unwrap()), None);
        }
    }
    assert!(!node.is_full());
}

fn inner_node_shrink_test(mut node: impl InnerNode<Value = ()>, num_children: usize) {
    let mut leaves = vec![LeafNode::new(vec![].into(), ()); num_children];

    let leaf_pointers = leaves
        .iter_mut()
        .map(|leaf| NodePtr::from(leaf).to_opaque())
        .collect::<Vec<_>>();

    for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
        node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
    }

    let shrunk_node = node.shrink();

    for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
        assert_eq!(
            shrunk_node.lookup_child(u8::try_from(idx).unwrap()),
            Some(leaf_pointer)
        );
    }
}

fn inner_node_split_at_on_test_keys_moved(
    mut node: impl InnerNode<Value = ()>,
    children_key_fragments: &[u8],
    split_key_fragment: u8,
) {
    assert!(children_key_fragments.len() < usize::from(u8::MAX));
    let total_num_children = children_key_fragments.len();
    // this ensures that the vector is never resized and the mutable references
    // aren't invalid pointers later on (not that we're using the pointers at all)
    let mut leaves = Vec::with_capacity(total_num_children);

    for key_fragment in children_key_fragments {
        leaves.push(LeafNode::new(vec![].into(), ()));
        let last_leaf = NodePtr::from(leaves.last_mut().unwrap()).to_opaque();
        node.write_child(*key_fragment, last_leaf);
    }

    let split_node = node.split_at(split_key_fragment);

    assert_eq!(node.header().prefix, split_node.header().prefix);

    for (idx, key_fragment) in children_key_fragments.iter().copied().enumerate() {
        let leaf_pointer = NodePtr::from(&mut leaves[idx]).to_opaque();
        if key_fragment < split_key_fragment {
            assert_eq!(node.lookup_child(key_fragment), Some(leaf_pointer));
            assert_eq!(split_node.lookup_child(key_fragment), None);
        } else {
            assert_eq!(node.lookup_child(key_fragment), None);
            assert_eq!(split_node.lookup_child(key_fragment), Some(leaf_pointer));
        }
    }

    let split_idx = children_key_fragments.partition_point(|x| *x < split_key_fragment);

    assert_eq!(node.header().num_children(), split_idx);
    assert_eq!(
        split_node.header().num_children(),
        total_num_children - split_idx
    );
}

#[test]
fn node4_lookup() {
    let mut n = InnerNode4::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    assert!(n.lookup_child(123).is_none());

    n.header.num_children = 3;
    n.keys[0].write(3);
    n.keys[1].write(123);
    n.keys[2].write(1);

    n.child_pointers[0].write(l1_ptr);
    n.child_pointers[1].write(l2_ptr);
    n.child_pointers[2].write(l3_ptr);

    assert_eq!(n.lookup_child(123), Some(l2_ptr));
}

#[test]
fn node4_write_child() {
    inner_node_write_child_test(InnerNode4::empty(), 4)
}

#[test]
fn node4_remove_child() {
    inner_node_remove_child_test(InnerNode4::empty(), 4)
}

#[test]
#[should_panic]
fn node4_write_child_full_panic() {
    inner_node_write_child_test(InnerNode4::empty(), 5);
}

#[test]
fn node4_grow() {
    let mut n4 = InnerNode4::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n4.write_child(3, l1_ptr);
    n4.write_child(123, l2_ptr);
    n4.write_child(1, l3_ptr);

    let n16 = n4.grow();

    assert_eq!(n16.lookup_child(3), Some(l1_ptr));
    assert_eq!(n16.lookup_child(123), Some(l2_ptr));
    assert_eq!(n16.lookup_child(1), Some(l3_ptr));
    assert_eq!(n16.lookup_child(4), None);
}

#[test]
#[should_panic]
fn node4_shrink() {
    let n4 = InnerNode4::<()>::empty();

    n4.shrink();
}

#[test]
fn node4_split_at_on_existing_key() {
    inner_node_split_at_on_test_keys_moved(InnerNode4::<()>::empty(), &[1, 3, 82, 123], 82);
}

#[test]
fn node4_split_at_on_non_existent_key() {
    inner_node_split_at_on_test_keys_moved(InnerNode4::<()>::empty(), &[1, 3, 82, 123], 66);
}

#[test]
fn node4_split_at_both_empty_ends() {
    inner_node_split_at_on_test_keys_moved(InnerNode4::<()>::empty(), &[1, 3, 82, 123], 0);
    inner_node_split_at_on_test_keys_moved(InnerNode4::<()>::empty(), &[1, 3, 82, 123], 244);
}

#[test]
fn node16_lookup() {
    let mut n = InnerNode16::empty();
    let mut l1 = LeafNode::new(Box::new([]), ());
    let mut l2 = LeafNode::new(Box::new([]), ());
    let mut l3 = LeafNode::new(Box::new([]), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    assert!(n.lookup_child(123).is_none());

    n.header.num_children = 3;
    n.keys[0].write(3);
    n.keys[1].write(123);
    n.keys[2].write(1);

    n.child_pointers[0].write(l1_ptr);
    n.child_pointers[1].write(l2_ptr);
    n.child_pointers[2].write(l3_ptr);

    assert_eq!(n.lookup_child(123), Some(l2_ptr));
}

#[test]
fn node16_write_child() {
    inner_node_write_child_test(InnerNode16::empty(), 16)
}

#[test]
fn node16_remove_child() {
    inner_node_remove_child_test(InnerNode16::empty(), 16)
}

#[test]
#[should_panic]
fn node16_write_child_full_panic() {
    inner_node_write_child_test(InnerNode16::empty(), 17);
}

#[test]
fn node16_grow() {
    let mut n16 = InnerNode16::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n16.write_child(3, l1_ptr);
    n16.write_child(123, l2_ptr);
    n16.write_child(1, l3_ptr);

    let n48 = n16.grow();

    assert_eq!(n48.lookup_child(3), Some(l1_ptr));
    assert_eq!(n48.lookup_child(123), Some(l2_ptr));
    assert_eq!(n48.lookup_child(1), Some(l3_ptr));
    assert_eq!(n48.lookup_child(4), None);
}

#[test]
fn node16_shrink() {
    inner_node_shrink_test(InnerNode16::empty(), 4);
}

#[test]
#[should_panic]
fn node16_shrink_too_many_children_panic() {
    inner_node_shrink_test(InnerNode16::empty(), 5);
}

#[test]
fn node16_split_at_on_existing_key() {
    inner_node_split_at_on_test_keys_moved(
        InnerNode16::<()>::empty(),
        &[1, 3, 17, 29, 42, 82, 89, 123, 137, 201],
        82,
    );
}

#[test]
fn node16_split_at_on_non_existent_key() {
    inner_node_split_at_on_test_keys_moved(
        InnerNode16::<()>::empty(),
        &[1, 3, 17, 29, 42, 82, 89, 123, 137, 201],
        66,
    );
}

#[test]
fn node16_split_at_both_empty_ends() {
    inner_node_split_at_on_test_keys_moved(
        InnerNode16::<()>::empty(),
        &[1, 3, 17, 29, 42, 82, 89, 123, 137, 201],
        0,
    );
    inner_node_split_at_on_test_keys_moved(
        InnerNode16::<()>::empty(),
        &[1, 3, 17, 29, 42, 82, 89, 123, 137, 201],
        244,
    );
}

#[test]
fn node48_lookup() {
    let mut n = InnerNode48::empty();
    let mut l1 = LeafNode::new(Box::new([]), ());
    let mut l2 = LeafNode::new(Box::new([]), ());
    let mut l3 = LeafNode::new(Box::new([]), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    assert!(n.lookup_child(123).is_none());

    n.header.num_children = 3;

    n.child_indices[1] = 2usize.try_into().unwrap();
    n.child_indices[3] = 0usize.try_into().unwrap();
    n.child_indices[123] = 1usize.try_into().unwrap();

    n.child_pointers[0].write(l1_ptr);
    n.child_pointers[1].write(l2_ptr);
    n.child_pointers[2].write(l3_ptr);

    assert_eq!(n.lookup_child(123), Some(l2_ptr));
}

#[test]
fn node48_write_child() {
    inner_node_write_child_test(InnerNode48::empty(), 48)
}

#[test]
fn node48_remove_child() {
    inner_node_remove_child_test(InnerNode48::empty(), 48)
}

#[test]
#[should_panic]
fn node48_write_child_full_panic() {
    inner_node_write_child_test(InnerNode48::empty(), 49);
}

#[test]
fn node48_grow() {
    let mut n48 = InnerNode48::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n48.write_child(3, l1_ptr);
    n48.write_child(123, l2_ptr);
    n48.write_child(1, l3_ptr);

    let n256 = n48.grow();

    assert_eq!(n256.lookup_child(3), Some(l1_ptr));
    assert_eq!(n256.lookup_child(123), Some(l2_ptr));
    assert_eq!(n256.lookup_child(1), Some(l3_ptr));
    assert_eq!(n256.lookup_child(4), None);
}

#[test]
fn node48_shrink() {
    inner_node_shrink_test(InnerNode48::empty(), 16);
}

#[test]
#[should_panic]
fn node48_shrink_too_many_children_panic() {
    inner_node_shrink_test(InnerNode48::empty(), 17);
}

#[test]
fn node48_split_at_on_existing_key() {
    let keys = (0..=47u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode48::<()>::empty(), keys.as_ref(), 34);
}

#[test]
fn node48_split_at_on_non_existent_key() {
    let keys = (0..=47u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode48::<()>::empty(), keys.as_ref(), 35);
}

#[test]
fn node48_split_at_both_empty_ends() {
    let keys = (0..=47u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode48::<()>::empty(), keys.as_ref(), 0);
    inner_node_split_at_on_test_keys_moved(InnerNode48::<()>::empty(), keys.as_ref(), 47);
}

#[test]
fn node256_lookup() {
    let mut n = InnerNode256::empty();
    let mut l1 = LeafNode::new(Box::new([]), ());
    let mut l2 = LeafNode::new(Box::new([]), ());
    let mut l3 = LeafNode::new(Box::new([]), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    assert!(n.lookup_child(123).is_none());

    n.header.num_children = 3;

    n.child_pointers[1] = Some(l1_ptr);
    n.child_pointers[123] = Some(l2_ptr);
    n.child_pointers[3] = Some(l3_ptr);

    assert_eq!(n.lookup_child(123), Some(l2_ptr));
}

#[test]
fn node256_write_child() {
    inner_node_write_child_test(InnerNode256::empty(), 256)
}

#[test]
fn node256_remove_child() {
    inner_node_remove_child_test(InnerNode256::empty(), 256)
}

#[test]
#[should_panic]
fn node256_grow() {
    let n = InnerNode256::<()>::empty();

    n.grow();
}

#[test]
fn node256_shrink() {
    inner_node_shrink_test(InnerNode256::empty(), 48);
}

#[test]
#[should_panic]
fn node256_shrink_too_many_children_panic() {
    inner_node_shrink_test(InnerNode256::empty(), 49);
}

#[test]
fn node256_split_at_on_existing_key() {
    let keys = (0..=255u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode256::<()>::empty(), keys.as_ref(), 82);
}

#[test]
fn node256_split_at_on_non_existent_key() {
    let keys = (0..=255u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode256::<()>::empty(), keys.as_ref(), 65);
}

#[test]
fn node256_split_at_both_empty_ends() {
    let keys = (0..=255u8).filter(|key| key % 2 == 0).collect::<Vec<_>>();
    inner_node_split_at_on_test_keys_moved(InnerNode256::<()>::empty(), keys.as_ref(), 0);
    inner_node_split_at_on_test_keys_moved(InnerNode256::<()>::empty(), keys.as_ref(), 255);
}

#[test]
fn header_read_write_prefix() {
    let mut h = Header::empty();

    assert_eq!(h.prefix_size(), 0);
    assert_eq!(h.read_prefix(), &[]);

    h.extend_prefix(&[1, 2, 3]);

    assert_eq!(h.prefix_size(), 3);
    assert_eq!(h.read_prefix(), &[1, 2, 3]);

    h.extend_prefix(&[4, 5, 6]);

    assert_eq!(h.prefix_size(), 6);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6]);

    h.extend_prefix(&[7, 8]);

    assert_eq!(h.prefix_size(), 8);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

    h.extend_prefix(&[9, 10, 11, 12]);

    assert_eq!(h.prefix_size(), 12);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);

    h.extend_prefix(&[]);

    assert_eq!(h.prefix_size(), 12);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
}

#[test]
fn header_prepend_prefix() {
    let mut h = Header::default();

    assert_eq!(h.prefix_size(), 0);
    assert_eq!(h.read_prefix(), &[]);

    h.prepend_prefix(&[]);

    assert_eq!(h.prefix_size(), 0);
    assert_eq!(h.read_prefix(), &[]);

    h.prepend_prefix(&[1, 2, 3]);

    assert_eq!(h.prefix_size(), 3);
    assert_eq!(h.read_prefix(), &[1, 2, 3]);

    h.prepend_prefix(&[4, 5, 6]);

    assert_eq!(h.prefix_size(), 6);
    assert_eq!(h.read_prefix(), &[4, 5, 6, 1, 2, 3]);

    h.extend_prefix(&[7, 8, 9]);

    assert_eq!(h.prefix_size(), 9);
    assert_eq!(h.read_prefix(), &[4, 5, 6, 1, 2, 3, 7, 8, 9]);
}

#[test]
fn header_check_prefix() {
    let mut h = Header::empty();

    h.extend_prefix(&[1, 2, 3]);

    assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
    assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
    assert_eq!(h.match_prefix(&[1, 2]), 2);
    assert_eq!(h.match_prefix(&[]), 0);

    h.extend_prefix(&[4, 5, 6, 7, 8, 9, 10, 11, 12]);

    assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
    assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
    assert_eq!(h.match_prefix(&[1, 2]), 2);
    assert_eq!(h.match_prefix(&[]), 0);

    assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]), 8);
    assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), 12);
    assert_eq!(
        h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]),
        12
    );
    assert_eq!(
        h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 100, 200, 254, 255]),
        8
    );
}

#[test]
fn empty_prefix_bytes_match() {
    let mut h = Header::empty();

    h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
    h.ltrim_prefix(NUM_PREFIX_BYTES);
    // 6 bytes are represented

    assert_eq!(h.match_prefix(&[1, 2, 3]), 0);
    assert_eq!(h.match_prefix(&[0]), 0);
    assert_eq!(h.match_prefix(&[]), 0);
    assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6]), 0);
    assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), 0);

    assert_eq!(h.match_prefix(&[9, 10, 11, 12]), 4);
    assert_eq!(h.match_prefix(&[9, 10, 11, 12, 13, 14]), 6);
}

#[test]
fn header_delete_prefix() {
    let mut h = Header::empty();
    h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 8);

    h.ltrim_prefix(0);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 8);

    h.ltrim_prefix(3);
    assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 5);

    h.ltrim_prefix(1);
    assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 4);

    h.ltrim_prefix(4);
    assert_eq!(h.read_prefix(), &[]);
    assert_eq!(h.prefix_size(), 0);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_too_many_bytes_panic() {
    let mut h = Header::empty();
    h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 8);

    h.ltrim_prefix(10);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_non_stored_bytes_panic() {
    let mut h = Header::empty();
    h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size(), 8);

    h.ltrim_prefix(0);
}
