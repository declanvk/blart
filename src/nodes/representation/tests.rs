use super::*;
use std::{ffi::CString, mem};

#[cfg(not(feature = "nightly"))]
use sptr::Strict;

// This test is important because it verifies that we can transform a tagged
// pointer to a type with large and small alignment and back without issues.
#[test]
fn leaf_node_alignment() {
    let mut p0 = TaggedPointer::<LeafNode<[u8; 0], _>, 3>::new(Box::into_raw(Box::new(
        LeafNode::new([], 3u8),
    )))
    .unwrap()
    .cast::<OpaqueValue>();
    p0.set_data(0b001);

    #[repr(align(64))]
    struct LargeAlignment;

    let mut p1 = TaggedPointer::<LeafNode<LargeAlignment, _>, 3>::new(Box::into_raw(Box::new(
        LeafNode::new(LargeAlignment, 2u16),
    )))
    .unwrap()
    .cast::<OpaqueValue>();
    p1.set_data(0b011);

    let mut p2 = TaggedPointer::<LeafNode<_, LargeAlignment>, 3>::new(Box::into_raw(Box::new(
        LeafNode::new(1u64, LargeAlignment),
    )))
    .unwrap()
    .cast::<OpaqueValue>();
    p2.set_data(0b111);

    unsafe {
        // These tests apparently leak memory in Miri's POV unless we explicitly cast
        // them back to the original type when we deallocate. The `.cast` calls
        // are required, even though the tests pass under normal execution otherwise (I
        // guess normal test execution doesn't care about leaked memory?)
        drop(Box::from_raw(p0.cast::<LeafNode<[u8; 0], u8>>().to_ptr()));
        drop(Box::from_raw(
            p1.cast::<LeafNode<LargeAlignment, u16>>().to_ptr(),
        ));
        drop(Box::from_raw(
            p2.cast::<LeafNode<u64, LargeAlignment>>().to_ptr(),
        ));
    }
}

#[test]
fn opaque_node_ptr_is_correct() {
    let mut n4 = InnerNode4::<Box<[u8]>, usize>::empty();
    let mut n16 = InnerNode16::<Box<[u8]>, usize>::empty();
    let mut n48 = InnerNode48::<Box<[u8]>, usize>::empty();
    let mut n256 = InnerNode256::<Box<[u8]>, usize>::empty();

    let n4_ptr = NodePtr::from(&mut n4).to_opaque();
    let n16_ptr = NodePtr::from(&mut n16).to_opaque();
    let n48_ptr = NodePtr::from(&mut n48).to_opaque();
    let n256_ptr = NodePtr::from(&mut n256).to_opaque();

    assert!(n4_ptr.is::<InnerNode4<Box<[u8]>, usize>>());
    assert!(n16_ptr.is::<InnerNode16<Box<[u8]>, usize>>());
    assert!(n48_ptr.is::<InnerNode48<Box<[u8]>, usize>>());
    assert!(n256_ptr.is::<InnerNode256<Box<[u8]>, usize>>());
}

#[test]
#[cfg(target_pointer_width = "64")]
// fn node_sizes() {
//     const EXPECTED_HEADER_SIZE: usize = 40;

//     assert_eq!(mem::size_of::<Header>(), EXPECTED_HEADER_SIZE);
//     // key map: 4 * (1 byte) = 4 bytes
//     // child map: 4 * (8 bytes (on 64-bit platform)) = 32
//     //
//     // 4 bytes of padding are inserted after the `keys` field to align the field to
//     // an 8 byte boundary.
//     assert_eq!(
//         mem::size_of::<InnerNode4<Box<[u8]>, usize>>(),
//         EXPECTED_HEADER_SIZE + 40
//     );
//     // key map: 16 * (1 byte) = 16 bytes
//     // child map: 16 * (8 bytes (on 64-bit platform)) = 128
//     assert_eq!(
//         mem::size_of::<InnerNode16<Box<[u8]>, usize>>(),
//         EXPECTED_HEADER_SIZE + 144
//     );
//     // key map: 256 * (1 byte) = 256 bytes
//     // child map: 48 * (8 bytes (on 64-bit platform)) = 384
//     assert_eq!(
//         mem::size_of::<InnerNode48<Box<[u8]>, usize>>(),
//         EXPECTED_HEADER_SIZE + 640
//     );
//     // child & key map: 256 * (8 bytes (on 64-bit platform)) = 2048
//     assert_eq!(
//         mem::size_of::<InnerNode256<Box<[u8]>, usize>>(),
//         EXPECTED_HEADER_SIZE + 2048
//     );

//     // Assert that pointer is expected size and has non-null optimization
//     assert_eq!(mem::size_of::<Option<OpaqueNodePtr<Box<[u8]>, ()>>>(), 8);
//     assert_eq!(mem::size_of::<OpaqueNodePtr<Box<[u8]>, ()>>(), 8);
// }
#[test]
fn node_alignment() {
    assert_eq!(mem::align_of::<InnerNode4<Box<[u8]>, u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode16<Box<[u8]>, u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode48<Box<[u8]>, u8>>(), 8);
    assert_eq!(mem::align_of::<InnerNode256<Box<[u8]>, u8>>(), 8);
    assert_eq!(mem::align_of::<LeafNode<Box<[u8]>, u8>>(), 8);
    assert_eq!(mem::align_of::<Header>(), 8);

    assert_eq!(
        mem::align_of::<InnerNode4<Box<[u8]>, u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode16<Box<[u8]>, u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode48<Box<[u8]>, u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<InnerNode256<Box<[u8]>, u8>>(),
        mem::align_of::<OpaqueValue>()
    );
    assert_eq!(
        mem::align_of::<LeafNode<Box<[u8]>, u8>>(),
        mem::align_of::<OpaqueValue>()
    );

    let n4 = InnerNode4::<Box<[u8]>, ()>::empty();
    let n16 = InnerNode4::<Box<[u8]>, ()>::empty();
    let n48 = InnerNode4::<Box<[u8]>, ()>::empty();
    let n256 = InnerNode4::<Box<[u8]>, ()>::empty();

    let n4_ptr = (&n4 as *const InnerNode4<Box<[u8]>, ()>).addr();
    let n16_ptr = (&n16 as *const InnerNode4<Box<[u8]>, ()>).addr();
    let n48_ptr = (&n48 as *const InnerNode4<Box<[u8]>, ()>).addr();
    let n256_ptr = (&n256 as *const InnerNode4<Box<[u8]>, ()>).addr();

    // Ensure that there are 3 bits of unused space in the node pointer because of
    // the alignment.
    assert!(n4_ptr.trailing_zeros() >= 3);
    assert!(n16_ptr.trailing_zeros() >= 3);
    assert!(n48_ptr.trailing_zeros() >= 3);
    assert!(n256_ptr.trailing_zeros() >= 3);
}

fn inner_node_write_child_test(
    mut node: impl InnerNode<Key = Box<[u8]>, Value = ()>,
    num_children: usize,
) {
    let mut leaves = vec![LeafNode::new(vec![].into(), ()); num_children];

    assert!(!node.is_full());
    {
        let leaf_pointers = leaves
            .iter_mut()
            .map(|leaf| NodePtr::from(leaf).to_opaque())
            .collect::<Vec<_>>();

        for (idx, leaf_pointer) in leaf_pointers.iter().copied().enumerate() {
            println!("{idx}");
            node.write_child(u8::try_from(idx).unwrap(), leaf_pointer);
        }

        for (idx, leaf_pointer) in leaf_pointers.into_iter().enumerate() {
            assert_eq!(
                node.lookup_child(u8::try_from(idx).unwrap()),
                Some(leaf_pointer)
            );
        }
    }
    // println!("{}")
    assert!(node.is_full());
}

fn inner_node_remove_child_test(
    mut node: impl InnerNode<Key = Box<[u8]>, Value = ()>,
    num_children: usize,
) {
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

fn inner_node_shrink_test(
    mut node: impl InnerNode<Key = Box<[u8]>, Value = ()>,
    num_children: usize,
) {
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

#[test]
fn node4_lookup() {
    let mut n = InnerNode4::<Box<[u8]>, ()>::empty();
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

// #[test]
// #[should_panic]
// fn node4_write_child_full_panic() {
//     inner_node_write_child_test(InnerNode4::empty(), 5);
// }

#[test]
fn node4_grow() {
    let mut n4 = InnerNode4::<Box<[u8]>, ()>::empty();
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
    let n4 = InnerNode4::<Box<[u8]>, ()>::empty();

    n4.shrink();
}

#[test]
fn node16_lookup() {
    let mut n = InnerNode16::<Box<[u8]>, ()>::empty();
    let mut l1 = LeafNode::new(Box::from([]), ());
    let mut l2 = LeafNode::new(Box::from([]), ());
    let mut l3 = LeafNode::new(Box::from([]), ());
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

// #[test]
// #[should_panic]
// fn node16_write_child_full_panic() {
//     inner_node_write_child_test(InnerNode16::empty(), 17);
// }

#[test]
#[should_panic]
fn node16_grow_panic() {
    let mut n16 = InnerNode16::<Box<[u8]>, ()>::empty();
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
fn node16_grow() {
    let mut n16 = InnerNode16::<Box<[u8]>, ()>::empty();
    let mut v = Vec::new();
    for i in 0..16 {
        let mut l = LeafNode::new(vec![].into(), ());
        let l_ptr = NodePtr::from(&mut l).to_opaque();
        v.push(l_ptr);
        n16.write_child(i * 2, l_ptr);
    }

    let n48 = n16.grow();

    for i in 0..16 {
        assert_eq!(n48.lookup_child(i * 2), Some(v[i as usize]));
    }
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
fn node48_lookup() {
    let mut n = InnerNode48::<Box<[u8]>, ()>::empty();
    let mut l1 = LeafNode::new(Box::from([]), ());
    let mut l2 = LeafNode::new(Box::from([]), ());
    let mut l3 = LeafNode::new(Box::from([]), ());
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
    let mut n48 = InnerNode48::<Box<[u8]>, ()>::empty();
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
fn node256_lookup() {
    let mut n = InnerNode256::<Box<[u8]>, ()>::empty();
    let mut l1 = LeafNode::new(Box::from([]), ());
    let mut l2 = LeafNode::new(Box::from([]), ());
    let mut l3 = LeafNode::new(Box::from([]), ());
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
    let n = InnerNode256::<Box<[u8]>, ()>::empty();

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

// #[test]
// fn empty_prefix_bytes_match() {
//     let mut h = Header::empty();

//     h.extend_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
//     h.ltrim_prefix(NUM_PREFIX_BYTES);
//     // 6 bytes are represented

//     assert_eq!(h.match_prefix(&[1, 2, 3]), 0);
//     assert_eq!(h.match_prefix(&[0]), 0);
//     assert_eq!(h.match_prefix(&[]), 0);
//     assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6]), 0);
//     assert_eq!(h.match_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), 0);

//     assert_eq!(h.match_prefix(&[9, 10, 11, 12]), 4);
//     assert_eq!(h.match_prefix(&[9, 10, 11, 12, 13, 14]), 6);
// }

#[test]
fn header_delete_prefix() {
    let mut h = Header::new(&[1, 2, 3, 4, 5, 6, 7, 8], 8);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 8);

    h.ltrim_by(0);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 8);

    h.ltrim_by(3);
    assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 5);

    h.ltrim_by(1);
    assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 4);

    h.ltrim_by(4);
    assert_eq!(h.read_prefix(), &[]);
    assert_eq!(h.prefix_len(), 0);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_too_many_bytes_panic() {
    let mut h = Header::new(&[1, 2, 3, 4, 5, 6, 7, 8], 8);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 8);

    h.ltrim_by(10);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_non_stored_bytes_panic() {
    let mut h = Header::new(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], 14);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_len(), 8);

    h.ltrim_by(0);
}

#[test]
fn simd_match_prefix() {
    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5, 6], 6);
    let match_prefix = node.match_prefix(&[1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 5, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => assert_eq!(matched_bytes, 5),
        MatchPrefix::Match { matched_bytes } => panic!("should be a mismatch"),
    };

    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5, 6], 6);
    let match_prefix = node.match_prefix(&[1, 2, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => panic!("should be a match"),
        MatchPrefix::Match { matched_bytes } => assert_eq!(matched_bytes, 6),
    };

    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5], 5);
    let match_prefix = node.match_prefix(&[1, 2, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 6, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => panic!("should be a match"),
        MatchPrefix::Match { matched_bytes } => assert_eq!(matched_bytes, 5),
    };

    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5], 5);
    let match_prefix = node.match_prefix(&[0, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 5, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => assert_eq!(matched_bytes, 0),
        MatchPrefix::Match { matched_bytes } => panic!("should be a mismatch"),
    };

    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5], 5);
    let match_prefix = node.match_prefix(&[1, 2, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 5, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => assert_eq!(matched_bytes, 2),
        MatchPrefix::Match { matched_bytes } => panic!("should be a mismatch"),
    };

    let node = InnerNode4::<CString, usize>::from_prefix(&[1, 2, 3, 4, 5], 5);
    let match_prefix = node.match_prefix(&[1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 5, 0);
    match match_prefix {
        MatchPrefix::Mismatch {  mismatch: Mismatch { matched_bytes, .. } } => assert_eq!(matched_bytes, 4),
        MatchPrefix::Match { matched_bytes } => panic!("should be a mismatch"),
    };
}
