use std::mem;

use super::*;

#[test]
fn opaque_node_ptr_is_correct() {
    let mut n4 = InnerNode4::<usize>::empty();
    let mut n16 = InnerNode16::<usize>::empty();
    let mut n48 = InnerNode48::<usize>::empty();
    let mut n256 = InnerNode256::<usize>::empty();

    let n4_ptr = NodePtr::from(&mut n4);
    let n16_ptr = NodePtr::from(&mut n16);
    let n48_ptr = NodePtr::from(&mut n48);
    let n256_ptr = NodePtr::from(&mut n256);

    let opaque_n4_ptr = n4_ptr.to_opaque();
    let opaque_n16_ptr = n16_ptr.to_opaque();
    let opaque_n48_ptr = n48_ptr.to_opaque();
    let opaque_n256_ptr = n256_ptr.to_opaque();

    assert!(opaque_n4_ptr.is::<InnerNode4<usize>>());
    assert!(opaque_n16_ptr.is::<InnerNode16<usize>>());
    assert!(opaque_n48_ptr.is::<InnerNode48<usize>>());
    assert!(opaque_n256_ptr.is::<InnerNode256<usize>>());
}

#[test]
#[cfg(target_pointer_width = "64")]
fn node_sizes() {
    let header_size = mem::size_of::<Header>();
    assert_eq!(header_size, 16);
    // key map: 4 * (1 byte) = 4 bytes
    // child map: 4 * (8 bytes (on 64-bit platform)) = 32
    //
    // 4 bytes of padding are inserted after the `keys` field to align the field to
    // an 8 byte boundary.
    assert_eq!(mem::size_of::<InnerNode4<usize>>(), 56);
    // key map: 16 * (1 byte) = 16 bytes
    // child map: 16 * (8 bytes (on 64-bit platform)) = 128
    assert_eq!(mem::size_of::<InnerNode16<usize>>(), 160);
    // key map: 256 * (1 byte) = 256 bytes
    // child map: 48 * (8 bytes (on 64-bit platform)) = 384
    assert_eq!(mem::size_of::<InnerNode48<usize>>(), 656);
    // child & key map: 256 * (8 bytes (on 64-bit platform)) = 2048
    assert_eq!(mem::size_of::<InnerNode256<usize>>(), 2064);
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
    let mut n = InnerNode4::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    assert_eq!(n.lookup_child(3), Some(l1_ptr));
    assert_eq!(n.lookup_child(123), Some(l2_ptr));
    assert_eq!(n.lookup_child(1), Some(l3_ptr));
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
fn node4_iterate() {
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

    let pairs = n4.iter().collect::<Vec<_>>();
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 123 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 1 && *ptr == l3_ptr)
        .is_some());
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
    let mut n = InnerNode16::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    assert_eq!(n.lookup_child(3), Some(l1_ptr));
    assert_eq!(n.lookup_child(123), Some(l2_ptr));
    assert_eq!(n.lookup_child(1), Some(l3_ptr));
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
fn node16_iterate() {
    let mut n = InnerNode16::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    let pairs = n.iter().collect::<Vec<_>>();
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 123 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 1 && *ptr == l3_ptr)
        .is_some());
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

    n.child_indices[1] = 2.try_into().unwrap();
    n.child_indices[3] = 0.try_into().unwrap();
    n.child_indices[123] = 1.try_into().unwrap();

    n.child_pointers[0].write(l1_ptr);
    n.child_pointers[1].write(l2_ptr);
    n.child_pointers[2].write(l3_ptr);

    assert_eq!(n.lookup_child(123), Some(l2_ptr));
}

#[test]
fn node48_write_child() {
    let mut n = InnerNode48::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    assert_eq!(n.lookup_child(3), Some(l1_ptr));
    assert_eq!(n.lookup_child(123), Some(l2_ptr));
    assert_eq!(n.lookup_child(1), Some(l3_ptr));
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
fn node48_iterate() {
    let mut n = InnerNode48::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    let pairs = n.iter().collect::<Vec<_>>();
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 123 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 1 && *ptr == l3_ptr)
        .is_some());
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
    let mut n = InnerNode256::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    assert_eq!(n.lookup_child(3), Some(l1_ptr));
    assert_eq!(n.lookup_child(123), Some(l2_ptr));
    assert_eq!(n.lookup_child(1), Some(l3_ptr));
}

#[test]
fn node256_iterate() {
    let mut n = InnerNode256::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();

    n.write_child(3, l1_ptr);
    n.write_child(123, l2_ptr);
    n.write_child(1, l3_ptr);

    let pairs = n.iter().collect::<Vec<_>>();
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 123 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 1 && *ptr == l3_ptr)
        .is_some());
}

#[test]
fn header_read_write_prefix() {
    let mut h = Header::empty();

    assert_eq!(h.prefix_size, 0);
    assert_eq!(h.read_prefix(), &[]);

    h.write_prefix(&[1, 2, 3]);

    assert_eq!(h.prefix_size, 3);
    assert_eq!(h.read_prefix(), &[1, 2, 3]);

    h.write_prefix(&[4, 5, 6]);

    assert_eq!(h.prefix_size, 6);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6]);

    h.write_prefix(&[7, 8]);

    assert_eq!(h.prefix_size, 8);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

    h.write_prefix(&[9, 10, 11, 12]);

    assert_eq!(h.prefix_size, 12);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);

    h.write_prefix(&[]);

    assert_eq!(h.prefix_size, 12);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
}

#[test]
fn header_check_prefix() {
    let mut h = Header::empty();

    h.write_prefix(&[1, 2, 3]);

    assert_eq!(h.match_prefix(&[1, 2, 3]), 3);
    assert_eq!(h.match_prefix(&[0, 1, 2]), 0);
    assert_eq!(h.match_prefix(&[1, 2]), 2);
    assert_eq!(h.match_prefix(&[]), 0);

    h.write_prefix(&[4, 5, 6, 7, 8, 9, 10, 11, 12]);

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
        12
    );
}

#[test]
fn header_delete_prefix() {
    let mut h = Header::empty();
    h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 8);

    h.ltrim_prefix(0);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 8);

    h.ltrim_prefix(3);
    assert_eq!(h.read_prefix(), &[4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 5);

    h.ltrim_prefix(1);
    assert_eq!(h.read_prefix(), &[5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 4);

    h.ltrim_prefix(4);
    assert_eq!(h.read_prefix(), &[]);
    assert_eq!(h.prefix_size, 0);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_too_many_bytes_panic() {
    let mut h = Header::empty();
    h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 8);

    h.ltrim_prefix(10);
}

#[test]
#[should_panic]
fn header_ltrim_prefix_non_stored_bytes_panic() {
    let mut h = Header::empty();
    h.write_prefix(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
    assert_eq!(h.read_prefix(), &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(h.prefix_size, 8);

    h.ltrim_prefix(0);
}

#[test]
fn header_is_full() {
    let mut n = InnerNode4::empty();

    assert!(!n.header.is_full());

    let mut l1 = LeafNode::new(Box::new([]), ());
    let mut l2 = LeafNode::new(Box::new([]), ());
    let mut l3 = LeafNode::new(Box::new([]), ());
    let mut l4 = LeafNode::new(Box::new([]), ());

    {
        let l1_ptr = NodePtr::from(&mut l1).to_opaque();
        let l2_ptr = NodePtr::from(&mut l2).to_opaque();
        let l3_ptr = NodePtr::from(&mut l3).to_opaque();
        let l4_ptr = NodePtr::from(&mut l4).to_opaque();

        n.write_child(0, l1_ptr);
        n.write_child(1, l2_ptr);
        n.write_child(2, l3_ptr);

        assert!(!n.header.is_full());

        n.write_child(3, l4_ptr);

        assert!(n.header.is_full());
    }
}
