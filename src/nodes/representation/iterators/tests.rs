use super::*;

fn node4_fixture() -> (InnerNode4<()>, [LeafNode<()>; 4], [OpaqueNodePtr<()>; 4]) {
    let mut n4 = InnerNode4::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let mut l4 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();
    let l4_ptr = NodePtr::from(&mut l4).to_opaque();

    n4.write_child(3, l1_ptr);
    n4.write_child(255, l2_ptr);
    n4.write_child(0u8, l3_ptr);
    n4.write_child(85, l4_ptr);

    (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
}

#[test]
fn node4_iterate() {
    let (n4, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node4_fixture();

    let pairs = unsafe { InnerNodeCompressedIter::new(&n4) };
    assert_eq!(
        [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)]
            .into_iter()
            .collect::<Vec<(u8, _)>>(),
        pairs.into_iter().collect::<Vec<_>>(),
        "expected values did not match for range [{:?}]",
        ..
    );
}

fn node16_fixture() -> (InnerNode16<()>, [LeafNode<()>; 4], [OpaqueNodePtr<()>; 4]) {
    let mut n4 = InnerNode16::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let mut l4 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();
    let l4_ptr = NodePtr::from(&mut l4).to_opaque();

    n4.write_child(3, l1_ptr);
    n4.write_child(255, l2_ptr);
    n4.write_child(0u8, l3_ptr);
    n4.write_child(85, l4_ptr);

    (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
}

#[test]
fn node16_iterate() {
    let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node16_fixture();

    let pairs = unsafe { InnerNodeCompressedIter::new(&node).collect::<Vec<_>>() };
    assert_eq!(
        pairs,
        &[(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr),]
    )
}

fn node48_fixture() -> (InnerNode48<()>, [LeafNode<()>; 4], [OpaqueNodePtr<()>; 4]) {
    let mut n4 = InnerNode48::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let mut l4 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();
    let l4_ptr = NodePtr::from(&mut l4).to_opaque();

    n4.write_child(3, l1_ptr);
    n4.write_child(255, l2_ptr);
    n4.write_child(0u8, l3_ptr);
    n4.write_child(85, l4_ptr);

    (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
}

#[test]
fn node48_iterate() {
    let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node48_fixture();

    let pairs = unsafe { InnerNode48Iter::new(&node).collect::<Vec<_>>() };
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 255 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 0u8 && *ptr == l3_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 85 && *ptr == l4_ptr)
        .is_some());
}

fn node256_fixture() -> (InnerNode256<()>, [LeafNode<()>; 4], [OpaqueNodePtr<()>; 4]) {
    let mut n4 = InnerNode256::empty();
    let mut l1 = LeafNode::new(vec![].into(), ());
    let mut l2 = LeafNode::new(vec![].into(), ());
    let mut l3 = LeafNode::new(vec![].into(), ());
    let mut l4 = LeafNode::new(vec![].into(), ());
    let l1_ptr = NodePtr::from(&mut l1).to_opaque();
    let l2_ptr = NodePtr::from(&mut l2).to_opaque();
    let l3_ptr = NodePtr::from(&mut l3).to_opaque();
    let l4_ptr = NodePtr::from(&mut l4).to_opaque();

    n4.write_child(3, l1_ptr);
    n4.write_child(255, l2_ptr);
    n4.write_child(0u8, l3_ptr);
    n4.write_child(85, l4_ptr);

    (n4, [l1, l2, l3, l4], [l1_ptr, l2_ptr, l3_ptr, l4_ptr])
}

#[test]
fn node256_iterate() {
    let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = node256_fixture();

    let pairs = unsafe { InnerNode256Iter::new(&node).collect::<Vec<_>>() };
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 3 && *ptr == l1_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 255 && *ptr == l2_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 0u8 && *ptr == l3_ptr)
        .is_some());
    assert!(pairs
        .iter()
        .find(|(key_fragment, ptr)| *key_fragment == 85 && *ptr == l4_ptr)
        .is_some());
}

macro_rules! node_range_test_cases {
    ($fixture:ident; $iterator:ty) => {
        let (node, _, [l1_ptr, l2_ptr, l3_ptr, l4_ptr]) = $fixture();

        node_range_test_cases!(($iterator, node) =>
            {
                ..;
                [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)]
            },
            {
                4..;
                [(85, l4_ptr), (255, l2_ptr)]
            },
            {
                4..86;
                [(85, l4_ptr)]
            },
            {
                ..=85;
                [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr)]
            },
            {
                49..60;
                []
            },
            {
                ..0;
                []
            },
            {
                0..0;
                []
            },
            {
                0..=0;
                [(0u8, l3_ptr)]
            },
            {
                255..=0;
                []
            },
            {
                255..;
                [(255u8, l2_ptr)]
            },
            {
                (Bound::Included(&0u8), Bound::Included(&255));
                [(0u8, l3_ptr), (3, l1_ptr), (85, l4_ptr), (255, l2_ptr)]
            },
            {
                (Bound::Included(&3), Bound::Included(&4));
                [(3, l1_ptr)]
            },
            {
                (Bound::Excluded(&0u8), Bound::Excluded(&255));
                [(3, l1_ptr), (85, l4_ptr)]
            },
            {
                (Bound::Excluded(&0u8), Bound::Included(&255));
                [(3, l1_ptr), (85, l4_ptr), (255, l2_ptr)]
            },
            {
                (Bound::Excluded(&255), Bound::<&u8>::Unbounded);
                []
            },
            {
                (Bound::Excluded(&255), Bound::Included(&255));
                []
            },
        );
    };
    (($iterator:ty, $node:expr) => $({$range:expr ; $expected:expr}),*$(,)?) => {
        $(
            assert_eq!(
                $expected.into_iter().collect::<Vec<(u8, _)>>(),
                unsafe { <$iterator>::range(&$node, $range) }.into_iter().collect::<Vec<_>>(),
                "expected values did not match for range [{:?}]", $range
            );
        )*
    };
}

#[test]
fn node4_iter_ranges() {
    node_range_test_cases!(node4_fixture; InnerNodeCompressedIter<()>);
}

#[test]
fn node16_iter_ranges() {
    node_range_test_cases!(node16_fixture; InnerNodeCompressedIter<()>);
}

#[test]
fn node48_iter_ranges() {
    node_range_test_cases!(node48_fixture; InnerNode48Iter<()>);
}

#[test]
fn node256_iter_ranges() {
    node_range_test_cases!(node256_fixture; InnerNode256Iter<()>);
}
