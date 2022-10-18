use super::*;
use std::ops::Bound;

fn create_range() -> (Bound<u8>, Bound<u8>) {
    let bound_type: u8 = kani::any();
    // 0 - include include
    // 1 - include exclude
    // 2 - include unbounded
    // 3 - exclude include
    // 4 - exclude exclude
    // 5 - exclude unbounded
    // 6 - unbounded include
    // 7 - unbounded exclude
    // 8 - unbounded unbounded

    kani::assume(bound_type <= 8);

    let start_bound = match bound_type {
        0 | 1 | 2 => Bound::Included(kani::any::<u8>()),
        3 | 4 | 5 => Bound::Excluded(kani::any::<u8>()),
        6 | 7 | 8 => Bound::Unbounded,
        _ => panic!("not supposed to happen"),
    };

    let end_bound = match bound_type {
        0 | 3 | 6 => Bound::Included(kani::any::<u8>()),
        1 | 4 | 7 => Bound::Excluded(kani::any::<u8>()),
        2 | 5 | 8 => Bound::Unbounded,
        _ => panic!("not supposed to happen"),
    };

    (start_bound, end_bound)
}

#[kani::proof]
#[kani::unwind(10)]
fn verify_node4_any_range() {
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

    let range = create_range();

    let pairs = unsafe { InnerNodeCompressedIter::range(&n4, range) };

    pairs.for_each(|(key_byte, _)| {
        assert!(
            range.contains(&key_byte),
            "range [{:?}] does not contain key byte [{}] from iterator!",
            range,
            key_byte
        );
    });
}
