use std::iter;

use super::*;

#[test]
fn leaf_tree_min_max_same() {
    let root = NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()))
        .to_opaque();

    let min_leaf = unsafe { minimum_unchecked(root) };
    let max_leaf = unsafe { maximum_unchecked(root) };

    assert_eq!(min_leaf, max_leaf);

    unsafe { deallocate_tree(root) }
}

#[test]
fn large_tree_same_length_keys_min_max() {
    const LEN: usize = 3;
    const STOPS: u8 = 5;
    let mut keys = iter::successors(Some(vec![u8::MIN; LEN].into_boxed_slice()), move |prev| {
        if prev.iter().all(|digit| *digit == u8::MAX) {
            None
        } else {
            Some(
                prev.iter()
                    .map(|digit| digit.saturating_add(u8::MAX / STOPS))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            )
        }
    });
    let mut root = NodePtr::allocate_node(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        root = unsafe { insert_unchecked(root, key, idx + 1).unwrap() };
    }

    let min_leaf = unsafe { minimum_unchecked(root).unwrap() };
    let max_leaf = unsafe { maximum_unchecked(root).unwrap() };

    assert_ne!(min_leaf, max_leaf);
    let min_leaf = min_leaf.read();
    let max_leaf = max_leaf.read();
    assert!(min_leaf.key < max_leaf.key);
    assert_eq!(min_leaf.key.as_ref(), &[u8::MIN, u8::MIN, u8::MIN]);
    assert_eq!(max_leaf.key.as_ref(), &[u8::MAX, u8::MAX, u8::MAX]);

    unsafe { deallocate_tree(root) }
}

#[test]
fn skewed_tree_min_max() {
    const MAX_LEN: usize = 12;
    let mut keys = iter::successors(Some(vec![u8::MAX; 1].into_boxed_slice()), |prev| {
        if prev.len() < MAX_LEN {
            let mut key = vec![u8::MIN; prev.len()];
            key.push(u8::MAX);
            Some(key.into_boxed_slice())
        } else {
            None
        }
    });

    let mut root = NodePtr::allocate_node(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

    for (idx, key) in keys.enumerate() {
        root = unsafe { insert_unchecked(root, key, idx + 1).unwrap() };
    }

    let min_leaf = unsafe { minimum_unchecked(root).unwrap() };
    let max_leaf = unsafe { maximum_unchecked(root).unwrap() };

    assert_ne!(min_leaf, max_leaf);
    let min_leaf = min_leaf.read();
    let max_leaf = max_leaf.read();
    assert!(min_leaf.key < max_leaf.key);
    assert_eq!(
        min_leaf.key.as_ref(),
        &[
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MIN,
            u8::MAX
        ]
    );
    assert_eq!(max_leaf.key.as_ref(), &[u8::MAX]);

    unsafe { deallocate_tree(root) }
}
