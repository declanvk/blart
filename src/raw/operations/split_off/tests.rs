use alloc::{alloc::Global, boxed::Box, vec::Vec};

use super::*;
use crate::{
    raw::{NodeType, deallocate_tree, search_unchecked},
    testing::{
        PrefixExpansion, generate_key_fixed_length, generate_key_with_prefix, generate_keys_skewed,
        setup_tree_from_entries,
    },
    visitor::WellFormedChecker,
};

type Key = Box<[u8]>;

#[derive(Debug, PartialEq, Eq)]
enum SplitShape {
    OnlyLessThan,
    OnlyGreaterThanOrEqual,
    Normal { left: NodeType, right: NodeType },
}

fn keys(raw: &[&[u8]]) -> Vec<Key> {
    raw.iter().map(|key| Box::<[u8]>::from(*key)).collect()
}

/// Collect the keys of the tree by walking the leaf linked list from the minimum leaf.
///
/// # Safety
///  - The tree must not be mutated for the duration of this function.
unsafe fn collect_keys<const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<Key, usize, PREFIX_LEN>,
) -> Vec<Key> {
    let mut keys = Vec::new();
    // SAFETY: Covered by the safety requirements of this function
    let mut current = Some(unsafe { minimum_unchecked(root) });
    while let Some(leaf_ptr) = current {
        // SAFETY: Covered by the safety requirements of this function
        let leaf = unsafe { leaf_ptr.as_ref() };
        keys.push(leaf.key_ref().clone());
        current = leaf.next;
    }
    keys
}

/// Check that the tree is well-formed (including the leaf linked list being properly terminated)
/// and contains exactly the `expected` keys, all of which can be found by searching.
///
/// # Safety
///  - The tree must not be mutated for the duration of this function.
#[track_caller]
unsafe fn check_side<const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<Key, usize, PREFIX_LEN>,
    expected: &[Key],
) {
    // SAFETY: Covered by the safety requirements of this function
    let stats = unsafe { WellFormedChecker::check_tree(root) }.expect("tree should be well-formed");
    assert_eq!(stats.num_leaf, expected.len());

    // SAFETY: Covered by the safety requirements of this function
    assert_eq!(unsafe { collect_keys(root) }, expected);

    for key in expected {
        // SAFETY: Covered by the safety requirements of this function
        let leaf = unsafe { search_unchecked(root, key) };
        assert!(leaf.is_some(), "key {key:?} should be found by search");
    }
}

/// Build a tree from `keys`, split it at `split_key`, check that both halves are well-formed and
/// contain the expected keys, then deallocate everything.
///
/// `inspect` is called with the raw result before any checks or deallocation.
#[track_caller]
fn check_split_off_with<const PREFIX_LEN: usize>(
    keys: &[Key],
    split_key: &[u8],
    inspect: impl FnOnce(&SplitOffResult<Key, usize, PREFIX_LEN>),
) -> SplitShape {
    let mut sorted = keys.to_vec();
    sorted.sort();
    let (expected_left, expected_right): (Vec<_>, Vec<_>) =
        sorted.into_iter().partition(|key| key.as_ref() < split_key);

    let root: OpaqueNodePtr<Key, usize, PREFIX_LEN> =
        setup_tree_from_entries(keys.iter().cloned().zip(0..));

    // SAFETY: The tree was just created, so there are no other references to it
    let result = unsafe { split_off_unchecked(root, split_key, &Global) };

    inspect(&result);

    // SAFETY: Each half is a separate tree that is only accessed here, and is deallocated at the
    // end
    unsafe {
        match result {
            SplitOffResult::NormalSplit {
                less_than_root,
                less_than_root_max_leaf,
                greater_than_or_equal_root,
                greater_than_or_equal_min_leaf,
            } => {
                check_side(less_than_root, &expected_left);
                check_side(greater_than_or_equal_root, &expected_right);

                assert_eq!(less_than_root_max_leaf, maximum_unchecked(less_than_root));
                assert_eq!(
                    greater_than_or_equal_min_leaf,
                    minimum_unchecked(greater_than_or_equal_root)
                );

                let shape = SplitShape::Normal {
                    left: less_than_root.node_type(),
                    right: greater_than_or_equal_root.node_type(),
                };

                deallocate_tree(less_than_root, &Global);
                deallocate_tree(greater_than_or_equal_root, &Global);

                shape
            },
            SplitOffResult::OnlyLessThan { less_than_root } => {
                assert!(
                    expected_right.is_empty(),
                    "expected keys {expected_right:?} on the right"
                );
                assert_eq!(
                    less_than_root, root,
                    "original tree should be returned as-is"
                );
                check_side(less_than_root, &expected_left);

                deallocate_tree(less_than_root, &Global);

                SplitShape::OnlyLessThan
            },
            SplitOffResult::OnlyGreaterThanOrEqual {
                greater_than_or_equal_root,
            } => {
                assert!(
                    expected_left.is_empty(),
                    "expected keys {expected_left:?} on the left"
                );
                assert_eq!(
                    greater_than_or_equal_root, root,
                    "original tree should be returned as-is"
                );
                check_side(greater_than_or_equal_root, &expected_right);

                deallocate_tree(greater_than_or_equal_root, &Global);

                SplitShape::OnlyGreaterThanOrEqual
            },
        }
    }
}

#[track_caller]
fn check_split_off<const PREFIX_LEN: usize>(keys: &[Key], split_key: &[u8]) -> SplitShape {
    check_split_off_with::<PREFIX_LEN>(keys, split_key, |_| {})
}

/// Read the prefix length and stored prefix bytes of the left root of a normal split.
fn left_root_prefix<const PREFIX_LEN: usize>(
    result: &SplitOffResult<Key, usize, PREFIX_LEN>,
) -> (usize, Vec<u8>) {
    let SplitOffResult::NormalSplit { less_than_root, .. } = result else {
        panic!("expected a normal split, got {result:?}");
    };
    assert_ne!(less_than_root.node_type(), NodeType::Leaf);

    // SAFETY: The root is an inner node, and is not mutated while the header reference is live
    let header = unsafe { less_than_root.header_ref_unchecked() };
    (header.prefix_len(), header.read_prefix().to_vec())
}

/// Split the tree at every interesting point: each key, each prefix of a key, and keys just
/// before and after each key.
#[track_caller]
fn check_split_off_everywhere<const PREFIX_LEN: usize>(keys: &[Key]) {
    let mut split_keys: Vec<Vec<u8>> = vec![vec![], vec![0], vec![255]];
    for key in keys {
        for len in 0..=key.len() {
            split_keys.push(key[..len].to_vec());
        }

        let mut extended = key.to_vec();
        extended.push(0);
        split_keys.push(extended);

        if let Some((&last, init)) = key.split_last() {
            if let Some(after) = last.checked_add(1) {
                split_keys.push([init, &[after]].concat());
            }
            if let Some(before) = last.checked_sub(1) {
                split_keys.push([init, &[before]].concat());
            }
        }
    }
    split_keys.sort();
    split_keys.dedup();

    for split_key in split_keys {
        let _ = check_split_off::<PREFIX_LEN>(keys, &split_key);
    }
}

#[test]
fn split_off_singleton_tree() {
    let keys = keys(&[&[1, 2, 3]]);

    assert_eq!(
        check_split_off::<16>(&keys, &[0]),
        SplitShape::OnlyGreaterThanOrEqual
    );
    // The split key is included in the right side
    assert_eq!(
        check_split_off::<16>(&keys, &[1, 2, 3]),
        SplitShape::OnlyGreaterThanOrEqual
    );
    assert_eq!(
        check_split_off::<16>(&keys, &[1, 2, 3, 0]),
        SplitShape::OnlyLessThan
    );
    assert_eq!(check_split_off::<16>(&keys, &[5]), SplitShape::OnlyLessThan);
}

#[test]
fn split_off_node4_at_existing_key() {
    let keys = keys(&[&[1], &[2], &[3], &[4]]);

    assert_eq!(
        check_split_off::<16>(&keys, &[3]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node4
        }
    );
    // Left side collapses to a single leaf
    assert_eq!(
        check_split_off::<16>(&keys, &[2]),
        SplitShape::Normal {
            left: NodeType::Leaf,
            right: NodeType::Node4
        }
    );
    // Right side collapses to a single leaf
    assert_eq!(
        check_split_off::<16>(&keys, &[4]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Leaf
        }
    );
}

#[test]
fn split_off_leaf_less_than_split_key() {
    let keys = keys(&[&[1], &[2], &[3], &[4]]);

    // The search ends at leaf `[2]`, which is less than the split key
    assert_eq!(
        check_split_off::<16>(&keys, &[2, 5]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node4
        }
    );
    // The search ends at leaf `[4]`, which is less than the split key, and nothing is greater
    assert_eq!(
        check_split_off::<16>(&keys, &[4, 0]),
        SplitShape::OnlyLessThan
    );
}

#[test]
fn split_off_missing_child() {
    let keys = keys(&[&[1], &[3], &[5], &[7]]);

    assert_eq!(
        check_split_off::<16>(&keys, &[4]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node4
        }
    );
    assert_eq!(
        check_split_off::<16>(&keys, &[0]),
        SplitShape::OnlyGreaterThanOrEqual
    );
    assert_eq!(check_split_off::<16>(&keys, &[8]), SplitShape::OnlyLessThan);
}

#[test]
fn split_off_node16() {
    let keys: Vec<Key> = (0..16u8).map(|byte| Box::from([byte])).collect();

    // Both halves fit in a Node16, the original node is reused for one of them
    assert_eq!(
        check_split_off::<16>(&keys, &[8]),
        SplitShape::Normal {
            left: NodeType::Node16,
            right: NodeType::Node16
        }
    );
    // The left half is small enough to shrink to a Node4
    assert_eq!(
        check_split_off::<16>(&keys, &[3]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node16
        }
    );
}

#[test]
fn split_off_node48() {
    let keys: Vec<Key> = (0..17u8).map(|byte| Box::from([byte])).collect();

    // Neither half fits in a Node48, so the original node is deallocated
    assert_eq!(
        check_split_off::<16>(&keys, &[8]),
        SplitShape::Normal {
            left: NodeType::Node16,
            right: NodeType::Node16
        }
    );

    let keys: Vec<Key> = (0..48u8).map(|byte| Box::from([byte])).collect();

    assert_eq!(
        check_split_off::<16>(&keys, &[20]),
        SplitShape::Normal {
            left: NodeType::Node48,
            right: NodeType::Node48
        }
    );
}

#[test]
fn split_off_node256() {
    let keys: Vec<Key> = (0..49u8).map(|byte| Box::from([byte])).collect();

    assert_eq!(
        check_split_off::<16>(&keys, &[24]),
        SplitShape::Normal {
            left: NodeType::Node48,
            right: NodeType::Node48
        }
    );

    let keys: Vec<Key> = (0..=255u8).map(|byte| Box::from([byte])).collect();

    assert_eq!(
        check_split_off::<16>(&keys, &[100]),
        SplitShape::Normal {
            left: NodeType::Node256,
            right: NodeType::Node256
        }
    );
}

#[test]
fn split_off_boundary_key_bytes() {
    let keys: Vec<Key> = (0..=255u8).map(|byte| Box::from([byte])).collect();

    // There are no siblings after byte 255
    assert_eq!(
        check_split_off::<16>(&keys, &[255]),
        SplitShape::Normal {
            left: NodeType::Node256,
            right: NodeType::Leaf
        }
    );
    assert_eq!(
        check_split_off::<16>(&keys, &[255, 0]),
        SplitShape::OnlyLessThan
    );
    // There are no siblings before byte 0
    assert_eq!(
        check_split_off::<16>(&keys, &[0]),
        SplitShape::OnlyGreaterThanOrEqual
    );
    assert_eq!(
        check_split_off::<16>(&keys, &[0, 0]),
        SplitShape::Normal {
            left: NodeType::Leaf,
            right: NodeType::Node256
        }
    );
}

#[test]
fn split_off_prefix_mismatch() {
    // `[1, 5, 5, 1]` and `[1, 5, 5, 2]` are under an inner node with the prefix `[5, 5]`
    let keys = keys(&[&[0, 0, 0, 0], &[1, 5, 5, 1], &[1, 5, 5, 2], &[2, 0, 0, 0]]);

    // Node prefix is greater than the split key, the whole node goes right
    assert_eq!(
        check_split_off::<16>(&keys, &[1, 4]),
        SplitShape::Normal {
            left: NodeType::Leaf,
            right: NodeType::Node4
        }
    );
    // Mismatch partway through the prefix
    assert_eq!(
        check_split_off::<16>(&keys, &[1, 5, 4]),
        SplitShape::Normal {
            left: NodeType::Leaf,
            right: NodeType::Node4
        }
    );
    // Node prefix is less than the split key, the whole node goes left
    assert_eq!(
        check_split_off::<16>(&keys, &[1, 6]),
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Leaf
        }
    );
}

#[test]
fn split_off_key_ends_before_node() {
    // `[1, 5, 5, 1]` and `[1, 5, 5, 2]` are under an inner node with the prefix `[5, 5]`
    let keys = keys(&[&[0, 0, 0, 0], &[1, 5, 5, 1], &[1, 5, 5, 2], &[2, 0, 0, 0]]);

    // The split key runs out of bytes before, inside, and right after the node prefix. In each
    // case the split key is a prefix of every key in the node, so the node goes right.
    for split_key in [&[1][..], &[1, 5], &[1, 5, 5]] {
        assert_eq!(
            check_split_off::<16>(&keys, split_key),
            SplitShape::Normal {
                left: NodeType::Leaf,
                right: NodeType::Node4
            },
            "split key {split_key:?}"
        );
    }
}

#[test]
fn split_off_collapse_into_inner_node() {
    let keys = keys(&[&[1, 1], &[1, 2], &[2, 1], &[2, 2], &[3, 1]]);

    // The root's left side is just the inner node at `[1]`, which collapses into the root
    // position and takes on the key byte `1` as its prefix.
    let shape = check_split_off_with::<16>(&keys, &[2, 0], |result| {
        assert_eq!(left_root_prefix(result), (1, vec![1]));
    });
    assert_eq!(
        shape,
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node4
        }
    );
}

fn check_multi_level_collapse<const PREFIX_LEN: usize>() {
    let keys = keys(&[&[1, 1, 1], &[1, 1, 2], &[1, 2, 0], &[2, 0, 0]]);

    // The inner node at `[1, 1]` collapses through two levels, gaining the prefix `[1, 1]`
    let shape = check_split_off_with::<PREFIX_LEN>(&keys, &[1, 2, 0], |result| {
        let (prefix_len, stored_prefix) = left_root_prefix(result);
        assert_eq!(prefix_len, 2);
        assert_eq!(stored_prefix, [1, 1][..PREFIX_LEN.min(2)]);
    });
    assert_eq!(
        shape,
        SplitShape::Normal {
            left: NodeType::Node4,
            right: NodeType::Node4
        }
    );
}

#[test]
fn split_off_multi_level_collapse() {
    check_multi_level_collapse::<16>();
}

#[test]
fn split_off_multi_level_collapse_prefix_longer_than_capacity() {
    check_multi_level_collapse::<1>();
}

#[test]
fn split_off_multi_level_collapse_implicit_prefix() {
    check_multi_level_collapse::<0>();
}

#[test]
fn split_off_everywhere_small_tree() {
    let keys: Vec<Key> = generate_key_fixed_length([1, 1, 1])
        .map(Box::from)
        .collect();

    check_split_off_everywhere::<16>(&keys);
    check_split_off_everywhere::<0>(&keys);
}

// The trees below are too large to split at every point under Miri in a reasonable time
#[cfg(not(miri))]
mod everywhere {
    use super::*;

    fn fixed_length_keys() -> Vec<Key> {
        generate_key_fixed_length([3, 3, 3])
            .map(Box::from)
            .collect()
    }

    fn prefix_keys() -> Vec<Key> {
        generate_key_with_prefix(
            [2, 2, 2],
            [
                PrefixExpansion {
                    base_index: 0,
                    expanded_length: 3,
                },
                PrefixExpansion {
                    base_index: 2,
                    expanded_length: 4,
                },
            ],
        )
        .collect()
    }

    #[test]
    fn split_off_everywhere_fixed_length() {
        let keys = fixed_length_keys();
        check_split_off_everywhere::<16>(&keys);
        check_split_off_everywhere::<1>(&keys);
        check_split_off_everywhere::<0>(&keys);
    }

    #[test]
    fn split_off_everywhere_with_prefixes() {
        let keys = prefix_keys();
        check_split_off_everywhere::<16>(&keys);
        check_split_off_everywhere::<2>(&keys);
        check_split_off_everywhere::<0>(&keys);
    }

    #[test]
    fn split_off_everywhere_skewed() {
        let keys: Vec<Key> = generate_keys_skewed(16).collect();
        check_split_off_everywhere::<16>(&keys);
        check_split_off_everywhere::<4>(&keys);
        check_split_off_everywhere::<0>(&keys);
    }

    #[test]
    fn split_off_everywhere_node256() {
        let keys: Vec<Key> = (0..=255u8).map(|byte| Box::from([byte])).collect();
        check_split_off_everywhere::<16>(&keys);
    }
}
