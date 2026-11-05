//! Bulk load a trie from a pre-sorted iterator of keys and values

use alloc::vec::{Drain, Vec};
use core::{
    iter::{self, Peekable},
    ops::Range,
};

use crate::{
    allocator::Allocator,
    raw::{
        InnerNode, InnerNode16, InnerNode4, InnerNode48, InnerNodeDirect, InsertPrefixError,
        LeafNode, NodePtr, NodeType, OpaqueNodePtr,
    },
    AsBytes,
};

#[derive(Debug)]
pub struct BulkInsertOutput<K, V, const PREFIX_LEN: usize> {
    pub root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    pub min_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    pub max_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    pub num_entries: usize,
}

/// Takes a list of keys and values and constructs a trie from them or returns
/// an error if any of the keys are prefixes.
///
/// If the list contains duplicate keys, only the last entry (in the original
/// order) for each key is kept.
///
/// This function is more efficient than inserting keys one-by-one since it can
/// construct entire sub-trees at a time.
///
/// # Panic
///
/// Panics if the list of items is empty.
pub fn bulk_insert<K, V, const PREFIX_LEN: usize>(
    mut entries: impl AsMut<[(K, V)]> + IntoIterator<Item = (K, V)>,
    alloc: &impl Allocator,
) -> Result<BulkInsertOutput<K, V, PREFIX_LEN>, InsertPrefixError>
where
    K: AsBytes,
{
    assert!(
        !entries.as_mut().is_empty(),
        "list of items for bulk insert must not be empty"
    );

    // Sort the slice of key-value pairs by key. This sort is stable so that entries
    // with duplicate keys stay in their original relative order, which lets the
    // dedup below keep the last one.
    entries
        .as_mut()
        .sort_by(|(a, _), (b, _)| a.as_bytes().cmp(b.as_bytes()));

    // Prefix check
    if let Some(err) = check_key_prefixes(entries.as_mut()) {
        return Err(err);
    }

    // Remove duplicate keys, keeping the last entry for each key.
    let mut entries = entries.into_iter().peekable();
    let entries = iter::from_fn(move || {
        let mut current = entries.next()?;
        while let Some(next) = entries.next_if(|(key, _)| key.as_bytes() == current.0.as_bytes()) {
            current = next;
        }
        Some(current)
    });

    // Build the trie from the iterator of key-value pairs. The entries are sorted,
    // deduplicated, and have no prefixes, so this will not panic unless the
    // `AsBytes` implementation is non-deterministic. The iterator is non-empty
    // because the list was asserted to be non-empty and the dedup always yields at
    // least one entry from a non-empty input.
    Ok(bulk_insert_sorted(entries.peekable(), alloc))
}

/// Return `Some(error)` if any of the keys in the given slice are a prefix of
/// a different key. Duplicate keys are not considered prefixes.
///
/// This function assumes that the given slice is sorted by key bytes.
fn check_key_prefixes<K, V>(entries: &[(K, V)]) -> Option<InsertPrefixError>
where
    K: AsBytes,
{
    debug_assert!(entries.is_sorted_by(|a, b| a.0.as_bytes() <= b.0.as_bytes()));

    // In a sorted list, if a key `x` is a prefix of a key `y`, then every key
    // between them also starts with `x`, so it is enough to check adjacent pairs.
    for (a, b) in entries.iter().zip(entries.iter().skip(1)) {
        let (a, b) = (a.0.as_bytes(), b.0.as_bytes());
        if a != b && b.starts_with(a) {
            return Some(InsertPrefixError {
                byte_repr: b.to_vec().into_boxed_slice(),
            });
        }
    }
    None
}

#[derive(Debug)]
enum BulkInsertFrame {
    Explore {
        current_depth: usize,
        slice_bounds: Range<usize>,
    },
    FinishInnerNode {
        start_depth: usize,
        slice_bounds: Range<usize>,
        prefix_end: usize,
        children_start_idx: usize,
        fragments_start_idx: usize,
    },
}

/// Constructs a trie from a pre-sorted iterator of keys and values.
///
/// The entries must be in strictly increasing order of key bytes (as returned
/// by [`AsBytes::as_bytes`]), and no key may be a prefix of any other key.
///
/// The key bytes are read once from each key after it is moved into its leaf,
/// and those bytes are checked against these requirements before building the
/// tree. This means a non-deterministic [`AsBytes`] implementation causes a
/// panic, not a malformed tree.
///
/// # Panic
///  - Panics if the list of entries is empty.
///  - Panics if the entries are not strictly increasing, or if any key is a prefix of another key.
pub fn bulk_insert_sorted<K, V, const PREFIX_LEN: usize>(
    mut entries: Peekable<impl Iterator<Item = (K, V)>>,
    alloc: &impl Allocator,
) -> BulkInsertOutput<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    assert!(
        entries.peek().is_some(),
        "list of items for bulk insert must not be empty"
    );

    let mut key_bytes = Vec::with_capacity(entries.size_hint().0);
    // If anything panics before the tree is finished, this guard deallocates the
    // leaves allocated so far, so that the keys and values are not leaked.
    let mut leaves_guard = LeafListGuard {
        min_leaf: None,
        alloc,
    };
    let mut prev_leaf = None;
    let mut num_entries = 0;
    for (key, value) in entries {
        let mut leaf = LeafNode::with_no_siblings(key, value);
        leaf.previous = prev_leaf;
        let leaf_ptr = NodePtr::allocate_node_ptr(leaf, alloc);
        if let Some(prev_leaf) = prev_leaf {
            // SAFETY: `prev_leaf` was allocated in the previous iteration of this loop
            // and is not deallocated in this function, so it is valid for writes.
            // This writes the `next` field through a raw place without creating a
            // `&mut LeafNode`, so the live shared reference to the previous leaf's key
            // (stored in `key_bytes`) is not invalidated. That reference covers only
            // the key, not the `next` field.
            unsafe { (*prev_leaf.to_ptr()).next = Some(leaf_ptr) };
        }
        // SAFETY: `leaf_ptr` was just allocated and initialized, and is not
        // deallocated in this function. The key is never mutated for the rest of this
        // function: later writes to this leaf only touch its `next` field, through a
        // raw place (see above).
        let key = unsafe { leaf_ptr.as_key_ref() };
        key_bytes.push(key.as_bytes());

        if leaves_guard.min_leaf.is_none() {
            leaves_guard.min_leaf = Some(leaf_ptr);
        }
        prev_leaf = Some(leaf_ptr);
        num_entries += 1;
    }
    let min_leaf = leaves_guard
        .min_leaf
        .expect("already checked non-empty list of entries");
    let max_leaf = prev_leaf.expect("already checked non-empty list of entries");

    // Check the bytes that the tree will actually be built from. Adjacent pairs are
    // enough: if every key is strictly less than the next one and not a prefix of
    // it, then no key is a prefix of any later key, because every key between a
    // prefix `x` and a key starting with `x` would also start with `x`.
    for (a, b) in key_bytes.iter().zip(key_bytes.iter().skip(1)) {
        assert!(
            a < b && !b.starts_with(a),
            "bulk insert keys must be strictly increasing and not prefixes of each other, the \
             `AsBytes` implementation may be non-deterministic"
        );
    }

    let mut stack = vec![BulkInsertFrame::Explore {
        current_depth: 0,
        slice_bounds: 0..num_entries,
    }];

    // We're leaving the key and value as `MaybeUninit` so we can do a final pass at
    // the end to actually initialize all the leaf nodes. This lets us avoid a
    // tricky situation here because we can't remove the key or value from the
    // `entries` vec while we have references in the `key_bytes` vec.
    //
    // The overall goal here is to avoid cloning the key or value, in case they are
    // large.
    let mut children = Vec::<OpaqueNodePtr<K, V, PREFIX_LEN>>::with_capacity(128);

    // The key byte of each child, pushed when the parent node is explored and
    // drained when it is finished. This works like a stack, since a node's
    // descendants are all finished before the node itself.
    let mut fragments = Vec::<u8>::new();
    // Scratch buffer for the start positions of each child group.
    let mut group_starts = Vec::<usize>::new();

    let mut next_leaf = Some(min_leaf);
    while let Some(frame) = stack.pop() {
        match frame {
            BulkInsertFrame::Explore {
                current_depth,
                slice_bounds,
            } => {
                if slice_bounds.start == (slice_bounds.end - 1) {
                    // In this case there is only a single entry in this part of
                    // the slice, so we're going to take the next leaf node from the linked list.

                    let leaf_ptr = next_leaf.expect(
                        "we should visit leaf conditions exactly equal to the number of leaves \
                         that are present",
                    );
                    // SAFETY: `leaf_ptr` comes from the leaf linked list built above, so it
                    // points to a live, initialized leaf. Leaves are no longer mutated at
                    // this point, so a shared reference is fine.
                    let leaf = unsafe { leaf_ptr.as_ref() };

                    next_leaf = leaf.next;

                    children.push(leaf_ptr.to_opaque());
                } else {
                    let key_bytes_subslice = &key_bytes[slice_bounds.clone()];
                    // We move past the equal parts of the key
                    let prefix_end = advance_depth_past_prefix(key_bytes_subslice, current_depth);

                    // Add this frame to know when to stop processing the current inner node
                    stack.push(BulkInsertFrame::FinishInnerNode {
                        start_depth: current_depth,
                        slice_bounds: slice_bounds.clone(),
                        prefix_end,
                        children_start_idx: children.len(),
                        fragments_start_idx: fragments.len(),
                    });

                    group_starts.clear();
                    group_unique_keys_at_depth(key_bytes_subslice, prefix_end, &mut group_starts);
                    fragments.extend(group_starts.iter().map(|&start_in_subslice| {
                        key_bytes_subslice[start_in_subslice][prefix_end]
                    }));

                    // We reverse this iterator so the last `Explore` frame pushed on will be from
                    // the earliest part of the current slice.
                    let unique_group_starts = group_starts
                        .iter()
                        .rev()
                        .map(|start_in_subslice| start_in_subslice + slice_bounds.start);
                    let mut prev_position = slice_bounds.end;

                    for start in unique_group_starts {
                        stack.push(BulkInsertFrame::Explore {
                            // We add a single byte here to account for the "child key byte", which
                            // each inner node uses to index into its children.
                            current_depth: prefix_end + 1,
                            slice_bounds: start..prev_position,
                        });
                        prev_position = start;
                    }
                }
            },
            BulkInsertFrame::FinishInnerNode {
                start_depth,
                slice_bounds,
                prefix_end,
                children_start_idx,
                fragments_start_idx,
            } => {
                assert!(!children.is_empty(), "there must be at least one child");

                let overall_num_children = children.len();
                assert!(
                    children_start_idx < overall_num_children,
                    "there must be enough children present for the inner node: \
                     {children_start_idx:?} < {overall_num_children:?}"
                );
                let num_children_for_this_node = overall_num_children - children_start_idx;

                assert!(
                    num_children_for_this_node > 1,
                    "there must be more than a single child for non-root inner node"
                );
                assert!(
                    num_children_for_this_node <= 256,
                    "the number of children must be less than 256"
                );

                let key_bytes_subslice = &key_bytes[slice_bounds.clone()];
                let prefix = &key_bytes_subslice[0][start_depth..prefix_end];

                fn allocate_inner_node_and_fill_children<
                    N: InnerNode<PREFIX_LEN>,
                    const PREFIX_LEN: usize,
                >(
                    prefix: &[u8],
                    alloc: &impl Allocator,
                    fragments: Drain<'_, u8>,
                    children: Drain<'_, OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN>>,
                ) -> OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN> {
                    let mut key_child_pair = fragments.zip(children);

                    let (first_key, first_child) = key_child_pair
                        .next()
                        .expect("inner node must have at least two children");
                    let (second_key, second_child) = key_child_pair
                        .next()
                        .expect("inner node must have at least two children");
                    // The key fragments come from sorted keys, so each child can be appended
                    // after the previous one.
                    let mut builder = N::builder(prefix, prefix.len())
                        .append_child(first_key, first_child)
                        .append_child(second_key, second_child);

                    for (key_fragment, child_pointer) in key_child_pair {
                        builder = builder.append_child(key_fragment, child_pointer);
                    }

                    let node_ptr = NodePtr::allocate_node_ptr(builder.build(), alloc);
                    node_ptr.to_opaque()
                }

                let new_child = match NodeType::type_for_num_children(num_children_for_this_node) {
                    NodeType::Node4 => allocate_inner_node_and_fill_children::<
                        InnerNode4<K, V, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        prefix,
                        alloc,
                        fragments.drain(fragments_start_idx..),
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node16 => allocate_inner_node_and_fill_children::<
                        InnerNode16<K, V, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        prefix,
                        alloc,
                        fragments.drain(fragments_start_idx..),
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node48 => allocate_inner_node_and_fill_children::<
                        InnerNode48<K, V, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        prefix,
                        alloc,
                        fragments.drain(fragments_start_idx..),
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node256 => allocate_inner_node_and_fill_children::<
                        InnerNodeDirect<K, V, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        prefix,
                        alloc,
                        fragments.drain(fragments_start_idx..),
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Leaf => unreachable!("Leaves have no children"),
                };

                children.push(new_child);
            },
        }
    }

    assert_eq!(
        children.len(),
        1,
        "there should be only a single child as the new root node"
    );
    let root = children.pop().unwrap();

    // The tree is complete and owns the leaves now.
    leaves_guard.min_leaf = None;

    BulkInsertOutput {
        root,
        min_leaf,
        max_leaf,
        num_entries,
    }
}

/// Deallocates a linked list of leaves on drop, starting from `min_leaf`.
struct LeafListGuard<'a, K, V, const PREFIX_LEN: usize, A: Allocator> {
    min_leaf: Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>,
    alloc: &'a A,
}

impl<K, V, const PREFIX_LEN: usize, A: Allocator> Drop for LeafListGuard<'_, K, V, PREFIX_LEN, A> {
    fn drop(&mut self) {
        let mut next = self.min_leaf.take();
        while let Some(leaf_ptr) = next {
            // SAFETY: The leaves in this list were allocated by `bulk_insert_sorted`
            // with `self.alloc`, and are not part of a finished tree (the guard is
            // cleared once the tree is complete), so nothing else will access or
            // deallocate them. Each leaf is deallocated once, since we move to the
            // next leaf before deallocating.
            let leaf = unsafe { NodePtr::deallocate_node_ptr(leaf_ptr, self.alloc) };
            next = leaf.next;
        }
    }
}

/// Push the positions in the `key_bytes` slice where each radix group of the
/// keys starts onto `starts`.
///
/// This always pushes at least one value: `0`. This function assumes that the
/// `key_bytes` slice is lexicographically sorted and that all the keys share
/// the same bytes before `current_depth`. Then each group of keys with the same
/// byte at `current_depth` is a contiguous run, so the end of each run can be
/// found with a binary search instead of comparing every key.
fn group_unique_keys_at_depth(
    key_bytes_subslice: &[&[u8]],
    current_depth: usize,
    starts: &mut Vec<usize>,
) {
    let mut start = 0;
    while start < key_bytes_subslice.len() {
        starts.push(start);
        let byte = key_bytes_subslice[start][current_depth];
        start += key_bytes_subslice[start..].partition_point(|key| key[current_depth] <= byte);
    }
}

/// Starting from `current_depth` advance past any common byte sequences in
/// `key_bytes` and return the new depth.
///
/// This function assumes that the given slice of key bytes is sorted
/// lexicographically, and that all the keys share the same bytes before
/// `current_depth`. In that case the common prefix of the whole slice is the
/// common prefix of the first and last key, since every key in between is
/// bounded by those two. This makes the function independent of the number of
/// keys.
fn advance_depth_past_prefix(key_bytes_subslice: &[&[u8]], current_depth: usize) -> usize {
    debug_assert!(key_bytes_subslice.is_sorted());

    let [first, .., last] = key_bytes_subslice else {
        return current_depth;
    };

    let common_len = first[current_depth..]
        .iter()
        .zip(&last[current_depth..])
        .take_while(|(a, b)| a == b)
        .count();

    current_depth + common_len
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use core::fmt;

    use super::*;
    use crate::testing::generate_key_fixed_length;
    #[cfg(feature = "std")]
    use crate::{
        allocator::Global,
        testing::{generate_keys_skewed, swap},
        TreeMap,
    };

    #[test]
    fn advance_depth_past_prefix_cases() {
        // Short circuit case
        assert_eq!(advance_depth_past_prefix(&[], 0), 0);
        assert_eq!(advance_depth_past_prefix(&[b"abcd"], 0), 0);

        // Case - immediately find current depth has non-equal values
        assert_eq!(advance_depth_past_prefix(&[b"a", b"b"], 0), 0);

        // Case - advances past shared prefix
        assert_eq!(advance_depth_past_prefix(&[b"000000a", b"000000b"], 0), 6);
        assert_eq!(advance_depth_past_prefix(&[b"000000a", b"000000b"], 3), 6);
    }

    fn group_starts(key_bytes: &[&[u8]], depth: usize) -> Vec<usize> {
        let mut starts = Vec::new();
        group_unique_keys_at_depth(key_bytes, depth, &mut starts);
        starts
    }

    #[test]
    fn group_unique_keys_at_depth_two_level_key() {
        let keys: Vec<_> = generate_key_fixed_length([15, 3]).collect();
        let key_bytes: Vec<_> = keys.iter().map(|key| key.as_bytes()).collect();

        assert_eq!(
            group_starts(&key_bytes, 0),
            vec![0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]
        );

        let mut last_idx = key_bytes.len();
        for start in [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]
            .into_iter()
            .rev()
        {
            let key_bytes_subslice = &key_bytes[start..last_idx];
            assert_eq!(
                group_starts(key_bytes_subslice, 1),
                // Since the second level of the key has 4 unique value, we expect each to become a
                // separate group
                vec![0, 1, 2, 3],
                "{key_bytes_subslice:?} {start}..{last_idx}"
            );
            last_idx = start;
        }
    }

    #[cfg(feature = "std")]
    fn check_bulk_insert_entries<K, V>(entries: Vec<(K, V)>)
    where
        K: AsBytes + PartialEq + fmt::Debug + Clone,
        V: PartialEq + fmt::Debug + Clone,
    {
        let output = bulk_insert::<_, _, { crate::collections::map::DEFAULT_PREFIX_LEN }>(
            entries.clone(),
            &Global,
        )
        .unwrap();

        // SAFETY: This is sorta safe? The `from_raw_in` does say its input from come
        // from a `TreeMap::into_raw` call, but this should be okay since we're keeping
        // the same allocator.
        //
        // Need this for deallocate and well-formed check
        let bulk_tree = unsafe { TreeMap::from_raw_in(Some(output.root), Global).unwrap() };

        let mut non_bulk_tree = TreeMap::new();
        for (key, value) in entries {
            non_bulk_tree.try_insert(key, value).unwrap();
        }

        assert_eq!(bulk_tree, non_bulk_tree);
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_integer_keys() {
        check_bulk_insert_entries(vec![(3, "c"), (17, "d"), (41, "e")]);
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_two_level_keys() {
        check_bulk_insert_entries(
            generate_key_fixed_length([15, 3])
                .enumerate()
                .map(swap)
                .collect(),
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_wide_short_keys() {
        check_bulk_insert_entries(
            generate_key_fixed_length([255])
                .enumerate()
                .map(swap)
                .collect(),
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_skewed_keys() {
        check_bulk_insert_entries(generate_keys_skewed(64).enumerate().map(swap).collect());
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_duplicate_keys_keeps_last() {
        check_bulk_insert_entries(vec![(3, "a"), (17, "b"), (3, "c"), (3, "d"), (41, "e")]);

        let map: TreeMap<u32, &str> = TreeMap::from(vec![(1, "a"), (2, "b"), (1, "c")]);
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&1), Some(&"c"));
        assert_eq!(map.get(&2), Some(&"b"));

        // Sorted input with duplicates takes the bulk insert path
        let map: TreeMap<u32, &str> = TreeMap::from(vec![(1, "a"), (1, "c"), (2, "b")]);
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&1), Some(&"c"));
        assert_eq!(map.get(&2), Some(&"b"));
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_prefix_keys_error() {
        use alloc::boxed::Box;

        let entries: Vec<(Box<[u8]>, usize)> = vec![
            (Box::from(&b"ab"[..]), 0),
            (Box::from(&b"a"[..]), 1),
            (Box::from(&b"b"[..]), 2),
        ];
        let err = bulk_insert::<_, _, 16>(entries, &Global).unwrap_err();
        assert_eq!(&*err.byte_repr, b"ab");
    }

    #[test]
    #[should_panic = "bulk insert keys must be strictly increasing"]
    fn bulk_insert_sorted_unsorted_keys_panics() {
        // The leaves allocated before the panic are deallocated by the guard, which
        // Miri checks with its leak detection.
        let entries = [([2u8], "b"), ([1u8], "a")];
        let _ = bulk_insert_sorted::<_, _, 16>(entries.into_iter().peekable(), &Global);
    }

    #[test]
    #[should_panic = "bulk insert keys must be strictly increasing"]
    fn bulk_insert_sorted_prefix_keys_panics() {
        use alloc::boxed::Box;

        let entries: Vec<(Box<[u8]>, usize)> =
            vec![(Box::from(&b"a"[..]), 0), (Box::from(&b"ab"[..]), 1)];
        let _ = bulk_insert_sorted::<_, _, 16>(entries.into_iter().peekable(), &Global);
    }

    #[test]
    #[cfg(feature = "std")]
    fn bulk_insert_singleton() {
        check_bulk_insert_entries(generate_keys_skewed(1).enumerate().map(swap).collect());
    }
}
