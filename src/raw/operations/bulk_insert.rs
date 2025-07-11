//! Bulk load a trie from a pre-sorted iterator of keys and values

use std::{iter, mem::MaybeUninit, ops::Range, vec::Drain};

use crate::{
    alloc::Allocator,
    raw::{
        Header, InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, InsertPrefixError,
        LeafNode, NodePtr, NodeType, OpaqueNodePtr,
    },
    AsBytes,
};

#[derive(Debug)]
pub struct BulkInsertOutput<K, V, const PREFIX_LEN: usize> {
    pub root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    pub min_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
    pub max_leaf: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
}

/// Takes a list of keys and values and constructs a trie from them or returns
/// an error if any of the keys are prefixes.
///
/// This function is more efficient than inserting keys one-by-one since it can
/// construct entire sub-trees at a time.
///
/// # Panic
///
/// Panics if the list of items is empty.
pub fn bulk_insert<K, V, const PREFIX_LEN: usize>(
    mut entries: Vec<(K, V)>,
    alloc: &impl Allocator,
) -> Result<BulkInsertOutput<K, V, PREFIX_LEN>, InsertPrefixError>
where
    K: AsBytes,
{
    assert!(
        !entries.is_empty(),
        "list of items for bulk insert must not be empty"
    );

    // Sort the slice of key-value pairs by key.
    entries.sort_by(|(a, _), (b, _)| a.as_bytes().cmp(b.as_bytes()));

    // Prefix check
    if let Some(err) = check_key_prefixes(&entries) {
        return Err(err);
    }

    // Recursively build the trie from the iterator of key-value pairs.
    Ok(bulk_insert_unchecked(entries, alloc))
}

/// Return `Some(error)` if any of the keys in the given slice are prefixes of
/// each other.
///
/// This function assumes that the given slice is sorted by key bytes.
fn check_key_prefixes<K, V>(entries: &[(K, V)]) -> Option<InsertPrefixError>
where
    K: AsBytes,
{
    debug_assert!(entries.is_sorted_by(|a, b| a.0.as_bytes() <= b.0.as_bytes()));

    for (a, b) in entries.iter().zip(entries.iter().skip(1)) {
        if a.0.as_bytes().starts_with(b.0.as_bytes()) {
            return Some(InsertPrefixError {
                byte_repr: b.0.as_bytes().to_vec().into_boxed_slice(),
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
    },
}

/// Recursively constructs a trie from a pre-sorted iterator of keys and
/// values.
///
/// # Panic
///  - This function assumes that the list of entries is sorted by key bytes,
///    otherwise it may panic.
///  - This function also assumes that there are no key is a prefix of any other
///    key in the list, other it may panic.
pub fn bulk_insert_unchecked<K, V, const PREFIX_LEN: usize>(
    mut entries: Vec<(K, V)>,
    alloc: &impl Allocator,
) -> BulkInsertOutput<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    assert!(
        !entries.is_empty(),
        "list of items for bulk insert must not be empty"
    );

    let mut key_bytes = Vec::with_capacity(entries.len());
    key_bytes.extend(entries.iter().map(|entry| entry.0.as_bytes()));

    debug_assert!(key_bytes.is_sorted());

    let mut prev_leaf = None;
    let mut stack = vec![BulkInsertFrame::Explore {
        current_depth: 0,
        slice_bounds: 0..entries.len(),
    }];

    // We're leaving the key and value as `MaybeUninit` so we can do a final pass at
    // the end to actually initialize all the leaf nodes. This lets us avoid a
    // tricky situation here because we can't remove the key or value from the
    // `entries` vec while we have references in the `key_bytes` vec.
    //
    // The overall goal here is to avoid cloning the key or value, in case they are
    // large.
    let mut children =
        Vec::<OpaqueNodePtr<MaybeUninit<K>, MaybeUninit<V>, PREFIX_LEN>>::with_capacity(128);

    while let Some(frame) = stack.pop() {
        match frame {
            BulkInsertFrame::Explore {
                current_depth,
                slice_bounds,
            } => {
                if slice_bounds.start == (slice_bounds.end - 1) {
                    // In this case there is only a single entry in this part of
                    // the slice, so we're going to manufacture a leaf node.
                    let mut new_leaf = LeafNode::uninit_no_siblings();
                    // We only set the previous leaf pointer, we'll perform a final iteration
                    // through the tree leaves after constructing the tree to fixup the leave keys
                    // and values and "next pointers"
                    new_leaf.previous = prev_leaf;
                    let leaf_ptr = NodePtr::allocate_node_ptr(new_leaf, alloc);
                    prev_leaf = Some(leaf_ptr);
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
                    });

                    // We reverse this iterator so the last `Explore` frame pushed on will be from
                    // the earliest part of the current slice.
                    let unique_group_starts =
                        group_unique_keys_at_depth(key_bytes_subslice, prefix_end)
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
                let header = Header::<PREFIX_LEN>::new(prefix, prefix.len());

                fn allocate_inner_node_and_fill_children<
                    N: InnerNode<PREFIX_LEN>,
                    const PREFIX_LEN: usize,
                >(
                    header: Header<PREFIX_LEN>,
                    alloc: &impl Allocator,
                    key_bytes_subslice: &[&[u8]],
                    prefix_end: usize,
                    children: Drain<'_, OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN>>,
                ) -> OpaqueNodePtr<N::Key, N::Value, PREFIX_LEN> {
                    let mut inner_node = N::from_header(header);

                    let key_child_pair = group_unique_keys_at_depth(key_bytes_subslice, prefix_end)
                        .map(|idx| key_bytes_subslice[idx][prefix_end])
                        .zip(children);

                    // TODO(opt): Would it be possible to optimize this to fill all the children of
                    // an inner node at once?
                    for (key_fragment, child_pointer) in key_child_pair {
                        inner_node.write_child(key_fragment, child_pointer);
                    }

                    let node_ptr = NodePtr::allocate_node_ptr(inner_node, alloc);
                    node_ptr.to_opaque()
                }

                let new_child = match NodeType::type_for_num_children(num_children_for_this_node) {
                    NodeType::Node4 => allocate_inner_node_and_fill_children::<
                        InnerNode4<MaybeUninit<K>, MaybeUninit<V>, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        header,
                        alloc,
                        key_bytes_subslice,
                        prefix_end,
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node16 => allocate_inner_node_and_fill_children::<
                        InnerNode16<MaybeUninit<K>, MaybeUninit<V>, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        header,
                        alloc,
                        key_bytes_subslice,
                        prefix_end,
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node48 => allocate_inner_node_and_fill_children::<
                        InnerNode48<MaybeUninit<K>, MaybeUninit<V>, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        header,
                        alloc,
                        key_bytes_subslice,
                        prefix_end,
                        children.drain(children_start_idx..),
                    ),
                    NodeType::Node256 => allocate_inner_node_and_fill_children::<
                        InnerNode256<MaybeUninit<K>, MaybeUninit<V>, PREFIX_LEN>,
                        PREFIX_LEN,
                    >(
                        header,
                        alloc,
                        key_bytes_subslice,
                        prefix_end,
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
    let uninit_root = children.pop().unwrap();
    let uninit_max_leaf = prev_leaf.expect("entries must not be empty");

    // Here is where we fixup the uninitialized leaves' keys and values and `next`
    // pointers
    let mut previous_uninit_leaf_ptr = None;
    let mut current_uninit_leaf_ptr = uninit_max_leaf;
    let mut min_leaf_ptr = None;
    // Removing the entries starting from the back and iterating through the linked
    // list from the back
    while let Some((key, value)) = entries.pop() {
        // SAFETY: TODO
        let uninit_leaf = unsafe { current_uninit_leaf_ptr.as_mut() };

        uninit_leaf.write(key, value);
        uninit_leaf.next = previous_uninit_leaf_ptr;
        // Leaf should be fully initialized at this point, since the key, value,
        // previous, and next fields have all been written

        // SAFETY: TODO
        min_leaf_ptr = Some(unsafe { current_uninit_leaf_ptr.assume_init() });

        previous_uninit_leaf_ptr = Some(current_uninit_leaf_ptr);
        if let Some(new_uninit_leaf_ptr) = uninit_leaf.previous {
            current_uninit_leaf_ptr = new_uninit_leaf_ptr;
        }
    }

    // SAFETY: TODO
    let root = unsafe { uninit_root.assume_init() };
    // SAFETY: TODO
    let max_leaf = unsafe { uninit_max_leaf.assume_init() };
    // PANIC SAFETY: TODO
    let min_leaf = min_leaf_ptr.expect("entries must not be empty");

    BulkInsertOutput {
        root,
        min_leaf,
        max_leaf,
    }
}

/// Returns an iterator of positions in the `key_bytes` slice where the radix
/// grouping of the keys starts.
///
/// The iterator returned will always yield at least one value: `Some(0)`. This
/// function assumes that the `key_bytes` slice is lexicographically
/// sorted.
fn group_unique_keys_at_depth<'a>(
    key_bytes_subslice: &'a [&[u8]],
    current_depth: usize,
) -> impl DoubleEndedIterator<Item = usize> + 'a {
    iter::once(0).chain(
        key_bytes_subslice
            .iter()
            .enumerate()
            .map(move |(idx, bytes)| (idx, bytes[current_depth]))
            .zip(
                key_bytes_subslice
                    .iter()
                    .skip(1)
                    .map(move |bytes| bytes[current_depth]),
            )
            .filter_map(|((idx, a), b)| if a != b { Some(idx + 1) } else { None }),
    )
}

/// Starting from `current_depth` advance past any common byte sequences in
/// `key_bytes` and return the new depth.
///
/// # Panics
/// This function assumes that the given slice of key bytes is sorted
/// lexicographically. Otherwise it may panic on an out of bounds access.
fn advance_depth_past_prefix(key_bytes_subslice: &[&[u8]], current_depth: usize) -> usize {
    debug_assert!(key_bytes_subslice.is_sorted());

    if key_bytes_subslice.len() <= 1 {
        return current_depth;
    }

    let mut depth = current_depth;

    loop {
        if any_keys_not_equal_at_depth(key_bytes_subslice, depth) {
            break;
        } else {
            depth += 1;
        }
    }

    depth
}

/// Return true if all the bytes are equal across all keys at the given `depth`.
fn any_keys_not_equal_at_depth(key_bytes_subslice: &[&[u8]], depth: usize) -> bool {
    assert!(key_bytes_subslice.len() > 1);

    let first = key_bytes_subslice[0][depth];
    key_bytes_subslice.iter().any(|key| key[depth] != first)
}

#[cfg(test)]
mod tests {
    use std::fmt;

    use crate::{
        alloc::Global,
        tests_common::{generate_key_fixed_length, generate_keys_skewed, swap},
        TreeMap,
    };

    use super::*;

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

    #[test]
    fn group_unique_keys_at_depth_two_level_key() {
        let keys: Vec<_> = generate_key_fixed_length([15, 3]).collect();
        let key_bytes: Vec<_> = keys.iter().map(|key| key.as_bytes()).collect();

        assert_eq!(
            group_unique_keys_at_depth(&key_bytes, 0).collect::<Vec<_>>(),
            vec![0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]
        );

        let mut last_idx = key_bytes.len();
        for start in [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]
            .into_iter()
            .rev()
        {
            let key_bytes_subslice = &key_bytes[start..last_idx];
            assert_eq!(
                group_unique_keys_at_depth(key_bytes_subslice, 1).collect::<Vec<_>>(),
                // Since the second level of the key has 4 unique value, we expect each to become a
                // separate group
                vec![0, 1, 2, 3],
                "{key_bytes_subslice:?} {start}..{last_idx}"
            );
            last_idx = start;
        }
    }

    fn check_bulk_insert_entries<K, V>(entries: Vec<(K, V)>)
    where
        K: AsBytes + PartialEq + fmt::Debug + Clone,
        V: PartialEq + fmt::Debug + Clone,
    {
        let output = bulk_insert::<_, _, 16>(entries.clone(), &Global).unwrap();

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
    fn bulk_insert_integer_keys() {
        check_bulk_insert_entries(vec![(3, "c"), (17, "d"), (41, "e")]);
    }

    #[test]
    fn bulk_insert_two_level_keys() {
        check_bulk_insert_entries(
            generate_key_fixed_length([15, 3])
                .enumerate()
                .map(swap)
                .collect(),
        );
    }

    #[test]
    fn bulk_insert_wide_short_keys() {
        check_bulk_insert_entries(
            generate_key_fixed_length([255])
                .enumerate()
                .map(swap)
                .collect(),
        );
    }

    #[test]
    fn bulk_insert_skewed_keys() {
        check_bulk_insert_entries(generate_keys_skewed(64).enumerate().map(swap).collect());
    }

    #[test]
    fn bulk_insert_singleton() {
        check_bulk_insert_entries(generate_keys_skewed(1).enumerate().map(swap).collect());
    }
}
