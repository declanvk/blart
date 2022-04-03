#![feature(once_cell)]

mod common;

use blart::{deallocate_tree, insert_unchecked, search_unchecked, tests_common, LeafNode, NodePtr};
use common::{get_profiler, test_heap};

#[test]
#[cfg(not(miri))]
fn test_memory_usage() {
    // TODO(#1): Increase this back to `u8::MAX` after updating to an iterative
    // insert algorithm.
    const KEY_LENGTH_LIMIT: usize = (u8::MAX / 2) as usize;

    let keys: Vec<_> = tests_common::generate_keys_skewed(KEY_LENGTH_LIMIT).collect();

    let prof = get_profiler(file!());

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.total_blocks, 0);
        dhat::assert_eq!(stats.total_bytes, 0);
    });

    {
        let mut keys = keys.into_iter();
        let mut current_root =
            NodePtr::allocate_node(LeafNode::new(keys.next().unwrap(), 0)).to_opaque();

        for (idx, key) in keys.enumerate() {
            current_root = unsafe { insert_unchecked(current_root, key, idx + 1).unwrap() };
        }

        for (value, key) in tests_common::generate_keys_skewed(KEY_LENGTH_LIMIT).enumerate() {
            let search_result = unsafe { search_unchecked(current_root, key.as_ref()) };

            assert_eq!(search_result.unwrap().read().value, value);
        }

        unsafe { deallocate_tree(current_root) };
    }

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.curr_blocks, 0);
        dhat::assert_eq!(stats.curr_bytes, 0);

        dhat::assert_eq!(stats.max_blocks, 255);
        dhat::assert_eq!(stats.max_bytes, 12498);

        let mean_blocks_per_key = (stats.max_blocks as f64) / (KEY_LENGTH_LIMIT as f64);
        let mean_bytes_per_key = (stats.max_bytes as f64) / (KEY_LENGTH_LIMIT as f64);

        eprintln!(
            "Inserting {} keys, this comes to [{} mean blockers per key] and [{} mean bytes per \
             key].",
            KEY_LENGTH_LIMIT, mean_blocks_per_key, mean_bytes_per_key
        )
    });
}
