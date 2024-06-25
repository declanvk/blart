mod common;

#[test]
#[cfg(not(miri))]
fn test_memory_usage() {
    use blart::{tests_common, tests_common::PrefixExpansion, TreeMap};
    use common::{get_profiler, test_heap};

    const KEY_LEVEL_WIDTH: [u8; 3] = [6, 6, 5];
    const PREFIX_EXPANSIONS: [PrefixExpansion; 2] = [
        PrefixExpansion {
            base_index: 0,
            expanded_length: 9,
        },
        PrefixExpansion {
            base_index: 2,
            expanded_length: 2,
        },
    ];

    let keys: Vec<_> =
        tests_common::generate_key_with_prefix(KEY_LEVEL_WIDTH, PREFIX_EXPANSIONS).collect();
    let prof = get_profiler(file!());

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.total_blocks, 0);
        dhat::assert_eq!(stats.total_bytes, 0);
    });

    {
        let keys = keys.into_iter();
        let mut tree = TreeMap::new();

        for (idx, key) in keys.enumerate() {
            tree.try_insert(key, idx).unwrap();
        }

        for (value, key) in
            tests_common::generate_key_with_prefix(KEY_LEVEL_WIDTH, PREFIX_EXPANSIONS).enumerate()
        {
            let result = tree.get(&key).unwrap();
            assert_eq!(result, &value);
        }
    }

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.curr_blocks, 0);
        dhat::assert_eq!(stats.curr_bytes, 0);

        dhat::assert_eq!(stats.max_blocks, 352);
        dhat::assert_eq!(stats.max_bytes, 16696);

        let num_keys = KEY_LEVEL_WIDTH
            .iter()
            .map(|val| (*val as usize) + 1)
            .product::<usize>() as f64;

        let mean_blocks_per_key = (stats.max_blocks as f64) / num_keys;
        let mean_bytes_per_key = (stats.max_bytes as f64) / num_keys;

        eprintln!(
            "Inserting {num_keys} keys, this comes to [{mean_blocks_per_key} mean blocks per key] \
             and [{mean_bytes_per_key} mean bytes per key].",
        )
    });
}
