mod common;

#[test]
#[cfg(not(miri))]
fn test_memory_usage() {
    use blart::{testing, TreeMap};
    use common::{get_profiler, test_heap};

    const KEY_LENGTH_LIMIT: usize = u8::MAX as usize;

    let keys: Vec<_> = testing::generate_keys_skewed(KEY_LENGTH_LIMIT).collect();
    let keys_copy = keys.clone();
    let prof = get_profiler(file!());

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.total_blocks, 0);
        dhat::assert_eq!(stats.total_bytes, 0);
    });

    {
        let mut tree = TreeMap::new();

        for (idx, key) in keys.into_iter().enumerate() {
            tree.try_insert(key, idx).unwrap();
        }

        for (value, key) in keys_copy.into_iter().enumerate() {
            let result = tree.get(&key).unwrap();
            assert_eq!(result, &value, "{tree:?} {key:?}");
        }
    }

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.curr_blocks, 0);
        dhat::assert_eq!(stats.curr_bytes, 0);

        dhat::assert_eq!(stats.max_blocks, 510);
        dhat::assert_eq!(stats.max_bytes, 26488);

        let mean_blocks_per_key = (stats.max_blocks as f64) / (KEY_LENGTH_LIMIT as f64);
        let mean_bytes_per_key = (stats.max_bytes as f64) / (KEY_LENGTH_LIMIT as f64);

        eprintln!(
            "Inserting {KEY_LENGTH_LIMIT} keys, this comes to [{mean_blocks_per_key} mean blocks \
             per key] and [{mean_bytes_per_key} mean bytes per key].",
        )
    });
}
