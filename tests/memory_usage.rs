use blart::{deallocate_tree, insert_unchecked, search_unchecked, tests_common, LeafNode, NodePtr};
use std::{
    fs,
    hash::{Hash, Hasher},
    path::PathBuf,
};

#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

/// Setup a folder in the cargo `target/` directory that will hold dhat output
/// files.
fn setup_dhat_output_dir() -> PathBuf {
    const PARENT_OUTPUT_DIR: &str = "dhat-output/";

    let output_path = PathBuf::from(PARENT_OUTPUT_DIR);

    fs::create_dir_all(&output_path).expect("unable to create dhat output folder");

    output_path
}

fn generate_dhat_output_filename(test_filename: &str, function_name: &str) -> PathBuf {
    let mut output_path = setup_dhat_output_dir();

    let test_filename_hash = {
        let mut hasher = rustc_hash::FxHasher::default();
        eprintln!("TFN:{}", test_filename);
        test_filename.hash(&mut hasher);
        hasher.finish()
    };

    output_path.push(format!(
        "heap-{:x}-{}.json",
        test_filename_hash, function_name
    ));

    output_path
}

/// Initialize a [`dhat::Profiler`] for testing memory usage.
fn get_profiler(function_name: &str) -> dhat::Profiler {
    let output_path = generate_dhat_output_filename(file!(), function_name);

    dhat::Profiler::builder()
        .testing()
        .file_name(output_path)
        .trim_backtraces(Some(8)) // arbitrary choice, increase if needed
        .build()
}

/// Safe context to run `dhat::assert_*` methods, guaranteed running
/// [`dhat::Profiler`] and fresh [`dhat::HeapStats`]
fn test_heap(_profiler: &dhat::Profiler, f: impl FnOnce(dhat::HeapStats)) {
    let stats = dhat::HeapStats::get();

    (f)(stats)
}

#[test]
#[cfg(not(miri))]
fn test_memory_usage_of_skewed_tree() {
    // TODO(#1): Increase this back to `u8::MAX` after updating to an iterative
    // insert algorithm.
    const KEY_LENGTH_LIMIT: usize = (u8::MAX / 2) as usize;

    let prof = get_profiler("test_memory_usage_of_skewed_tree");

    test_heap(&prof, |stats| {
        dhat::assert_eq!(stats.curr_blocks, 0);
        dhat::assert_eq!(stats.curr_bytes, 0);

        dhat::assert_eq!(stats.max_blocks, 0);
        dhat::assert_eq!(stats.max_bytes, 0);
    });

    {
        let mut keys = tests_common::generate_keys_skewed(KEY_LENGTH_LIMIT);
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

        dhat::assert_eq!(stats.max_blocks, 382);
        dhat::assert_eq!(stats.max_bytes, 20626);

        let mean_blocks_per_key = (stats.max_blocks as f64) / (KEY_LENGTH_LIMIT as f64);
        let mean_bytes_per_key = (stats.max_bytes as f64) / (KEY_LENGTH_LIMIT as f64);

        eprintln!(
            "Inserting {} keys, this comes to [{} mean blockers per key] and [{} mean bytes per \
             key].",
            KEY_LENGTH_LIMIT, mean_blocks_per_key, mean_bytes_per_key
        )
    });
}
