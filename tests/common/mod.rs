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

/// Create DHAT output folder and generate output filename based on test
/// filename.
#[cfg_attr(miri, allow(dead_code))]
pub fn generate_dhat_output_filename(test_filename: &str) -> PathBuf {
    let mut output_path = setup_dhat_output_dir();

    let test_filename_hash = {
        let mut hasher = rustc_hash::FxHasher::default();
        test_filename.hash(&mut hasher);
        hasher.finish()
    };

    output_path.push(format!("heap-{:x}.json", test_filename_hash));

    output_path
}

/// Initialize a [`dhat::Profiler`] for testing memory usage.
#[cfg_attr(miri, allow(dead_code))]
pub fn get_profiler(file_name: &str) -> dhat::Profiler {
    let output_path = generate_dhat_output_filename(file_name);

    dhat::Profiler::builder()
        .testing()
        .file_name(output_path)
        .trim_backtraces(Some(8)) // arbitrary choice, increase if needed
        .build()
}

/// Safe context to run `dhat::assert_*` methods, guaranteed running
/// [`dhat::Profiler`] and fresh [`dhat::HeapStats`]
#[cfg_attr(miri, allow(dead_code))]
pub fn test_heap<R>(_profiler: &dhat::Profiler, f: impl FnOnce(dhat::HeapStats) -> R) -> R {
    let stats = dhat::HeapStats::get();

    (f)(stats)
}
