use std::{path::PathBuf, time::Instant};

use blart::AsBytes;
use blart_analysis::{datasets::load_sods_u64_dataset, key_analysis::analyze_sorted_key_iter};
use rayon::slice::ParallelSliceMut;

/// Calculate the inner node width distribution from the set of keys in a given
/// SOSD dataset.
#[derive(argh::FromArgs)]
struct Args {
    /// print timing information to stderr
    #[argh(switch, short = 't')]
    timing: bool,

    /// file path location of the SOSD dataset
    #[argh(positional)]
    path: PathBuf,
}

fn main() {
    let args: Args = argh::from_env();

    let mut keys = vec![];
    let start = Instant::now();
    load_sods_u64_dataset(&args.path, |k| {
        keys.extend(k.into_iter().map(|key| key.get().get()));
    })
    .unwrap();
    let load_time = start.elapsed();
    keys.as_mut_slice()
        .par_sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    let sort_time = start.elapsed() - load_time;

    let dist = analyze_sorted_key_iter(keys.iter().copied());
    let analyze_time = start.elapsed() - load_time - sort_time;

    if args.timing {
        eprintln!("Load={load_time:?} Sort={sort_time:?} Analyze={analyze_time:?}");
    }
    println!("{dist:?}");
}
