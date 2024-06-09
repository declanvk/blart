use argh::FromArgs;
use blart::{visitor::TreeStatsCollector, TreeMap};
use std::{
    error::Error,
    ffi::CString,
    fmt::Display,
    fs::{File, OpenOptions},
    io::{BufRead, BufReader},
    path::PathBuf,
};

#[derive(FromArgs)]
/// TREES
struct TreeToDotArgs {
    /// string used to delimit columns
    #[argh(option)]
    delimiter: Option<String>,

    /// input to read keys from an external file
    #[argh(positional)]
    input_file: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: TreeToDotArgs = argh::from_env();

    let input_file = OpenOptions::new()
        .read(true)
        .open(args.input_file)
        .expect("unable to open text file");

    let tree = read_key_values_from_text_file(input_file, args.delimiter);

    if tree.is_empty() {
        return Err(Box::new(EmptyTreeError));
    };

    collect_and_output_stats(tree)?;

    Ok(())
}

fn collect_and_output_stats(tree: TreeMap<Box<[u8]>, ()>) -> Result<(), Box<dyn Error>> {
    let root = tree.into_raw();

    // SAFETY: There are no concurrent mutation to the tree node or its children
    let stats = unsafe { TreeStatsCollector::collect(&root.unwrap()) };

    // SAFETY: This root pointer was created from earlier invocation of
    // `TreeMap::into_raw`, it is safe. No other tree is using this root.
    let _tree = unsafe { TreeMap::from_raw(root) };

    println!("{stats}");

    let overhead = stats.overhead_per_key_byte();

    println!("{overhead} bytes of overhead, per byte of key stored in tree");

    Ok(())
}

fn read_key_values_from_text_file(
    text_file: File,
    delimiter: Option<String>,
) -> TreeMap<Box<[u8]>, ()> {
    let iter = BufReader::new(text_file).lines().map(|line| {
        let line = line.expect("unable to read line");
        let key_content = if let Some(delimiter) = &delimiter {
            line.split(delimiter)
                .next()
                .expect("unable to get first element after split")
                .into()
        } else {
            line
        };

        let key = CString::new(key_content)
            .unwrap()
            .into_bytes_with_nul()
            .into_boxed_slice();

        (key, ())
    });

    let mut tree = TreeMap::new();

    for (key, value) in iter {
        let _ = tree.try_insert(key, value).unwrap();
    }

    tree
}

#[derive(Debug)]
struct EmptyTreeError;

impl Display for EmptyTreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "There were no keys to insert into the tree!")
    }
}

impl Error for EmptyTreeError {}
