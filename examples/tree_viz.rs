use std::{
    error::Error,
    ffi::CString,
    fmt::Display,
    fs::OpenOptions,
    io::{self, BufRead, BufReader, BufWriter, Write},
    path::{Path, PathBuf},
};

use argh::FromArgs;
use blart::{
    visitor::{DotPrinter, DotPrinterSettings},
    AsBytes, NoPrefixesBytes, TreeMap,
};

#[derive(FromArgs)]
/// TREES
struct TreeToDotArgs {
    /// optional delimiter to split key from value on each file line
    #[argh(option)]
    delimiter: Option<char>,

    /// input to read keys from an external file
    #[argh(positional)]
    input_file: PathBuf,

    /// where to output the tree diagram
    ///
    /// To output to stdout, use '_'.
    #[argh(positional)]
    output_location: String,
}

fn main() {
    let args: TreeToDotArgs = argh::from_env();

    let mut tree = TreeMap::new();

    for (key, value) in read_key_values_from_text_file(&args.input_file, args.delimiter) {
        let _ = tree.insert(key, value);
    }

    if tree.is_empty() {
        panic!("Tree should now be empty after reading keys from file");
    };

    if args.output_location == "_" {
        let stdout = io::stdout();
        let handle = stdout.lock();

        let mut buffer = BufWriter::new(handle);

        write_tree(&mut buffer, tree)
    } else {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(args.output_location)
            .expect("Failed to open file for output");

        let mut buffer = BufWriter::new(file);

        write_tree(&mut buffer, tree)
    }
    .expect("Failed to write tree to output")
}

pub struct DisplayWrapper(CString);

impl Display for DisplayWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.to_string_lossy())
    }
}

impl AsBytes for DisplayWrapper {
    fn as_bytes(&self) -> &[u8] {
        <CString as AsBytes>::as_bytes(&self.0)
    }
}

// SAFETY: We can impl `NoPrefixesBytes` since `CString` also implements that
unsafe impl NoPrefixesBytes for DisplayWrapper where CString: NoPrefixesBytes {}

fn write_tree(
    output: &mut dyn Write,
    tree: TreeMap<DisplayWrapper, String>,
) -> Result<(), Box<dyn Error>> {
    DotPrinter::print(output, &tree, DotPrinterSettings::default()).unwrap()?;

    Ok(())
}

fn read_key_values_from_text_file(
    text_file_path: &Path,
    delimiter: Option<char>,
) -> impl Iterator<Item = (DisplayWrapper, String)> {
    let text_file = OpenOptions::new()
        .read(true)
        .open(text_file_path)
        .expect("unable to open text file");

    BufReader::new(text_file).lines().map(move |line| {
        let line = line.expect("unable to read line");
        if let Some(delimiter) = delimiter {
            let entry_components = line.split(delimiter).collect::<Vec<_>>();

            assert_eq!(
                entry_components.len(),
                2,
                "Each line must only have delimiter once"
            );

            let key = entry_components[0];
            let value = entry_components[1];

            (
                DisplayWrapper(CString::new(String::from(key).into_bytes()).unwrap()),
                value.into(),
            )
        } else {
            (
                DisplayWrapper(CString::new(line.into_bytes()).unwrap()),
                String::new(),
            )
        }
    })
}
