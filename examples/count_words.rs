use argh::FromArgs;
use blart::TreeMap;
use std::{
    collections::BTreeMap, error::Error, ffi::CString, fs::OpenOptions, io::Read, path::PathBuf,
};

/// Count words in file
#[derive(FromArgs)]
struct CountWords {
    /// which map implementation to use for counting
    #[argh(positional, short = 'j')]
    map_impl: String,

    /// input to read keys from an external file
    #[argh(positional)]
    input_file: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: CountWords = argh::from_env();

    let mut input_file = OpenOptions::new()
        .read(true)
        .open(args.input_file)
        .expect("unable to open text file");

    let metadata = input_file
        .metadata()
        .expect("file metadata should be available");
    let file_len = metadata.len() as usize;
    let mut contents = Vec::with_capacity(file_len);

    let bytes_read = input_file
        .read_to_end(&mut contents)
        .expect("should be able to read entire file");

    assert_eq!(
        bytes_read, file_len,
        "should have read entire file into memory"
    );

    let stats = match args.map_impl.as_str() {
        "std" => count_words_std(&contents),
        "blart" => count_words_blart(&contents),
        other => panic!("unknown map impl '{other}'"),
    };

    println!("STATS: {stats:?}");

    Ok(())
}

#[derive(Debug)]
#[expect(dead_code)] // this struct is used for its debug repr
struct WordStats {
    num_unique: u64,
    first_word: CString,
    first_word_count: u64,
    last_word: CString,
    last_word_count: u64,
}

fn count_words_blart(contents: &[u8]) -> WordStats {
    let mut map = TreeMap::<CString, u64>::new();

    for word in contents.split_inclusive(|b| *b == SPLIT_BYTE) {
        let word = CString::new(word).unwrap();

        map.entry(word)
            .and_modify(|count| {
                *count += 1;
            })
            .or_insert(1);
    }

    let (first_word, first_word_count) = map
        .first_key_value()
        .expect("there should be at least 1 word in the map");

    let (last_word, last_word_count) = map
        .last_key_value()
        .expect("there should be at least 1 word in the map");

    WordStats {
        num_unique: map.len() as u64,
        last_word: last_word.clone(),
        last_word_count: *last_word_count,
        first_word: first_word.clone(),
        first_word_count: *first_word_count,
    }
}

const SPLIT_BYTE: u8 = b' ';

fn count_words_std(contents: &[u8]) -> WordStats {
    let mut map = BTreeMap::<CString, u64>::new();

    for word in contents.split_inclusive(|b| *b == SPLIT_BYTE) {
        let word = CString::new(word).unwrap();

        map.entry(word)
            .and_modify(|count| {
                *count += 1;
            })
            .or_insert(1);
    }

    let (first_word, first_word_count) = map
        .first_key_value()
        .expect("there should be at least 1 word in the map");

    let (last_word, last_word_count) = map
        .last_key_value()
        .expect("there should be at least 1 word in the map");

    WordStats {
        num_unique: map.len() as u64,
        last_word: last_word.clone(),
        last_word_count: *last_word_count,
        first_word: first_word.clone(),
        first_word_count: *first_word_count,
    }
}
