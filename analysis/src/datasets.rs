//! This module has logic for loading different benchmark dataset.

use std::{fs::OpenOptions, io, mem, path::Path, ptr};

use memmap2::Mmap;
use zerocopy::{native_endian, FromBytes, Unalign};

macro_rules! generate_load_sods_dataset {
    ($fn_name:ident, $zerocopy:ty) => {
        /// Load an [SOSD](https://github.com/learnedsystems/SOSD) dataset from the given path and consume the
        /// values in-place with the given closure.
        ///
        /// The values are unaligned because we're memory mapping the dataset file to
        /// quickly access the keys, and the start pointer won't necessarily have the
        /// right alignment for a u32/u64 value.
        pub fn $fn_name(
            path: &Path,
            mut consume: impl FnMut(&[Unalign<$zerocopy>]),
        ) -> Result<(), io::Error> {
            let file = OpenOptions::new().read(true).open(path)?;
            file.lock_shared()?;

            // SAFETY: Lock means we should have exclusive readonly access
            let mapped = unsafe { Mmap::map(&file)? };

            let bytes = &mapped[..];

            // The first value in the file is the size of the file in number of bytes.
            let size_size = mem::size_of::<Unalign<$zerocopy>>();
            let size = Unalign::<$zerocopy>::read_from_bytes(&bytes[..size_size]).unwrap();

            // SAFETY: size is valid for reads because it was derived from the `bytes`
            // references. The values known initialized for the same reason.
            let size = unsafe { ptr::read_unaligned(size.get_ptr()).get() };
            let size = usize::try_from(size).unwrap();

            let remaining_bytes = &bytes[size_size..];
            assert_eq!(
                remaining_bytes.len(),
                size * mem::size_of::<Unalign<$zerocopy>>()
            );

            let keys =
                <[Unalign<$zerocopy>] as zerocopy::FromBytes>::ref_from_bytes(remaining_bytes)
                    .unwrap();

            (consume)(keys);

            Ok(())
        }
    };
}

generate_load_sods_dataset!(load_sods_u64_dataset, native_endian::U64);
generate_load_sods_dataset!(load_sods_u32_dataset, native_endian::U32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check() {
        let mut counter = 0;
        load_sods_u64_dataset(
            Path::new("/home/declan/repos/github/learnedsystems/SOSD/data/books_200M_uint64"),
            |keys| counter = keys.len(),
        )
        .unwrap();

        assert_eq!(counter, 200_000_000);
    }
}
