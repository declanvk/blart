//! Helper function for writing tests

use std::{collections::HashSet, iter};

use crate::{
    raw::{InsertPrefixError, InsertResult, OpaqueNodePtr},
    AsBytes, TreeMap,
};

/// This function swaps the elements of a 2-tuple.
///
/// # Examples
///
/// ```
/// use blart::tests_common::swap;
///
/// assert_eq!(swap((1, 2)), (2, 1));
/// ```
pub fn swap<A, B>((a, b): (A, B)) -> (B, A) {
    (b, a)
}

/// Generate an iterator of bytestring keys, with increasing length up to a
/// maximum value.
///
/// This iterator will produce `max_len` number of keys. Each key has the form
/// `[0*, u8::MAX]`, meaning zero or more 0 values, followed by a single
/// `u8::MAX` value. The final `u8::MAX` value is added to ensure that no key is
/// a prefix of another key generated by this function.
///
/// # Examples
///
/// ```
/// # use blart::tests_common::generate_keys_skewed;
/// let keys = generate_keys_skewed(10).collect::<Vec<_>>();
/// assert_eq!(keys.len(), 10);
/// assert_eq!(keys[0].as_ref(), &[255]);
/// assert_eq!(keys[keys.len() - 1].as_ref(), &[0, 0, 0, 0, 0, 0, 0, 0, 0, 255]);
///
/// for k in keys {
///     println!("{:?}", k);
/// }
/// ```
///
/// The above example will print
/// ```text
/// [255]
/// [0, 255]
/// [0, 0, 255]
/// [0, 0, 0, 255]
/// [0, 0, 0, 0, 255]
/// [0, 0, 0, 0, 0, 255]
/// [0, 0, 0, 0, 0, 0, 255]
/// [0, 0, 0, 0, 0, 0, 0, 255]
/// [0, 0, 0, 0, 0, 0, 0, 0, 255]
/// [0, 0, 0, 0, 0, 0, 0, 0, 0, 255]
/// ```
///
/// # Panics
///  - Panics if `max_len` is 0.
pub fn generate_keys_skewed(max_len: usize) -> impl Iterator<Item = Box<[u8]>> {
    assert!(max_len > 0, "the fixed key length must be greater than 0");

    iter::successors(Some(vec![u8::MAX; 1].into_boxed_slice()), move |prev| {
        if prev.len() < max_len {
            let mut key = vec![u8::MIN; prev.len()];
            key.push(u8::MAX);
            Some(key.into_boxed_slice())
        } else {
            None
        }
    })
}

/// Generate an iterator of bytestring keys, all with the same length.
///
/// The `level_widths` argument specifies the number of values generated per
/// digit of the array. For example, using `[3, 2, 1]` will generate keys of
/// length 3. The generate keys will have 4 (3 + 1) unique values for the first
/// digit, 3 unique values for the second digit, and 2 unique values for the
/// last digit. In general, this iterator will produce `(level_widths[0] + 1)  *
/// (level_widths[1] + 1) * ... * (level_widths[KEY_LENGTH - 1] + 1)` keys in
/// total.
///
/// # Examples
///
/// ```
/// # use blart::tests_common::generate_key_fixed_length;
/// let keys = generate_key_fixed_length([3, 2, 1]).collect::<Vec<_>>();
/// assert_eq!(keys.len(), 24);
/// assert_eq!(keys[0].as_ref(), &[0, 0, 0]);
/// assert_eq!(keys[keys.len() / 2].as_ref(), &[2, 0, 0]);
/// assert_eq!(keys[keys.len() - 1].as_ref(), &[3, 2, 1]);
///
/// for k in keys {
///     println!("{:?}", k);
/// }
/// ```
///
/// The above example will print
/// ```text
/// [0, 0, 0]
/// [0, 0, 1]
/// [0, 1, 0]
/// [0, 1, 1]
/// [0, 2, 0]
/// [0, 2, 1]
/// [1, 0, 0]
/// [1, 0, 1]
/// [1, 1, 0]
/// [1, 1, 1]
/// [1, 2, 0]
/// [1, 2, 1]
/// [2, 0, 0]
/// [2, 0, 1]
/// [2, 1, 0]
/// [2, 1, 1]
/// [2, 2, 0]
/// [2, 2, 1]
/// [3, 0, 0]
/// [3, 0, 1]
/// [3, 1, 0]
/// [3, 1, 1]
/// [3, 2, 0]
/// [3, 2, 1]
/// ```
///
/// # Panics
///  - Panics if `max_len` is 0.
///  - Panics if `value_stops` is 0.
pub fn generate_key_fixed_length<const KEY_LENGTH: usize>(
    level_widths: [u8; KEY_LENGTH],
) -> impl Iterator<Item = [u8; KEY_LENGTH]> {
    struct FixedLengthKeys<const KEY_LENGTH: usize> {
        level_widths: [u8; KEY_LENGTH],
        next_value: Option<[u8; KEY_LENGTH]>,
    }

    impl<const KEY_LENGTH: usize> FixedLengthKeys<KEY_LENGTH> {
        pub fn new(level_widths: [u8; KEY_LENGTH]) -> Self {
            assert!(
                KEY_LENGTH > 0,
                "the fixed key length must be greater than 0"
            );
            assert!(
                level_widths.iter().all(|value_stops| value_stops > &0),
                "the number of distinct values for each key digit must be greater than 0"
            );

            FixedLengthKeys {
                level_widths,
                next_value: Some([u8::MIN; KEY_LENGTH]),
            }
        }
    }

    impl<const KEY_LENGTH: usize> Iterator for FixedLengthKeys<KEY_LENGTH> {
        type Item = [u8; KEY_LENGTH];

        fn next(&mut self) -> Option<Self::Item> {
            let next_value = self.next_value.take()?;

            if next_value
                .iter()
                .zip(self.level_widths)
                .all(|(digit, max_digit)| *digit == max_digit)
            {
                // the .take function already updated the next_value to None
                return Some(next_value);
            }

            let mut new_next_value = next_value;
            for idx in (0..new_next_value.len()).rev() {
                if new_next_value[idx] == self.level_widths[idx] {
                    new_next_value[idx] = u8::MIN;
                } else {
                    new_next_value[idx] = new_next_value[idx].saturating_add(1);
                    break;
                }
            }

            self.next_value = Some(new_next_value);
            Some(next_value)
        }
    }

    FixedLengthKeys::new(level_widths)
}

/// A single expansion of an existing existing that take an element at a
/// specified index and copies it multiple times.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrefixExpansion {
    /// The index in an unspecified sequence that will be copied.
    pub base_index: usize,
    /// The number of copies of the original element to create.
    pub expanded_length: usize,
}

/// Generate an iterator of fixed length bytestring keys, where specific
/// portions of the key are expanded as duplicate bytes.
///
/// This is meant to simulate keys with shared prefixes in different portions of
/// the key string.
///
/// # Examples
///
/// ```
/// # use blart::tests_common::{generate_key_with_prefix, PrefixExpansion};
/// let keys = generate_key_with_prefix([2; 3], [PrefixExpansion { base_index: 0, expanded_length: 3 }]).collect::<Vec<_>>();
/// assert_eq!(keys.len(), 27);
/// assert_eq!(keys[0].as_ref(), &[0, 0, 0, 0, 0]);
/// assert_eq!(keys[(keys.len() / 2) - 2].as_ref(), &[1, 1, 1, 0, 2]);
/// assert_eq!(keys[keys.len() - 1].as_ref(), &[2, 2, 2, 2, 2]);
///
/// for k in keys {
///     println!("{:?}", k);
/// }
/// ```
///
/// The above example will print out:
/// ```text
/// [0, 0, 0, 0, 0]
/// [0, 0, 0, 0, 1]
/// [0, 0, 0, 0, 2]
/// [0, 0, 0, 1, 0]
/// [0, 0, 0, 1, 1]
/// [0, 0, 0, 1, 2]
/// [0, 0, 0, 2, 0]
/// [0, 0, 0, 2, 1]
/// [0, 0, 0, 2, 2]
/// [1, 1, 1, 0, 0]
/// [1, 1, 1, 0, 1]
/// [1, 1, 1, 0, 2]
/// [1, 1, 1, 1, 0]
/// [1, 1, 1, 1, 1]
/// [1, 1, 1, 1, 2]
/// [1, 1, 1, 2, 0]
/// [1, 1, 1, 2, 1]
/// [1, 1, 1, 2, 2]
/// [2, 2, 2, 0, 0]
/// [2, 2, 2, 0, 1]
/// [2, 2, 2, 0, 2]
/// [2, 2, 2, 1, 0]
/// [2, 2, 2, 1, 1]
/// [2, 2, 2, 1, 2]
/// [2, 2, 2, 2, 0]
/// [2, 2, 2, 2, 1]
/// [2, 2, 2, 2, 2]
/// ```
///
/// # Panics
///  - Panics if `base_key_len` is 0.
///  - Panics if `value_stops` is 0.
///  - Panics if any `PrefixExpansion` has `expanded_length` equal to 0.
///  - Panics if any `PrefixExpansion` has `base_index` greater than or equal to
///    `base_key_len`.
pub fn generate_key_with_prefix<const KEY_LENGTH: usize>(
    level_widths: [u8; KEY_LENGTH],
    prefix_expansions: impl AsRef<[PrefixExpansion]>,
) -> impl Iterator<Item = Box<[u8]>> {
    fn apply_expansions_to_key(
        old_key: &[u8],
        new_key_template: &[u8],
        sorted_expansions: &[PrefixExpansion],
    ) -> Box<[u8]> {
        let mut new_key: Box<[u8]> = new_key_template.into();
        let mut new_key_index = 0usize;
        let mut old_key_index = 0usize;

        for expansion in sorted_expansions {
            let before_len = expansion.base_index - old_key_index;
            new_key[new_key_index..(new_key_index + before_len)]
                .copy_from_slice(&old_key[old_key_index..expansion.base_index]);
            new_key[(new_key_index + before_len)
                ..(new_key_index + before_len + expansion.expanded_length)]
                .fill(old_key[expansion.base_index]);

            old_key_index = expansion.base_index + 1;
            new_key_index += before_len + expansion.expanded_length;
        }

        // copy over remaining bytes from the old_key
        new_key[new_key_index..].copy_from_slice(&old_key[old_key_index..]);

        new_key
    }

    let expansions = prefix_expansions.as_ref();

    assert!(
        expansions
            .iter()
            .all(|expand| { expand.base_index < KEY_LENGTH }),
        "the prefix expansion index must be less than `base_key_len`."
    );
    assert!(
        expansions
            .iter()
            .all(|expand| { expand.expanded_length > 0 }),
        "the prefix expansion length must be greater than 0."
    );
    {
        let mut uniq_indices = HashSet::new();
        assert!(
            expansions
                .iter()
                .all(|expand| uniq_indices.insert(expand.base_index)),
            "the prefix expansion index must be unique"
        );
    }

    let mut sorted_expansions = expansions.to_vec();
    sorted_expansions.sort_by(|a, b| a.base_index.cmp(&b.base_index));

    let full_key_len = expansions
        .iter()
        .map(|expand| expand.expanded_length - 1)
        .sum::<usize>()
        + KEY_LENGTH;
    let full_key_template = vec![u8::MIN; full_key_len].into_boxed_slice();

    generate_key_fixed_length(level_widths)
        .map(move |key| apply_expansions_to_key(&key, &full_key_template, &sorted_expansions))
}

#[allow(dead_code)]
pub(crate) unsafe fn insert_unchecked<'a, K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key: K,
    value: V,
) -> Result<InsertResult<'a, K, V, PREFIX_LEN>, InsertPrefixError>
where
    K: AsBytes + 'a,
{
    use crate::raw::search_for_insert_point;

    let insert_point = unsafe { search_for_insert_point(root, key.as_bytes())? };
    Ok(unsafe { insert_point.apply(key, value) })
}

#[allow(dead_code)]
pub(crate) fn setup_tree_from_entries<K, V, const PREFIX_LEN: usize>(
    entries_it: impl Iterator<Item = (K, V)>,
) -> OpaqueNodePtr<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    let mut tree = TreeMap::with_prefix_len();

    for (key, value) in entries_it {
        let _ = tree.try_insert(key, value).unwrap();
    }

    TreeMap::into_raw(tree).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::TreeMap;

    use super::*;

    #[test]
    // disabled for miri because the runtime is too large, and this does not test any
    // safety-critical stuff
    #[cfg(not(miri))]
    fn key_generator_returns_expected_number_of_entries() {
        #[track_caller]
        fn check<K: AsBytes>(it: impl IntoIterator<Item = K>, expected_num_entries: usize) {
            let mut num_entries = 0;
            let it = it.into_iter().inspect(|_| num_entries += 1);
            let mut tree = TreeMap::new();
            for (key, value) in it.enumerate().map(|(a, b)| (b, a)) {
                tree.try_insert(key, value).unwrap();
            }

            assert_eq!(num_entries, tree.len());
            assert_eq!(expected_num_entries, num_entries);
        }

        check(generate_key_fixed_length([3, 2, 1]), 4 * 3 * 2);
        check(generate_key_fixed_length([15, 2]), 16 * 3);
        check(generate_key_fixed_length([255]), 256);
        check(generate_key_fixed_length([127]), 128);
        check(generate_key_fixed_length([7; 5]), 8 * 8 * 8 * 8 * 8);

        let no_op_expansion = [PrefixExpansion {
            base_index: 0,
            expanded_length: 1,
        }];
        check(
            generate_key_with_prefix([3, 2, 1], no_op_expansion),
            4 * 3 * 2,
        );
        check(generate_key_with_prefix([15, 2], no_op_expansion), 16 * 3);
        check(generate_key_with_prefix([255], no_op_expansion), 256);
        check(generate_key_with_prefix([127], no_op_expansion), 128);

        check(
            generate_key_with_prefix(
                [3, 2, 1],
                [
                    PrefixExpansion {
                        base_index: 0,
                        expanded_length: 1,
                    },
                    PrefixExpansion {
                        base_index: 1,
                        expanded_length: 1,
                    },
                    PrefixExpansion {
                        base_index: 2,
                        expanded_length: 1,
                    },
                ],
            ),
            4 * 3 * 2,
        );

        check(
            generate_key_with_prefix(
                [3, 2, 1],
                [
                    PrefixExpansion {
                        base_index: 0,
                        expanded_length: 3,
                    },
                    PrefixExpansion {
                        base_index: 1,
                        expanded_length: 256,
                    },
                    PrefixExpansion {
                        base_index: 2,
                        expanded_length: 127,
                    },
                ],
            ),
            4 * 3 * 2,
        );
    }
}
