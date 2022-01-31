use std::iter;

pub fn generate_keys_skewed(max_len: usize) -> impl Iterator<Item = Box<[u8]>> {
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

pub fn generate_key_fixed_length(
    max_len: usize,
    value_stops: u8,
) -> impl Iterator<Item = Box<[u8]>> {
    iter::successors(
        Some(vec![u8::MIN; max_len].into_boxed_slice()),
        move |prev| {
            if prev.iter().all(|digit| *digit == u8::MAX) {
                None
            } else {
                Some(
                    prev.iter()
                        .map(|digit| digit.saturating_add(u8::MAX / value_stops))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                )
            }
        },
    )
}
