use std::iter::FusedIterator;

use crate::{map::DEFAULT_PREFIX_LEN, RawIterator, TreeMap};

macro_rules! gen_iter {
    ($name:ident, $tree:ty, $ret:ty, $op:ident) => {
        /// An iterator over all the `LeafNode`s
        pub struct $name<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN> {
            inner: RawIterator<K, V, PREFIX_LEN>,
            size: usize,
            _tree: $tree,
        }

        impl<'a, K, V, const PREFIX_LEN: usize> $name<'a, K, V, PREFIX_LEN> {
            /// Create a new iterator that will visit all leaf nodes descended from the
            /// given node.
            pub(crate) fn new(tree: $tree) -> Self {
                let inner = match &tree.state {
                    // SAFETY: `min_leaf` is before or equal to `max_leaf` by construction and
                    // maintained on insert and delete from the tree
                    Some(state) => unsafe { RawIterator::new(state.min_leaf, state.max_leaf) },
                    None => RawIterator::empty(),
                };

                Self {
                    inner,
                    size: tree.num_entries,
                    _tree: tree,
                }
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> Iterator for $name<'a, K, V, PREFIX_LEN> {
            type Item = $ret;

            fn next(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has either a mutable or shared reference to the
                if let Some(next) = unsafe { self.inner.next() } {
                    self.size -= 1;
                    // `TreeMap`, so we know there will be no concurrent modification.
                    unsafe { Some(next.$op()) }
                } else {
                    None
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.size, Some(self.size))
            }

            fn last(mut self) -> Option<Self::Item>
            where
                Self: Sized,
            {
                self.next_back()
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> DoubleEndedIterator
            for $name<'a, K, V, PREFIX_LEN>
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has either a mutable or shared reference to the
                // `TreeMap`, so we know there will be no concurrent modification.
                if let Some(next) = unsafe { self.inner.next_back() } {
                    self.size -= 1;
                    // SAFETY: This iterator has either a mutable or shared reference to the
                    // `TreeMap`, so we know there will be no concurrent modification.
                    unsafe { Some(next.$op()) }
                } else {
                    None
                }
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize> FusedIterator for $name<'a, K, V, PREFIX_LEN> {}

        impl<'a, K, V, const PREFIX_LEN: usize> ExactSizeIterator for $name<'a, K, V, PREFIX_LEN> {
            fn len(&self) -> usize {
                self.size
            }
        }
    };
}

// SAFETY: Since we hold a shared reference is safe to
// create a shared reference to the leaf
gen_iter!(
    Iter,
    &'a TreeMap<K, V, PREFIX_LEN>,
    (&'a K, &'a V),
    as_key_value_ref
);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Send for Iter<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Sync for Iter<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: Since we hold a mutable reference is safe to
// create a mutable reference to the leaf
gen_iter!(
    IterMut,
    &'a mut TreeMap<K, V, PREFIX_LEN>,
    (&'a K, &'a mut V),
    as_key_ref_value_mut
);

// SAFETY: This iterator has a mutable reference to the underlying `TreeMap` and
// can be moved across threads if `&mut TreeMap<K, V>` is `Send`, which requires
// `TreeMap<K, V>` to be `Send` as well.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Send for IterMut<'a, K, V, PREFIX_LEN>
where
    K: Send,
    V: Send,
{
}

// SAFETY: This iterator uses no interior mutability and can be shared across
// threads so long as `TreeMap<K, V>: Sync`.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Sync for IterMut<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// The `Keys`, `Values`, and `ValuesMut` iterator only exist to match the
// interface of the `std::collections::BTreeMap`, otherwise I would not
// generally include them as they're mostly redundant with `Iter` and `IterMut`.

// SAFETY: Since we hold a shared reference is safe to
// create a shared reference to the leaf
gen_iter!(Keys, &'a TreeMap<K, V, PREFIX_LEN>, &'a K, as_key_ref);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Send for Keys<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Sync for Keys<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: Since we hold a shared reference is safe to
// create a shared reference to the leaf
gen_iter!(Values, &'a TreeMap<K, V, PREFIX_LEN>, &'a V, as_value_ref);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Send for Values<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Sync for Values<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

// SAFETY: Since we hold a mutable reference is safe to
// create a mutable reference to the leaf
gen_iter!(
    ValuesMut,
    &'a mut TreeMap<K, V, PREFIX_LEN>,
    &'a mut V,
    as_value_mut
);

// SAFETY: This iterator has a mutable reference to the underlying `TreeMap` and
// can be moved across threads if `&mut TreeMap<K, V>` is `Send`, which requires
// `TreeMap<K, V>` to be `Send` as well.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Send for ValuesMut<'a, K, V, PREFIX_LEN>
where
    K: Send,
    V: Send,
{
}

// SAFETY: This iterator uses no interior mutability and can be shared across
// threads so long as `TreeMap<K, V>: Sync`.
unsafe impl<'a, K, V, const PREFIX_LEN: usize> Sync for ValuesMut<'a, K, V, PREFIX_LEN>
where
    K: Sync,
    V: Sync,
{
}

#[cfg(test)]
mod tests {
    use crate::{tests_common::generate_key_fixed_length, TreeMap};

    use super::*;

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        // For `Iter`, `Keys`, and `Values` the requirement reads:
        // `unsafe impl<K: Sync, V: Sync> Send for Iter<K, V> {}`. The `Sync` bounds are
        // required because we're transferring a `&'a TreeMap<K, V>` across threads and
        // `&'a T` is only `Send` when `T` is `Sync`.
        fn iter_is_send<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_send::<Iter<'a, K, V>>();
        }

        fn iter_is_sync<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_sync::<Iter<'a, K, V>>();
        }

        iter_is_send::<[u8; 3], usize>();
        iter_is_sync::<[u8; 3], usize>();

        fn iter_mut_is_send<'a, K: Send + 'a, V: Send + 'a>() {
            is_send::<IterMut<'a, K, V>>();
        }

        fn iter_mut_is_sync<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_sync::<IterMut<'a, K, V>>();
        }

        iter_mut_is_send::<[u8; 3], usize>();
        iter_mut_is_sync::<[u8; 3], usize>();

        fn keys_is_send<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_send::<Keys<'a, K, V>>();
        }

        fn keys_is_sync<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_sync::<Keys<'a, K, V>>();
        }

        keys_is_send::<[u8; 3], usize>();
        keys_is_sync::<[u8; 3], usize>();

        fn values_is_send<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_send::<Values<'a, K, V>>();
        }

        fn values_is_sync<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_sync::<Values<'a, K, V>>();
        }

        values_is_send::<[u8; 3], usize>();
        values_is_sync::<[u8; 3], usize>();

        fn values_mut_is_send<'a, K: Send + 'a, V: Send + 'a>() {
            is_send::<ValuesMut<'a, K, V>>();
        }

        fn values_mut_is_sync<'a, K: Sync + 'a, V: Sync + 'a>() {
            is_sync::<ValuesMut<'a, K, V>>();
        }

        values_mut_is_send::<[u8; 3], usize>();
        values_mut_is_sync::<[u8; 3], usize>();
    }

    #[test]
    fn small_tree_iterator_front_and_back() {
        let keys: [Box<[u8]>; 9] = [
            vec![114, 159, 30].into_boxed_slice(),  // 0
            vec![30, 159, 204].into_boxed_slice(),  // 1
            vec![92, 39, 116].into_boxed_slice(),   // 2
            vec![58, 7, 66].into_boxed_slice(),     // 3
            vec![70, 30, 139].into_boxed_slice(),   // 4
            vec![220, 78, 94].into_boxed_slice(),   // 5
            vec![52, 231, 124].into_boxed_slice(),  // 6
            vec![173, 226, 147].into_boxed_slice(), // 7
            vec![6, 193, 187].into_boxed_slice(),   // 8
        ];

        let mut tree: TreeMap<_, _> = TreeMap::new();
        for (v, k) in keys.into_iter().enumerate() {
            tree.try_insert(k, v).unwrap();
        }

        let mut iter = tree.iter();

        assert_eq!(iter.next(), Some((&[6, 193, 187].into(), &8)));
        assert_eq!(iter.next(), Some((&[30, 159, 204].into(), &1)));
        assert_eq!(iter.next_back(), Some((&[220, 78, 94].into(), &5)));
        assert_eq!(iter.next_back(), Some((&[173, 226, 147].into(), &7)));

        let rest = iter.collect::<Vec<_>>();
        assert_eq!(rest.len(), 5);
        assert_eq!(
            rest,
            vec![
                (&[52, 231, 124].into(), &6),
                (&[58, 7, 66].into(), &3),
                (&[70, 30, 139].into(), &4),
                (&[92, 39, 116].into(), &2),
                (&[114, 159, 30].into(), &0),
            ]
        );
    }

    #[test]
    fn large_fixed_length_key_iterator_front_back() {
        struct TestValues {
            value_stops: u8,
            half_len: usize,
            first_half_last: [u8; 3],
            last_half_last: [u8; 3],
        }

        #[cfg(not(miri))]
        const TEST_PARAMS: TestValues = TestValues {
            value_stops: 5,
            half_len: 108,
            first_half_last: [2, 5, 5],
            last_half_last: [3, 0, 0],
        };
        #[cfg(miri)]
        const TEST_PARAMS: TestValues = TestValues {
            value_stops: 3,
            half_len: 32,
            first_half_last: [1, 3, 3],
            last_half_last: [2, 0, 0],
        };

        let keys = generate_key_fixed_length([TEST_PARAMS.value_stops; 3]);

        let mut tree: TreeMap<_, _> = TreeMap::new();
        for (v, k) in keys.enumerate() {
            tree.try_insert(k, v).unwrap();
        }

        let mut iter = tree.keys();

        let first_remaining_half = iter.by_ref().take(TEST_PARAMS.half_len).collect::<Vec<_>>();
        let last_remaining_half = iter
            .by_ref()
            .rev()
            .take(TEST_PARAMS.half_len)
            .collect::<Vec<_>>();

        assert!(iter.next().is_none());

        assert_eq!(first_remaining_half.len(), TEST_PARAMS.half_len);
        assert_eq!(last_remaining_half.len(), TEST_PARAMS.half_len);

        assert_eq!(first_remaining_half[0], &[0, 0, 0]);
        assert_eq!(
            first_remaining_half[first_remaining_half.len() - 1],
            &TEST_PARAMS.first_half_last
        );
        assert_eq!(
            last_remaining_half[0],
            if cfg!(miri) { &[3, 3, 3] } else { &[5, 5, 5] }
        );
        assert_eq!(
            last_remaining_half[last_remaining_half.len() - 1],
            &TEST_PARAMS.last_half_last
        );
    }
}
