mod iterator;
pub use iterator::*;

mod prefix;
pub use prefix::*;

mod into_iter;
pub use into_iter::*;

/*
/// An iterator over a sub-range of entries in a `TreeMap`.
///
/// This `struct` is created by the [`range`] method on `TreeMap`. See its
/// documentation for more.
///
/// [`range`]: TreeMap::range
pub struct Range<'a, K, V, H>(PhantomData<(&'a K, &'a V)>);

impl<'a, K, V, H> Iterator for Range<'a, K, V, H> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next_back()
    }

    #[cfg(feature = "nightly")]
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<'a, K, V, H> DoubleEndedIterator for Range<'a, K, V, H> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

/// A mutable iterator over a sub-range of entries in a `TreeMap`.
///
/// This `struct` is created by the [`range_mut`] method on `TreeMap`. See
/// its documentation for more.
///
/// [`range_mut`]: TreeMap::range_mut
pub struct RangeMut<'a, K, V, H>(PhantomData<(&'a K, &'a mut V)>);

impl<'a, K, V, H> Iterator for RangeMut<'a, K, V, H> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn min(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next()
    }

    fn max(mut self) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.next_back()
    }

    #[cfg(feature = "nightly")]
    fn is_sorted(self) -> bool
    where
        Self: Sized,
        Self::Item: PartialOrd,
    {
        true
    }
}

impl<'a, K, V, H> DoubleEndedIterator for RangeMut<'a, K, V, H> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
*/

// /// An iterator produced by calling [`drain_filter`] on `TreeMap`. See its
// /// documentation for more.
// ///
// /// [`drain_filter`]: TreeMap::range_mut
// pub struct ExtractIf<K, V, H>(PhantomData<(K, V)>);

// impl<K, V, H> Iterator for ExtractIf<K, V, H> {
//     type Item = (K, V);

//     fn next(&mut self) -> Option<Self::Item> {
//         todo!()
//     }
// }

#[cfg(test)]
mod tests {
    use crate::{tests_common::generate_key_fixed_length, TreeMap};

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
            first_half_last: [102, 255, 255],
            last_half_last: [153, 0, 0],
        };
        #[cfg(miri)]
        const TEST_PARAMS: TestValues = TestValues {
            value_stops: 3,
            half_len: 32,
            first_half_last: [85, 255, 255],
            last_half_last: [170, 0, 0],
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

        assert_eq!(first_remaining_half[0], &[0, 0, 0].into());
        assert_eq!(
            first_remaining_half[first_remaining_half.len() - 1],
            &TEST_PARAMS.first_half_last.into()
        );
        assert_eq!(last_remaining_half[0], &[255, 255, 255].into());
        assert_eq!(
            last_remaining_half[last_remaining_half.len() - 1],
            &TEST_PARAMS.last_half_last.into()
        );
    }

    #[test]
    fn prefix() {
        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcx", 0);
        t.insert(c"abcdx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(p0, vec![(&c"abcde", &0)]);
        assert_eq!(p1, vec![(&c"abcde", &0)]);

        let mut t = TreeMap::new();
        t.insert(c"abcde", 0);
        t.insert(c"abcdexxx", 0);
        t.insert(c"abcdexxy", 0);
        t.insert(c"abcdx", 0);
        t.insert(c"abcx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(
            p0,
            vec![(&c"abcde", &0), (&c"abcdexxx", &0), (&c"abcdexxy", &0)]
        );
        assert_eq!(
            p1,
            vec![(&c"abcdexxy", &0), (&c"abcdexxx", &0), (&c"abcde", &0)]
        );

        let mut t = TreeMap::new();
        t.insert(c"abcdexxx", 0);
        t.insert(c"abcdexxy", 0);
        t.insert(c"abcx", 0);
        t.insert(c"bx", 0);
        let p0: Vec<_> = t.prefix(c"abcde".to_bytes()).collect();
        let p1: Vec<_> = t.prefix(c"abcde".to_bytes()).rev().collect();
        assert_eq!(p0, vec![(&c"abcdexxx", &0), (&c"abcdexxy", &0)]);
        assert_eq!(p1, vec![(&c"abcdexxy", &0), (&c"abcdexxx", &0)]);
    }
}
