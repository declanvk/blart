mod iterator;
pub use iterator::*;

mod prefix;
pub use prefix::*;

mod into_iter;
pub use into_iter::*;

mod fuzzy;
pub use fuzzy::*;

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
