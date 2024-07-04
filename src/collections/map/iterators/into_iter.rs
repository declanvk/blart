use crate::{AsBytes, TreeMap};

/// An owning iterator over the entries of a `TreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on `TreeMap`
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
pub struct IntoIter<K: AsBytes, V, const PREFIX_LEN: usize>(TreeMap<K, V, PREFIX_LEN>);

impl<K: AsBytes, V, const PREFIX_LEN: usize> IntoIter<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        IntoIter(tree)
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Iterator for IntoIter<K, V, PREFIX_LEN> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        // TODO(#19): Optimize `IntoIter` by not maintaining a valid tree throughout
        // iteration
        self.0.pop_first()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len(), Some(self.0.len()))
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoIter<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_last()
    }
}

/// An owning iterator over the keys of a `TreeMap`.
///
/// This `struct` is created by the [`crate::TreeMap::into_keys`] method on
/// `TreeMap`. See its documentation for more.
pub struct IntoKeys<K: AsBytes, V, const PREFIX_LEN: usize>(IntoIter<K, V, PREFIX_LEN>);

impl<K: AsBytes, V, const PREFIX_LEN: usize> IntoKeys<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        IntoKeys(IntoIter::new(tree))
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Iterator for IntoKeys<K, V, PREFIX_LEN> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoKeys<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.0)
    }
}

/// An owning iterator over the values of a `TreeMap`.
///
/// This `struct` is created by the [`into_values`] method on `TreeMap`.
/// See its documentation for more.
///
/// [`into_values`]: crate::TreeMap::into_values
pub struct IntoValues<K: AsBytes, V, const PREFIX_LEN: usize>(IntoIter<K, V, PREFIX_LEN>);

impl<K: AsBytes, V, const PREFIX_LEN: usize> IntoValues<K, V, PREFIX_LEN> {
    pub(crate) fn new(tree: TreeMap<K, V, PREFIX_LEN>) -> Self {
        IntoValues(IntoIter::new(tree))
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> Iterator for IntoValues<K, V, PREFIX_LEN> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }
}

impl<K: AsBytes, V, const PREFIX_LEN: usize> DoubleEndedIterator for IntoValues<K, V, PREFIX_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.next_back()?.1)
    }
}
