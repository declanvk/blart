use core::{iter::FusedIterator, marker::PhantomData};

use crate::{
    allocator::{Allocator, Global},
    map::DEFAULT_PREFIX_LEN,
    raw::{maximum_unchecked, minimum_unchecked, OpaqueNodePtr, RawIterator},
    AsBytes, TreeMap,
};

macro_rules! implement_prefix_iter {
    (
        $(#[$outer:meta])*
        struct $name:ident {
            tree: $tree_ty:ty,
            item: $item_ty:ty,
            $leaf_accessor_func:ident
        }
    ) => {
        $(#[$outer])*
        pub struct $name<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global> {
            inner: RawIterator<K, V, PREFIX_LEN>,
            marker: PhantomData<$tree_ty>,
        }

        impl<'a, K: AsBytes, V, A: Allocator, const PREFIX_LEN: usize> $name<'a, K, V, PREFIX_LEN, A> {
            /// Create a new iterator over the given subtree, the iterator returns all
            /// key-value pairs in the subtree.
            ///
            /// # Safety:
            ///  - This function cannot be called concurrently with any mutating operation
            ///    on `root` or any child node of `root`. This function will arbitrarily
            ///    read to any child in the given tree.
            ///  - `root` must life for as long as the chosen lifetime and non mutated for the
            ///    length of that lifetime.
            pub(crate) unsafe fn new(
                root: OpaqueNodePtr<K, V, PREFIX_LEN>,
            ) -> Self {
                let (start, end) =
                    // SAFETY: The safety doc of this function guarantees no mutating
                    // operations will occur during this call.
                    unsafe { (minimum_unchecked(root), maximum_unchecked(root)) };

                Self {
                    // SAFETY: `start` is guaranteed to be less than or equal to `end` in the iteration
                    // order because of minimum_unchecked and maximum_unchecked
                    inner: unsafe { RawIterator::new(start, end) },
                    marker: PhantomData,
                }
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> Iterator for $name<'a, K, V, PREFIX_LEN, A> {
            type Item = $item_ty;

            fn next(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has a reference (either shared or mutable) to the
                // original `TreeMap` it is iterating over, preventing any other modification.
                let leaf_ptr = unsafe { self.inner.next()? };

                // SAFETY: The lifetimes returned from this function are returned as bounded by
                // lifetime 'a, meaning that they cannot outlive this iterator's reference
                // (shared or mutable) to the original TreeMap.
                Some(unsafe { leaf_ptr.$leaf_accessor_func() })
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> DoubleEndedIterator
            for $name<'a, K, V, PREFIX_LEN, A>
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                // SAFETY: This iterator has a reference (either shared or mutable) to the
                // original `TreeMap` it is iterating over, preventing any other modification.
                let leaf_ptr = unsafe { self.inner.next_back()? };

                // SAFETY: The lifetimes returned from this function are returned as bounded by
                // lifetime 'a, meaning that they cannot outlive this iterator's reference
                // (shared or mutable) to the original TreeMap.
                Some(unsafe { leaf_ptr.$leaf_accessor_func() })
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> FusedIterator for $name<'a, K, V, PREFIX_LEN, A> {}
    };
}

implement_prefix_iter!(
    /// An iterator over a subtree in a [`TreeMap`].
    ///
    /// This struct is created by the [`iter`][crate::map::InnerOccupiedEntry::iter] method on
    /// [`InnerOccupiedEntry`](crate::map::InnerOccupiedEntry).
    /// See its documentation for more details.
    struct SubtreeIter {
        tree: &'a TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a V),
        as_key_value_ref
    }
);

// SAFETY: This iterator holds a shared reference to the underlying `TreeMap`
// and thus can be moved across threads if the `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for SubtreeIter<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

// SAFETY: This iterator has no interior mutability and can be shared across
// thread so long as the reference `TreeMap<K, V>` can as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for SubtreeIter<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

implement_prefix_iter!(
    /// A mutable iterator over a range of entries that all have the same key prefix in a [`TreeMap`].
    ///
    /// This struct is created by the [`iter_mut`][crate::map::InnerOccupiedEntry::iter_mut] method
    /// on [`InnerOccupiedEntry`](crate::map::InnerOccupiedEntry).
    /// See its documentation for more details.
    struct SubtreeIterMut {
        tree: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
        item: (&'a K, &'a mut V),
        as_key_ref_value_mut
    }
);

// SAFETY: This iterator has a mutable reference to the underlying `TreeMap` and
// can be moved across threads if `&mut TreeMap<K, V>` is `Send`, which requires
// `TreeMap<K, V>` to be `Send` as well.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Send for SubtreeIterMut<'_, K, V, PREFIX_LEN, A>
where
    K: Send,
    V: Send,
    A: Send + Allocator,
{
}

// SAFETY: This iterator uses no interior mutability and can be shared across
// threads so long as `TreeMap<K, V>: Sync`.
unsafe impl<K, V, A, const PREFIX_LEN: usize> Sync for SubtreeIterMut<'_, K, V, PREFIX_LEN, A>
where
    K: Sync,
    V: Sync,
    A: Sync + Allocator,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterators_are_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn subtree_is_send<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_send::<SubtreeIter<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn subtree_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<SubtreeIter<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        subtree_is_send::<[u8; 3], usize, Global>();
        subtree_is_sync::<[u8; 3], usize, Global>();

        fn subtree_mut_is_send<'a, K: Send + 'a, V: Send + 'a, A: Send + Allocator + 'a>() {
            is_send::<SubtreeIterMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn subtree_mut_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<SubtreeIterMut<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        subtree_mut_is_send::<[u8; 3], usize, Global>();
        subtree_mut_is_sync::<[u8; 3], usize, Global>();
    }
}
