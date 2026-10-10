use core::fmt;

use super::{LeafNode, NodePtr};
use crate::allocator::Allocator;

type LeafPtr<K, V, const PREFIX_LEN: usize> = NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>;

struct RawIteratorInner<K, V, const PREFIX_LEN: usize> {
    start: LeafPtr<K, V, PREFIX_LEN>,
    end: LeafPtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> Copy for RawIteratorInner<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for RawIteratorInner<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for RawIteratorInner<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawIteratorInner")
            .field("start", &self.start)
            .field("end", &self.end)
            .finish()
    }
}

/// This struct represents a simple sort-iterator over leaves of a trie.
///
/// This struct does not actually implement the [`Iterator`] interface because
/// there are additional safety invariants on the [`next`][Self::next] and
/// [`next_back`][Self::next_back] functions.
pub struct RawIterator<K, V, const PREFIX_LEN: usize> {
    state: Option<RawIteratorInner<K, V, PREFIX_LEN>>,
}

impl<K, V, const PREFIX_LEN: usize> Copy for RawIterator<K, V, PREFIX_LEN> {}

impl<K, V, const PREFIX_LEN: usize> Clone for RawIterator<K, V, PREFIX_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PREFIX_LEN: usize> fmt::Debug for RawIterator<K, V, PREFIX_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawIterator")
            .field("state", &self.state)
            .finish()
    }
}

impl<K, V, const PREFIX_LEN: usize> RawIterator<K, V, PREFIX_LEN> {
    /// Create a new [`RawIterator`] with the given starting and ending
    /// pointers.
    ///
    /// # Safety
    /// `start` must be before or equal to `end` in the linked list order.
    pub unsafe fn new(start: LeafPtr<K, V, PREFIX_LEN>, end: LeafPtr<K, V, PREFIX_LEN>) -> Self {
        Self {
            state: Some(RawIteratorInner { start, end }),
        }
    }

    pub fn empty() -> Self {
        Self { state: None }
    }

    /// If the iterator is not empty, return the next leaf pointer in the
    /// forward direction.
    ///
    /// If the iterator is empty, this function returns `None`.
    ///
    /// # Safety
    ///
    /// This function must not be called concurrently with any modification on
    /// the tree since it will use shared references on the leaves.
    pub unsafe fn next(&mut self) -> Option<LeafPtr<K, V, PREFIX_LEN>> {
        match &mut self.state {
            None => None,
            Some(RawIteratorInner { start, end }) => {
                let is_singleton = start == end;

                let next = *start;

                if is_singleton {
                    self.state = None;
                } else {
                    // SAFETY: Covered by function safety doc
                    let start_leaf = unsafe { start.as_ref() };

                    // PANIC SAFETY: We can unwrap here because `is_singleton` implies that `start`
                    // and `end` are different, which also implies that `start` does not point to
                    // the last/maximum leaf
                    *start = start_leaf.next.unwrap();
                }

                Some(next)
            },
        }
    }

    /// If the iterator is not empty, return the next leaf pointer in the
    /// backwards direction.
    ///
    /// If the iterator is empty, this function returns `None`.
    ///
    /// # Safety
    ///
    /// This function must not be called concurrently with any modification on
    /// the tree since it will use shared references on the leaves.
    pub unsafe fn next_back(&mut self) -> Option<LeafPtr<K, V, PREFIX_LEN>> {
        match &mut self.state {
            None => None,
            Some(RawIteratorInner { start, end }) => {
                let is_singleton = start == end;

                let next_back = *end;

                if is_singleton {
                    self.state = None;
                } else {
                    // SAFETY: Covered by function safety doc
                    let end_leaf = unsafe { end.as_ref() };

                    // PANIC SAFETY: We can unwrap here because `is_singleton` implies that `start`
                    // and `end` are different, which also implies that `end` does not point to
                    // the last/maximum leaf. The safety requirements of `RawIterator::new` also
                    // require that `start` is before or equal to `end` in the linked list order.
                    *end = end_leaf.previous.unwrap();
                }

                Some(next_back)
            },
        }
    }
}

impl<K, V, const PREFIX_LEN: usize> RawIterator<K, V, PREFIX_LEN>
where
    K: Clone,
    V: Clone,
{
    /// Clones all leaves.
    ///
    /// # Safety
    ///
    /// This function must not be called concurrently with any modification on
    /// the tree since it will use shared references on the leaves.
    pub unsafe fn clone_leaves(&self, alloc: &impl Allocator) -> Self {
        struct DropGuard<'a, K, V, const PREFIX_LEN: usize, A: Allocator> {
            raw: Option<RawIteratorInner<K, V, PREFIX_LEN>>,
            alloc: &'a A,
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> DropGuard<'a, K, V, PREFIX_LEN, A> {
            fn into_raw(mut self) -> Option<RawIteratorInner<K, V, PREFIX_LEN>> {
                self.raw.take()
            }
        }

        impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> Drop for DropGuard<'a, K, V, PREFIX_LEN, A> {
            fn drop(&mut self) {
                let mut iter = RawIterator { state: self.raw };
                // SAFETY: these values have successfully been cloned, and we still own them
                while let Some(value) = unsafe { iter.next() } {
                    // SAFETY: value was just allocated using `self.alloc`
                    let _ = unsafe { NodePtr::deallocate_node_ptr(value, self.alloc) }.into_entry();
                }
            }
        }
        let mut copy = *self;
        let mut guard: DropGuard<_, _, _, _> = DropGuard { raw: None, alloc };
        // SAFETY: see function preconditions
        while let Some(cur) = unsafe { copy.next() } {
            let new =
                NodePtr::allocate_node_ptr(unsafe { cur.as_ref() }.clone_without_siblings(), alloc);
            if let Some(raw) = guard.raw.as_mut() {
                // SAFETY: new is unique here
                let new_mut = unsafe { new.as_mut() };
                // SAFETY: raw.end is unique here
                let prev_mut = unsafe { raw.end.as_mut() };
                prev_mut.next = Some(new);
                new_mut.previous = Some(raw.end);
                raw.end = new;
            } else {
                guard.raw = Some(RawIteratorInner {
                    start: new,
                    end: new,
                });
            }
        }
        // defuse the DropGuard!
        let raw = guard.into_raw();
        Self { state: raw }
    }
}
