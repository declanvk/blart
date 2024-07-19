use std::{
    borrow::Borrow,
    collections::VecDeque,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
};

use crate::{
    check_prefix_lookup_child, AsBytes, ConcreteNodePtr, InnerNode, NodePtr, OpaqueNodePtr,
    OrderedBytes, TreeMap,
};

/// An iterator over a sub-range of entries in a [`TreeMap`][crate::TreeMap].
///
/// This `struct` is created by the [`TreeMap::range`][crate::TreeMap::range].
/// See its documentation for more.x
pub struct Range<'a, K, V, const PREFIX_LEN: usize> {
    nodes: VecDeque<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    _tree: &'a TreeMap<K, V, PREFIX_LEN>,
}

impl<'a, K, V, const PREFIX_LEN: usize> Range<'a, K, V, PREFIX_LEN> {
    /// Create a new iterator that will visit all leaf nodes descended from the
    /// given node.
    pub(crate) fn new<Q>(tree: &'a TreeMap<K, V, PREFIX_LEN>, bound: impl RangeBounds<Q>) -> Self
    where
        K: Borrow<Q> + OrderedBytes,
        Q: OrderedBytes + ?Sized,
    {
        let Some(root) = tree.root else {
            return Self {
                nodes: VecDeque::new(),
                _tree: tree,
            };
        };

        let start_bytes = bound
            .start_bound()
            .map(|b| Vec::from(b.as_bytes()).into_boxed_slice());
        let end_bytes = bound
            .start_bound()
            .map(|b| Vec::from(b.as_bytes()).into_boxed_slice());

        let (trimmed_root, current_depth) = match (&start_bytes, &end_bytes) {
            (
                Bound::Included(start_bytes) | Bound::Excluded(start_bytes),
                Bound::Included(end_bytes) | Bound::Excluded(end_bytes),
            ) => {
                let common_prefix = match_prefix(start_bytes, end_bytes);

                let trimmed_root = unsafe {
                    // SAFETY: TODO
                    find_iter_start_point(root, common_prefix)
                };

                (trimmed_root, common_prefix.len())
            },
            (Bound::Included(_) | Bound::Excluded(_), Bound::Unbounded)
            | (Bound::Unbounded, Bound::Included(_) | Bound::Excluded(_)) => (root, 0),
            (Bound::Unbounded, Bound::Unbounded) => {
                let nodes = VecDeque::from([root]);

                // This functions essential the same as an `Iter` over the tree
                return Self { nodes, _tree: tree };
            },
        };

        let start_byte = start_bytes.as_ref().map(|bytes| bytes[current_depth]);
        let end_byte = end_bytes.as_ref().map(|bytes| bytes[current_depth]);
        let bound = (start_byte, end_byte);

        let mut nodes = VecDeque::new();

        match trimmed_root.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => unsafe {
                // SAFETY: TODO
                push_back_range(&mut nodes, inner, bound)
            },
            ConcreteNodePtr::Node16(inner) => unsafe {
                // SAFETY: TODO
                push_back_range(&mut nodes, inner, bound)
            },
            ConcreteNodePtr::Node48(inner) => unsafe {
                // SAFETY: TODO
                push_back_range(&mut nodes, inner, bound)
            },
            ConcreteNodePtr::Node256(inner) => unsafe {
                // SAFETY: TODO
                push_back_range(&mut nodes, inner, bound)
            },
            ConcreteNodePtr::LeafNode(leaf_ptr) => {
                let leaf = unsafe { leaf_ptr.as_ref() };

                // If the root leaf node is inside of the full byte range,
                // then include it in the iteration. Otherwise, use the empty nodes
                // list
                if contains(
                    (start_bytes.as_ref(), end_bytes.as_ref()),
                    leaf.key_ref().as_bytes(),
                ) {
                    nodes.push_back(trimmed_root);

                    return Self { nodes, _tree: tree };
                } else {
                    return Self { nodes, _tree: tree };
                }
            },
        }

        todo!()
    }

    fn push_back_rev_iter<N>(&mut self, inner: NodePtr<PREFIX_LEN, N>)
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        // SAFETY: Since `Self` holds a mutable/shared reference
        // is safe to create a shared reference from it
        unsafe {
            inner
                .as_ref()
                .iter()
                .rev()
                .for_each(|(_, n)| self.nodes.push_back(n))
        };
    }

    fn push_front<N>(&mut self, inner: NodePtr<PREFIX_LEN, N>)
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        // SAFETY: Since `Self` holds a mutable/shared reference
        // is safe to create a shared reference from it
        unsafe {
            inner
                .as_ref()
                .iter()
                .for_each(|(_, n)| self.nodes.push_front(n))
        };
    }
}

impl<'a, K: OrderedBytes, V, const PREFIX_LEN: usize> Iterator for Range<'a, K, V, PREFIX_LEN> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.nodes.pop_back() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node16(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node48(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::Node256(inner) => self.push_back_rev_iter(inner),
                ConcreteNodePtr::LeafNode(inner) => {
                    return unsafe { Some(inner.as_key_value_ref()) };
                },
            }
        }

        None
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
        // We get this since we only implement iterator for tree containing `Ord` keys,
        // and the leaves will be iterated in sorted order by key
        true
    }
}

impl<'a, K: OrderedBytes, V, const PREFIX_LEN: usize> DoubleEndedIterator
    for Range<'a, K, V, PREFIX_LEN>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.nodes.pop_front() {
            match node.to_node_ptr() {
                ConcreteNodePtr::Node4(inner) => self.push_front(inner),
                ConcreteNodePtr::Node16(inner) => self.push_front(inner),
                ConcreteNodePtr::Node48(inner) => self.push_front(inner),
                ConcreteNodePtr::Node256(inner) => self.push_front(inner),
                ConcreteNodePtr::LeafNode(inner) => {
                    return unsafe { Some(inner.as_key_value_ref()) };
                },
            }
        }

        None
    }
}

/// A mutable iterator over a sub-range of entries in a
/// [`TreeMap`][crate::TreeMap].
///
/// This `struct` is created by the
/// [`TreeMap::range_mut`][crate::TreeMap::range]. See its documentation for
/// more.
pub struct RangeMut<'a, K, V>(PhantomData<(&'a K, &'a mut V)>);

impl<'a, K, V> RangeMut<'a, K, V> {
    pub(crate) fn new() -> Self {
        todo!()
    }
}

impl<'a, K, V> Iterator for RangeMut<'a, K, V> {
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

impl<'a, K, V> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

fn contains<'a, T: AsRef<[u8]> + 'a>(bound: impl RangeBounds<&'a T>, key_bytes: &[u8]) -> bool {
    (match bound.start_bound() {
        Bound::Included(bytes) => bytes.as_ref() <= key_bytes,
        Bound::Excluded(bytes) => bytes.as_ref() < key_bytes,
        Bound::Unbounded => true,
    }) && (match bound.end_bound() {
        Bound::Included(bytes) => key_bytes <= bytes.as_ref(),
        Bound::Excluded(bytes) => key_bytes < bytes.as_ref(),
        Bound::Unbounded => true,
    })
}

/// Push all the children of the given node that have key bytes within the
/// given range into the back of the deque in reverse order.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `inner`.
unsafe fn push_back_range<N, K, V, const PREFIX_LEN: usize>(
    nodes: &mut VecDeque<OpaqueNodePtr<K, V, PREFIX_LEN>>,
    inner: NodePtr<PREFIX_LEN, N>,
    bound: impl RangeBounds<u8>,
) where
    N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
{
    // SAFETY: The lifetime of `as_ref` does not escape this function, and does not
    // overlap with any mutating operations (per the preconditions of this function)
    unsafe {
        inner
            .as_ref()
            .range(bound)
            .rev()
            .for_each(|(_, n)| nodes.push_back(n))
    };
}

fn match_prefix<'a>(a: &'a [u8], b: &[u8]) -> &'a [u8] {
    let mut matching = 0;
    for (a_val, b_val) in a.iter().copied().zip(b.iter().copied()) {
        if a_val != b_val {
            return &a[..matching];
        }
        matching += 1;
    }
    &a[..matching]
}

/// Find the point in the tree that is identified by the given prefix.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
unsafe fn find_iter_start_point<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    common_prefix: &[u8],
) -> OpaqueNodePtr<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let next_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, common_prefix, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, common_prefix, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, common_prefix, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, common_prefix, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(_) => {
                return current_node;
            },
        };

        let next_node = match next_node {
            Some(node) => node,
            None => {
                return current_node;
            },
        };

        current_node = next_node;
    }
}
