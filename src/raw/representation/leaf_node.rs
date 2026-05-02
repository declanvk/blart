use core::cmp::Ordering;

use crate::{
    raw::{Node, NodePtr, NodeType},
    AsBytes,
};

/// This type alias represents an optional pointer to a leaf node.
pub(crate) type OptionalLeafPtr<K, V, const PREFIX_LEN: usize> =
    Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>>;

/// Node that contains a single leaf value.
#[derive(Debug)]
#[repr(align(8))]
pub struct LeafNode<K, V, const PREFIX_LEN: usize> {
    /// The leaf value.
    value: V,
    /// The full key that the `value` was stored with.
    key: K,

    /// Pointer to the previous leaf node in the trie. If the value is `None`,
    /// then this is the first leaf.
    pub(crate) previous: OptionalLeafPtr<K, V, PREFIX_LEN>,

    /// Pointer to the next leaf node in the trie. If the value is `None`,
    /// then this is the last leaf.
    pub(crate) next: OptionalLeafPtr<K, V, PREFIX_LEN>,
}

impl<K, V, const PREFIX_LEN: usize> LeafNode<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    /// Insert the leaf node pointed to by `this_ptr` into the linked list that
    /// `previous_sibling_ptr` belongs to, placing the "this" leaf node after
    /// the "previous sibling" in the list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node, the `previous_sibling_ptr` leaf
    /// node, and the sibling leaf node of `previous_sibling_ptr`.
    pub unsafe fn insert_after(
        this_ptr: NodePtr<PREFIX_LEN, Self>,
        previous_sibling_ptr: NodePtr<PREFIX_LEN, Self>,
    ) {
        // SAFETY: Covered by safety doc of this function
        let (this, previous_sibling) =
            unsafe { (this_ptr.as_mut(), previous_sibling_ptr.as_mut()) };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            debug_assert!(
                previous_sibling.key.as_bytes() < this.key.as_bytes(),
                "sibling must be ordered before this leaf in the trie"
            );
        }

        this.previous = Some(previous_sibling_ptr);
        this.next = previous_sibling.next;

        if let Some(next_sibling_ptr) = previous_sibling.next {
            // SAFETY: Covered by safety doc of this function
            let next_sibling = unsafe { next_sibling_ptr.as_mut() };
            next_sibling.previous = Some(this_ptr);
        }
        previous_sibling.next = Some(this_ptr);
    }

    /// Insert the leaf node pointed to by `this_ptr` into the linked list that
    /// `next_sibling_ptr` belongs to, placing the "this" leaf node before
    /// the "next sibling" in the list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node, the `next_sibling_ptr` leaf
    /// node, and the sibling leaf node of `next_sibling_ptr`.
    pub unsafe fn insert_before(
        this_ptr: NodePtr<PREFIX_LEN, Self>,
        next_sibling_ptr: NodePtr<PREFIX_LEN, Self>,
    ) {
        // SAFETY: Covered by safety doc of this function
        let (this, next_sibling) = unsafe { (this_ptr.as_mut(), next_sibling_ptr.as_mut()) };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.key.as_bytes() < next_sibling.key.as_bytes(),
                "this leaf must be ordered before sibling in the trie"
            );
        }

        this.previous = next_sibling.previous;
        this.next = Some(next_sibling_ptr);

        if let Some(previous_sibling_ptr) = next_sibling.previous {
            // SAFETY: Covered by safety doc of this function
            let previous_sibling = unsafe { previous_sibling_ptr.as_mut() };
            previous_sibling.next = Some(this_ptr);
        }
        next_sibling.previous = Some(this_ptr);
    }

    /// Insert the leaf node pointed to by `this_ptr` into the linked list
    /// position that `old_leaf` currently occupies, and then remove `old_leaf`
    /// from the linked list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node and the sibling leaf nodes of the
    /// `old_leaf`.
    pub unsafe fn replace(this_ptr: NodePtr<PREFIX_LEN, Self>, old_leaf: &mut Self, force: bool) {
        // SAFETY: Covered by safety doc of this function
        let this = unsafe { this_ptr.as_mut() };

        if cfg!(debug_assertions) {
            debug_assert!(
                this.previous.is_none(),
                "previous ptr should be None on insert into linked list"
            );
            debug_assert!(
                this.next.is_none(),
                "next ptr should be None on insert into linked list"
            );
            if !force {
                debug_assert_eq!(
                    this.key.as_bytes(),
                    old_leaf.key.as_bytes(),
                    "To replace a node, the key must be exactly the same"
                );
            }
        }

        this.next = old_leaf.next;
        this.previous = old_leaf.previous;

        if let Some(prev_leaf_ptr) = this.previous {
            // SAFETY: Covered by safety doc of this function
            let prev_leaf = unsafe { prev_leaf_ptr.as_mut() };
            prev_leaf.next = Some(this_ptr);
        }

        if let Some(next_leaf_ptr) = this.next {
            // SAFETY: Covered by safety doc of this function
            let next_leaf = unsafe { next_leaf_ptr.as_mut() };
            next_leaf.previous = Some(this_ptr);
        }

        old_leaf.next = None;
        old_leaf.previous = None;
    }
}

impl<const PREFIX_LEN: usize, K, V> LeafNode<K, V, PREFIX_LEN> {
    /// Create a new leaf node with the given value and no siblings.
    pub fn with_no_siblings(key: K, value: V) -> Self {
        LeafNode {
            value,
            key,
            previous: None,
            next: None,
        }
    }

    /// Returns a shared reference to the key contained by this leaf node
    pub fn key_ref(&self) -> &K {
        &self.key
    }

    /// Returns a shared reference to the value contained by this leaf node
    pub fn value_ref(&self) -> &V {
        &self.value
    }

    /// Returns a mutable reference to the value contained by this leaf node
    pub fn value_mut(&mut self) -> &mut V {
        &mut self.value
    }

    /// Return shared references to the key and value contained by this leaf
    /// node
    pub fn entry_ref(&self) -> (&K, &V) {
        (&self.key, &self.value)
    }

    /// Return mutable references to the key and value contained by this leaf
    /// node
    pub fn entry_mut(&mut self) -> (&mut K, &mut V) {
        (&mut self.key, &mut self.value)
    }

    /// Consume the leaf node and return a tuple of the key and value
    pub fn into_entry(self) -> (K, V) {
        (self.key, self.value)
    }

    /// Check that the provided full key is the same one as the stored key.
    pub fn matches_full_key(&self, possible_key: &[u8]) -> bool
    where
        K: AsBytes,
    {
        self.key.as_bytes().eq(possible_key)
    }

    /// Compare lexicographically the leaf stored key bytes with the given
    /// search key bytes.
    pub fn compare_full_key(&self, possible_key: &[u8]) -> Ordering
    where
        K: AsBytes,
    {
        self.key.as_bytes().cmp(possible_key)
    }

    /// Check that the key starts with the given slice.
    pub fn starts_with(&self, key: &[u8]) -> bool
    where
        K: AsBytes,
    {
        self.key.as_bytes().starts_with(key)
    }

    /// This function removes this leaf node from its linked list.
    ///
    /// # Safety
    ///
    /// This function requires that no other operation is concurrently modifying
    /// or reading the `this_ptr` leaf node and its sibling leaf nodes.
    pub unsafe fn remove_self(this_ptr: NodePtr<PREFIX_LEN, Self>) {
        // SAFETY: Covered by safety doc of this function
        let this = unsafe { this_ptr.as_mut() };

        if let Some(sibling_ptr) = this.previous {
            // SAFETY: Covered by safety doc of this function
            let sibling = unsafe { sibling_ptr.as_mut() };
            sibling.next = this.next;
        }

        if let Some(sibling_ptr) = this.next {
            // SAFETY: Covered by safety doc of this function
            let sibling = unsafe { sibling_ptr.as_mut() };
            sibling.previous = this.previous;
        }

        // Normally this is where I would reset the `previous`/`next` pointers
        // to `None`, but it is useful in the delete case to keep this
        // information around.
    }

    /// Create a copy of this leaf node with the sibling references removed.
    pub fn clone_without_siblings(&self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Self {
            value: self.value.clone(),
            key: self.key.clone(),
            // We override the default clone behavior to wipe these values out, since its unlikely
            // that the cloned leaf should point to the old linked list of leaves
            previous: None,
            next: None,
        }
    }
}

impl<const PREFIX_LEN: usize, K, V> Node<PREFIX_LEN> for LeafNode<K, V, PREFIX_LEN> {
    type Key = K;
    type Value = V;

    const TYPE: NodeType = NodeType::Leaf;
}

#[cfg(test)]
mod tests {
    use std::boxed::Box;

    use super::*;
    use crate::{raw::representation::OpaqueValue, tagged_pointer::TaggedPointer};

    // This test is important because it verifies that we can transform a tagged
    // pointer to a type with large and small alignment and back without issues.
    #[test]
    fn leaf_node_alignment() {
        let mut p0 = TaggedPointer::<OpaqueValue, 3>::new(
            Box::into_raw(Box::<LeafNode<[u8; 0], _, 16>>::new(
                LeafNode::with_no_siblings([], 3u8),
            ))
            .cast::<OpaqueValue>(),
        )
        .unwrap();
        p0.set_data(0b001);

        #[repr(align(64))]
        struct LargeAlignment;

        let mut p1 = TaggedPointer::<OpaqueValue, 3>::new(
            Box::into_raw(Box::<LeafNode<LargeAlignment, _, 16>>::new(
                LeafNode::with_no_siblings(LargeAlignment, 2u16),
            ))
            .cast::<OpaqueValue>(),
        )
        .unwrap();
        p1.set_data(0b011);

        let mut p2 = TaggedPointer::<OpaqueValue, 3>::new(
            Box::into_raw(Box::<LeafNode<_, LargeAlignment, 16>>::new(
                LeafNode::with_no_siblings(1u64, LargeAlignment),
            ))
            .cast::<OpaqueValue>(),
        )
        .unwrap();
        p2.set_data(0b111);

        unsafe {
            // These tests apparently leak memory in Miri's POV unless we explicitly cast
            // them back to the original type when we deallocate. The `.cast` calls
            // are required, even though the tests pass under normal execution otherwise (I
            // guess normal test execution doesn't care about leaked memory?)
            drop(Box::from_raw(
                p0.to_ptr().cast::<LeafNode<[u8; 0], u8, 16>>().as_ptr(),
            ));
            drop(Box::from_raw(
                p1.to_ptr()
                    .cast::<LeafNode<LargeAlignment, u16, 16>>()
                    .as_ptr(),
            ));
            drop(Box::from_raw(
                p2.to_ptr()
                    .cast::<LeafNode<u64, LargeAlignment, 16>>()
                    .as_ptr(),
            ));
        }
    }
}
