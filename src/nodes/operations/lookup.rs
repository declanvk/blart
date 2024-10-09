use std::cmp::Ordering;

use crate::{
    AsBytes, AttemptOptimisticPrefixMatch, ConcreteNodePtr, InnerNode, LeafNode, NodePtr,
    OpaqueNodePtr, OptionalLeafPtr, PessimisticMismatch, PrefixMatch,
};

#[rustfmt::skip]
/// This enum is used to track the `match_*_prefix` state as a lookup traverses
/// the trie.
///
/// Snippet from the original ART paper:
///
/// > Path compression, the second technique, removes all inner nodes that have
/// > only a single child. In Figure 6, the inner node storing the partial key
/// > “A” was removed. Of course, this partial key cannot simply be ignored.
/// > There are two approaches to deal with it:
/// >
/// > - Pessimistic: At each inner node, a variable length (possibly empty)
/// >   partial key vector is stored. It contains the keys of all preceding
/// >   one-way nodes which have been removed. During lookup this vector is
/// >   compared to the search key before proceeding to the next child.
/// > - Optimistic: Only the count of preceding one-way nodes (equal to the
/// >   length of the vector in the pessimistic approach) is stored. Lookups just
/// >   skip this number of bytes without comparing them. Instead, when a lookup
/// >   arrives at a leaf its key must be compared to the search key to ensure
/// >   that no “wrong turn” was taken.
/// >
/// > Both approaches ensure that each inner node has at least two children. The
/// > optimistic approach is particularly beneficial for long strings but
/// > requires one additional check, while the pessimistic method uses more
/// > space, and has variable sized nodes leading to increased memory
/// > fragmentation. We therefore use a hybrid approach by storing a vector at
/// > each node like in the pessimistic approach, but with a constant size (8
/// > bytes) for all nodes. Only when this size is exceeded, the lookup
/// > algorithm dynamically switches to the optimistic strategy. Without wasting
/// > too much space or fragmenting memory, this avoids the additional check in
/// > cases that we investigated.
///
/// This enum is used to track that switch from "Pessimistic" to "Optimistic".
/// If a lookup has been [`Pessimistic`][PrefixMatchBehavior::Pessimistic],
/// then we can elide or shorten the key match check at the end. If we switch to
/// [`Optimistic`][PrefixMatchBehavior::Optimistic], then we can switch to a
/// different code path and only check the prefix length against the key.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub enum PrefixMatchBehavior {
    /// This variant indicates that all `prefix_*_match` calls have operated on
    /// entirely explicit prefix bytes.
    ///
    /// This variant is the default starting state for trie lookups.
    #[default]
    Pessimistic,
    /// This variant indicates that at least one `prefix_*_match` call has
    /// operated on implicit bytes.
    Optimistic,
}

impl PrefixMatchBehavior {
    /// This function will choose between different "match prefix" methods
    /// depending on the current behavior and attempt to match the prefix of the
    /// given inner node against the given key.
    #[inline]
    pub fn match_prefix<K, V, const PREFIX_LEN: usize>(
        &mut self,
        inner_node: &impl InnerNode<PREFIX_LEN, Key = K, Value = V>,
        key_bytes: &[u8],
    ) -> Result<AttemptOptimisticPrefixMatch, PessimisticMismatch> {
        let result = match self {
            // If we're still in the pessimistic branch we attempt to stay there
            PrefixMatchBehavior::Pessimistic => {
                inner_node.attempt_pessimistic_match_prefix(key_bytes)
            },
            // If we've hit at least one optimistic prefix check, then we can make all the prefix
            // checks optimistic
            PrefixMatchBehavior::Optimistic => inner_node
                .optimistic_match_prefix(key_bytes)
                .map(
                    |PrefixMatch { matched_bytes }| AttemptOptimisticPrefixMatch {
                        matched_bytes,
                        any_implicit_bytes: true,
                    },
                )
                .map_err(Into::into),
        };

        match &result {
            Ok(AttemptOptimisticPrefixMatch {
                any_implicit_bytes, ..
            }) if *any_implicit_bytes => {
                *self = PrefixMatchBehavior::Optimistic;
            },
            Err(PessimisticMismatch { prefix_byte, .. }) if prefix_byte.is_none() => {
                *self = PrefixMatchBehavior::Optimistic;
            },
            _ => {},
        }

        result
    }

    /// This function will compare the key bytes against the key in the given
    /// leaf node.
    ///
    /// Specifically:
    ///  - If the current behavior is "optimistic", then the entire leaf key
    ///    will be compared against the given key bytes
    ///  - If the current behavior is "pessimistic", then only the key bytes
    ///    that were not used during the lookup process will be compared against
    ///    the corresponding leaf key bytes.
    ///
    /// This is a minor optimization to reduce the amount of work needed
    /// confirming that a lookup found the right leaf node.
    pub fn compare_leaf_key<K: AsBytes, V, const PREFIX_LEN: usize>(
        self,
        leaf: &LeafNode<K, V, PREFIX_LEN>,
        key_bytes: &[u8],
        current_depth: usize,
    ) -> Ordering {
        match self {
            PrefixMatchBehavior::Pessimistic => {
                let leaf_key_bytes = leaf.key_ref().as_bytes();
                let current_depth = current_depth.min(leaf_key_bytes.len()).min(key_bytes.len());
                // PANIC SAFETY: Since we limit `current_depth` to be the minimum of the lengths
                // and the current depth we will at most get an empty slice, it
                // should panic. I ran a small test to make sure that `&[1][1..] == &[][..]` and
                // does not panic.
                let leaf_key_bytes = &leaf_key_bytes[current_depth..];
                let key_bytes = &key_bytes[current_depth..];
                leaf_key_bytes.cmp(key_bytes)
            },
            PrefixMatchBehavior::Optimistic => leaf.key_ref().as_bytes().cmp(key_bytes),
        }
    }

    /// This function will test the key bytes against the key in the given leaf
    /// node.
    ///
    /// Specifically:
    ///  - If the current behavior is "optimistic", then the entire leaf key
    ///    will be matched against the given key bytes
    ///  - If the current behavior is "pessimistic", then only the key bytes
    ///    that were not used during the lookup process will be tested against
    ///    the corresponding leaf key bytes.
    ///
    /// This is a minor optimization to reduce the amount of work needed
    /// confirming that a lookup found the right leaf node.
    pub fn matches_leaf_key<K: AsBytes, V, const PREFIX_LEN: usize>(
        self,
        leaf: &LeafNode<K, V, PREFIX_LEN>,
        key_bytes: &[u8],
        current_depth: usize,
    ) -> bool {
        match self {
            PrefixMatchBehavior::Pessimistic => {
                let leaf_key_bytes = leaf.key_ref().as_bytes();
                let current_depth = current_depth.min(leaf_key_bytes.len()).min(key_bytes.len());
                // PANIC SAFETY: Since we limit `current_depth` to be the minimum of the lengths
                // and the current depth we will at most get an empty slice, it
                // should panic. I ran a small test to make sure that `&[1][1..] == &[][..]` and
                // does not panic.
                let leaf_key_bytes = &leaf_key_bytes[current_depth..];
                let key_bytes = &key_bytes[current_depth..];
                leaf_key_bytes.eq(key_bytes)
            },
            PrefixMatchBehavior::Optimistic => leaf.matches_full_key(key_bytes),
        }
    }
}

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn search_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> OptionalLeafPtr<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    let mut current_node = root;
    let mut current_depth = 0;
    let mut prefix_match_behavior = PrefixMatchBehavior::default();

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_behavior,
                )
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_behavior,
                )
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_behavior,
                )
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut prefix_match_behavior,
                )
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                // SAFETY: The shared reference is bounded to this block and there are no
                // concurrent modifications, by the safety conditions of this function.
                let leaf = unsafe { leaf_node_ptr.as_ref() };

                if prefix_match_behavior.matches_leaf_key(leaf, key_bytes, current_depth) {
                    return Some(leaf_node_ptr);
                } else {
                    return None;
                }
            },
        }?;
    }
}

/// For the given `InnerNode`, check the node prefix, then lookup the child
/// based on the search depth.
///
/// If the prefix does not match, it returns `None`. If there is no matching
/// child for the key byte, it returns `None`.
///
/// # Safety
///  - No other access or mutation to the `inner_ptr` Node can happen while this
///    function runs.
pub(crate) unsafe fn check_prefix_lookup_child<K, V, N, const PREFIX_LEN: usize>(
    inner_ptr: NodePtr<PREFIX_LEN, N>,
    key_bytes: &[u8],
    current_depth: &mut usize,
    prefix_match_behavior: &mut PrefixMatchBehavior,
) -> Option<OpaqueNodePtr<K, V, PREFIX_LEN>>
where
    N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    K: AsBytes,
{
    // SAFETY: The lifetime produced from this is bounded to this scope and does not
    // escape. Further, no other code mutates the node referenced, which is further
    // enforced the "no concurrent reads or writes" requirement on the
    // `search_unchecked` function.
    let inner_node = unsafe { inner_ptr.as_ref() };
    let match_prefix = prefix_match_behavior.match_prefix(inner_node, &key_bytes[*current_depth..]);
    match match_prefix {
        Err(_) => None,
        Ok(AttemptOptimisticPrefixMatch { matched_bytes, .. }) => {
            // Since the prefix matched, advance the depth by the size of the prefix
            *current_depth += matched_bytes;

            let next_key_fragment = if *current_depth < key_bytes.len() {
                key_bytes[*current_depth]
            } else {
                // the key has insufficient bytes, it is a prefix of an existing key. Thus, the
                // key must not exist in the tree by the requirements of the insert function
                // (any key in the tree must not be the prefix of any other key in the tree)
                return None;
            };

            let child_lookup = inner_node.lookup_child(next_key_fragment);

            if child_lookup.is_some() {
                // Since the prefix matched and it found a child, advance the depth by 1 more
                // key byte
                *current_depth += 1;
            }

            child_lookup
        },
    }
}

#[cfg(test)]
mod tests;
