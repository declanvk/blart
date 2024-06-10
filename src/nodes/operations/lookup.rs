use std::borrow::Borrow;

use crate::{AsBytes, ConcreteNodePtr, InnerNode, LeafNode, NodePtr, OpaqueNodePtr};

/// Search in the given tree for the value stored with the given key.
///
/// # Safety
///
///  - This function cannot be called concurrently with any mutating operation
///    on `root` or any child node of `root`. This function will arbitrarily
///    read to any child in the given tree.
pub unsafe fn search_unchecked<Q, K, V>(
    root: OpaqueNodePtr<K, V>,
    key: &Q,
) -> Option<NodePtr<LeafNode<K, V>>>
where
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
{
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        current_node = match current_node.to_node_ptr() {
            ConcreteNodePtr::Node4(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node16(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node48(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::Node256(inner_ptr) => unsafe {
                // SAFETY: The safety requirement is covered by the safety requirement on the
                // containing function
                check_prefix_lookup_child(inner_ptr, key, &mut current_depth)
            },
            ConcreteNodePtr::LeafNode(leaf_node_ptr) => {
                let leaf_node = leaf_node_ptr.read();

                // Specifically we are matching the leaf node stored key against the full search
                // key to confirm that it is the right value.
                if leaf_node.matches_full_key(key) {
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
///
///  - No other access or mutation to the `inner_ptr` Node can happen while this
///    function runs.
pub(crate) unsafe fn check_prefix_lookup_child<Q, K, V, N>(
    inner_ptr: NodePtr<N>,
    key: &Q,
    current_depth: &mut usize,
) -> Option<OpaqueNodePtr<K, V>>
where
    N: InnerNode<Key = K, Value = V>,
    K: Borrow<Q> + AsBytes,
    Q: AsBytes + ?Sized,
{
    let key_bytes = key.as_bytes();

    // SAFETY: The lifetime produced from this is bounded to this scope and does not
    // escape. Further, no other code mutates the node referenced, which is further
    // enforced the "no concurrent reads or writes" requirement on the
    // `search_unchecked` function.
    let inner_node = unsafe { inner_ptr.as_ref() };
    let header = inner_node.header();
    let matched_prefix_size = header.match_prefix(&key_bytes[*current_depth..]);
    if matched_prefix_size != header.prefix_len() {
        return None;
    }

    // Since the prefix matched, advance the depth by the size of the prefix
    *current_depth += matched_prefix_size;

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
}

#[cfg(test)]
mod tests;
