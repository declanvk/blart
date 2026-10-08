use crate::{
    raw::{optimistic_descent, Descent, DescentEnd, NoPath, OpaqueNodePtr, OptionalLeafPtr},
    AsBytes,
};

/// Search in the given tree for the value stored with the given key.
///
/// This uses an [`optimistic_descent`], which skips inner node prefixes longer
/// than `PREFIX_LEN`. Any skipped bytes are checked by the final comparison
/// against the leaf key.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`. This function will arbitrarily read to any child in the given tree.
#[inline]
pub unsafe fn search_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> OptionalLeafPtr<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    // SAFETY: Covered by the safety requirements of this function
    let Descent {
        end,
        depth,
        unverified_from,
        ..
    } = unsafe { optimistic_descent::<_, _, _, NoPath>(root, key_bytes) };

    // If the search stopped at an inner node, then the key is not in the tree,
    // whether or not the skipped prefix bytes match
    let DescentEnd::Leaf(leaf_ptr) = end else {
        return None;
    };

    // SAFETY: The shared reference is bounded to this function and there are no
    // concurrent modifications, by the safety conditions of this function.
    let leaf_bytes = unsafe { leaf_ptr.as_key_ref() }.as_bytes();

    // All key bytes before this point have been compared on the way to the leaf.
    // It is limited by the lengths so that it will at most produce an empty slice.
    let compare_from = unverified_from
        .unwrap_or(depth)
        .min(leaf_bytes.len())
        .min(key_bytes.len());

    if leaf_bytes[compare_from..] == key_bytes[compare_from..] {
        Some(leaf_ptr)
    } else {
        None
    }
}

/// Search in the given tree for the value stored with the key that prefixes the
/// `key_bytes`
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`. This function will arbitrarily read to any child in the given tree.
pub unsafe fn prefix_search_unchecked<K, V, const PREFIX_LEN: usize>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> OptionalLeafPtr<K, V, PREFIX_LEN>
where
    K: AsBytes,
{
    // SAFETY: Covered by the safety requirements of this function
    let Descent {
        end,
        depth,
        unverified_from,
        ..
    } = unsafe { optimistic_descent::<_, _, _, NoPath>(root, key_bytes) };

    // If the search stopped at an inner node, then all the keys in its subtree are
    // longer than the key or differ from it, so none of them can be a prefix of it
    let DescentEnd::Leaf(leaf_ptr) = end else {
        return None;
    };

    // SAFETY: The shared reference is bounded to this function and there are no
    // concurrent modifications, by the safety conditions of this function.
    let leaf_bytes = unsafe { leaf_ptr.as_key_ref() }.as_bytes();

    // All key bytes before this point have been compared on the way to the leaf.
    // It is limited by the lengths so that it will at most produce an empty slice.
    let compare_from = unverified_from
        .unwrap_or(depth)
        .min(leaf_bytes.len())
        .min(key_bytes.len());

    if key_bytes[compare_from..].starts_with(&leaf_bytes[compare_from..]) {
        Some(leaf_ptr)
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
