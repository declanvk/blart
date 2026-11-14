//! Shared optimistic descent used by the trie operations.
//!
//! Many of the trie operations (like lookup, insert, delete, finding range bounds) need to walk
//! down to find an appropriate location based on an initial search key. This module has the shared
//! logic for that initial walk.
//!
//! The walk is "optimistic", meaning that inner node prefixes which have implicit bytes are skipped
//! without comparing them to the search key. Otherwise, for each prefix with implicit bytes, we'd
//! need to recurse down to an abitrary leaf node to find out what those missing bytes actually are.
//! This can slow down operations by a lot. Instead, the optimistic walk records the depth of the
//! first skipped byte, and then once the walk terminates, it checks all the skipped bytes against a
//! leaf. If the bytes match, then all good! Otherwise, we need to walk down from the root again to
//! find the inner node where the mismatch actually happens.

use core::ops::ControlFlow;

use crate::{
    AsBytes,
    hint::unlikely,
    raw::{
        ExplicitMismatch, InnerNode, InnerNodeCommon, LeafNode, NodePtr, OpaqueNodePtr,
        TreePathSearch, longest_common_prefix_len, match_concrete_node_ptr,
        short_common_prefix_len,
    },
};

/// Walk down the trie starting from `root`, following `key_bytes`.
///
/// Prefixes longer than `PREFIX_LEN` are skipped without comparing them, see
/// the [module docs](self) for details. If [`Descent::unverified_from`] is
/// `Some`, the caller must check the skipped bytes against a leaf before
/// relying on the result.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`. This function will arbitrarily read to any child in the given tree.
#[inline(always)]
pub(crate) unsafe fn optimistic_descent<K, V, const PREFIX_LEN: usize, P>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
) -> Descent<K, V, PREFIX_LEN, P>
where
    P: PathTracker<K, V, PREFIX_LEN>,
{
    /// Check the prefix of the given inner node and look up the child for the next
    /// key byte.
    ///
    /// On [`ControlFlow::Continue`], `current_depth` is updated to the depth of the
    /// key byte used to find the child. Otherwise, see [`DescentEnd`] for the
    /// meaning of `current_depth`.
    ///
    /// # Safety
    ///  - This function cannot be called concurrently with any mutating operation on the given
    ///    node.
    #[inline(always)]
    unsafe fn descend_inner_node<K, V, N, const PREFIX_LEN: usize>(
        inner_ptr: NodePtr<PREFIX_LEN, N>,
        key_bytes: &[u8],
        current_depth: &mut usize,
        unverified_from: &mut Option<usize>,
    ) -> ControlFlow<DescentEnd<K, V, PREFIX_LEN>, OpaqueNodePtr<K, V, PREFIX_LEN>>
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V>,
    {
        // SAFETY: The reference is bounded to this function and there are no concurrent
        // writes, covered by the safety requirements of this function
        let inner_node = unsafe { inner_ptr.as_ref() };
        let header = inner_node.header();
        let prefix_len = header.prefix_len();

        debug_assert!(*current_depth <= key_bytes.len());

        let prefix_bytes_used = if unlikely(prefix_len > PREFIX_LEN) {
            // Skip the whole prefix, the caller checks it after the descent
            unverified_from.get_or_insert(*current_depth);
            prefix_len
        } else {
            // The whole prefix is stored in the header, so it can be compared directly
            let prefix = header.read_prefix();
            let matched_bytes = short_common_prefix_len(prefix, &key_bytes[*current_depth..]);

            // `prefix.len() == prefix_len` here, since the prefix is not longer than
            // `PREFIX_LEN`
            if unlikely(matched_bytes < prefix_len) {
                return if matched_bytes == (key_bytes.len() - *current_depth) {
                    // The key ends inside the prefix
                    ControlFlow::Break(DescentEnd::KeyExhausted)
                } else {
                    ControlFlow::Break(DescentEnd::PrefixMismatch {
                        matched_bytes,
                        prefix_byte: prefix[matched_bytes],
                    })
                };
            }

            // At this point `matched_bytes == prefix_len`, but for some reason this is faster
            // on the benchmarks I was running.
            matched_bytes
        };

        let child_key_byte_depth = *current_depth + prefix_bytes_used;
        if unlikely(child_key_byte_depth >= key_bytes.len()) {
            // The key ends inside the prefix, or right after it
            return ControlFlow::Break(DescentEnd::KeyExhausted);
        }

        *current_depth = child_key_byte_depth;
        match inner_node.lookup_child(key_bytes[child_key_byte_depth]) {
            Some(child) => ControlFlow::Continue(child),
            None => ControlFlow::Break(DescentEnd::MissingChild),
        }
    }

    let mut path = P::default();
    let mut current_node = root;
    let mut current_depth = 0;
    let mut unverified_from = None;

    loop {
        let step = match_concrete_node_ptr!(match (current_node.to_node_ptr()) {
            InnerNode(inner_ptr) => unsafe {
                // SAFETY: Covered by the safety requirements of this function
                descend_inner_node(
                    inner_ptr,
                    key_bytes,
                    &mut current_depth,
                    &mut unverified_from,
                )
            },
            LeafNode(leaf_ptr) => ControlFlow::Break(DescentEnd::Leaf(leaf_ptr)),
        });

        match step {
            ControlFlow::Continue(child) => {
                path.visit_inner_node(current_node, key_bytes[current_depth]);
                current_node = child;
                // Increment by the key byte used to find the child
                current_depth += 1;
            },
            ControlFlow::Break(end) => {
                return Descent {
                    end,
                    node: current_node,
                    depth: current_depth,
                    unverified_from,
                    path,
                };
            },
        }
    }
}

/// Records the inner nodes visited by a [`optimistic_descent`].
///
/// Operations which modify the trie need the parent and grandparent of the
/// node where the search stopped, other operations can use [`NoPath`] which
/// compiles down to nothing.
pub(crate) trait PathTracker<K, V, const PREFIX_LEN: usize>: Default {
    /// Register that the search passed an inner node, taking the child at
    /// `key_byte`.
    fn visit_inner_node(&mut self, inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>, key_byte: u8);
}

impl<K, V, const PREFIX_LEN: usize> PathTracker<K, V, PREFIX_LEN>
    for TreePathSearch<K, V, PREFIX_LEN>
{
    #[inline(always)]
    fn visit_inner_node(&mut self, inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>, key_byte: u8) {
        TreePathSearch::visit_inner_node(self, inner_node, key_byte);
    }
}

/// A [`PathTracker`] which does not track anything.
#[derive(Debug, Default)]
pub(crate) struct NoPath;

impl<K, V, const PREFIX_LEN: usize> PathTracker<K, V, PREFIX_LEN> for NoPath {
    #[inline(always)]
    fn visit_inner_node(&mut self, _inner_node: OpaqueNodePtr<K, V, PREFIX_LEN>, _key_byte: u8) {}
}

/// The result of an [`optimistic_descent`].
pub(crate) struct Descent<K, V, const PREFIX_LEN: usize, P> {
    /// Why the descent stopped
    pub end: DescentEnd<K, V, PREFIX_LEN>,
    /// The node where the descent stopped. For [`DescentEnd::Leaf`], this is
    /// the leaf.
    pub node: OpaqueNodePtr<K, V, PREFIX_LEN>,
    /// The depth where the descent stopped, see [`DescentEnd`] for the exact
    /// meaning for each case.
    pub depth: usize,
    /// The depth of the first prefix byte which was skipped without comparing
    /// it to the key, if any. All key bytes on the path before this depth have
    /// been compared.
    pub unverified_from: Option<usize>,
    /// The inner nodes visited by the descent, not including
    /// [`Descent::node`].
    pub path: P,
}

/// The reason an [`optimistic_descent`] stopped.
pub(crate) enum DescentEnd<K, V, const PREFIX_LEN: usize> {
    /// The descent reached this leaf.
    ///
    /// [`Descent::depth`] is the number of key bytes used on the path to the
    /// leaf.
    Leaf(NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>),
    /// The inner node [`Descent::node`] has no child for the key byte at
    /// [`Descent::depth`].
    ///
    /// [`Descent::depth`] is the depth after the prefix of the inner node.
    MissingChild,
    /// The key ends inside the prefix of the inner node [`Descent::node`] or
    /// right after it, so there is no key byte to look up a child with.
    ///
    /// If the prefix is stored in the node header, then the key matched the
    /// prefix up to the end of the key. Otherwise the prefix was skipped and
    /// is included in the unverified bytes.
    ///
    /// [`Descent::depth`] is the depth at the start of the prefix of the inner
    /// node.
    KeyExhausted,
    /// The key differs from the prefix of the inner node [`Descent::node`],
    /// which is stored entirely in the node header.
    ///
    /// [`Descent::depth`] is the depth at the start of the prefix of the inner
    /// node.
    PrefixMismatch {
        /// The number of prefix bytes which matched the key
        matched_bytes: usize,
        /// The first prefix byte which differs from the key
        prefix_byte: u8,
    },
}

/// Return the number of leading bytes that are equal between the key and the
/// key of a leaf where a [`optimistic_descent`] stopped.
///
/// The comparison starts from the first unverified byte (or the leaf depth, if
/// nothing was skipped), since all bytes before it are known to be equal.
///
/// When nothing was skipped, only the end of the leaf key is left to compare,
/// which is usually short, so it uses [`short_common_prefix_len`]. Otherwise the
/// comparison also covers the skipped prefixes, which only happens for prefixes
/// longer than `PREFIX_LEN`, so it uses the out of line
/// [`longest_common_prefix_len`].
///
/// # Panics
///  - Panics if the start of the comparison is past the end of either key.
#[inline(always)]
pub(crate) fn leaf_common_prefix_len(
    leaf_bytes: &[u8],
    key_bytes: &[u8],
    depth: usize,
    unverified_from: Option<usize>,
) -> usize {
    match unverified_from {
        None => depth + short_common_prefix_len(&leaf_bytes[depth..], &key_bytes[depth..]),
        Some(unverified_from) => {
            unverified_from
                + longest_common_prefix_len(
                    &leaf_bytes[unverified_from..],
                    &key_bytes[unverified_from..],
                )
        },
    }
}

/// A difference between the search key and the trie which is inside an inner
/// node prefix that was skipped by an [`optimistic_descent`].
pub(crate) struct SkippedPrefixMismatch<K, V, const PREFIX_LEN: usize, P> {
    /// The inner node whose prefix contains the mismatch
    pub node: OpaqueNodePtr<K, V, PREFIX_LEN>,
    /// The depth at the start of the prefix of [`Self::node`]
    pub node_depth: usize,
    /// The length of the prefix of [`Self::node`]
    pub node_prefix_len: usize,
    /// The inner nodes on the path to [`Self::node`], not including it
    pub path: P,
    /// The depth of the first key byte which differs from the trie. This is
    /// always less than the length of the key.
    pub mismatch_depth: usize,
    /// A leaf in the subtree of [`Self::node`], which has the full prefix in
    /// its key.
    pub leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
}

impl<K: AsBytes, V, const PREFIX_LEN: usize, P> SkippedPrefixMismatch<K, V, PREFIX_LEN, P> {
    /// Describe this mismatch relative to the prefix of [`Self::node`].
    ///
    /// # Safety
    ///  - This function cannot be called concurrently with any mutating operation on the leaf.
    pub(crate) unsafe fn explicit_mismatch(
        &self,
        key_bytes: &[u8],
    ) -> ExplicitMismatch<K, V, PREFIX_LEN> {
        // SAFETY: Covered by the safety requirements of this function
        let leaf_bytes = unsafe { self.leaf_ptr.as_key_ref() }.as_bytes();

        ExplicitMismatch::new(
            &leaf_bytes[self.node_depth..],
            &key_bytes[self.node_depth..],
            self.mismatch_depth - self.node_depth,
            // The leaf is only needed when there are implicit prefix bytes to restore
            (self.node_prefix_len > PREFIX_LEN).then_some(self.leaf_ptr),
        )
    }
}

/// Check the prefix bytes skipped by an [`optimistic_descent`] (if any were
/// skipped) up to `verified_depth`, against the leaf returned by `leaf_ptr`.
///
/// `leaf_ptr` is only called when bytes were skipped. See
/// [`verify_skipped_prefixes`] for the requirements on the leaf and the
/// meaning of the result.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`.
///
/// # Panics
///  - Panics if `verified_depth` is greater than the length of the key or the leaf key.
#[inline(always)]
pub(crate) unsafe fn verify_descent<K, V, const PREFIX_LEN: usize, P>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
    unverified_from: Option<usize>,
    verified_depth: usize,
    leaf_ptr: impl FnOnce() -> NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
) -> Option<SkippedPrefixMismatch<K, V, PREFIX_LEN, P>>
where
    K: AsBytes,
    P: PathTracker<K, V, PREFIX_LEN>,
{
    let unverified_from = unverified_from?;
    // SAFETY: Covered by the safety requirements of this function
    unsafe { verify_skipped_prefixes(root, key_bytes, unverified_from, verified_depth, leaf_ptr()) }
}

/// Check the prefix bytes that were skipped by an [`optimistic_descent`], from
/// `unverified_from` up to `verified_depth`, against the key of `leaf_ptr`.
///
/// The leaf must be in the subtree of the node where the descent stopped, so
/// it shares all the prefix bytes on the search path. All the key bytes on the
/// path which were not skipped (prefixes stored in a node header, and child key
/// bytes) have already been compared, so the first difference between the key
/// and the leaf before `verified_depth` must be in a skipped prefix.
///
/// Returns `None` if the skipped bytes match, so the result of the descent is
/// correct. Otherwise, returns the location of the mismatch.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`.
///
/// # Panics
///  - Panics if `verified_depth` is greater than the length of the key or the leaf key.
#[cold]
#[inline(never)]
pub(crate) unsafe fn verify_skipped_prefixes<K, V, const PREFIX_LEN: usize, P>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
    unverified_from: usize,
    verified_depth: usize,
    leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
) -> Option<SkippedPrefixMismatch<K, V, PREFIX_LEN, P>>
where
    K: AsBytes,
    P: PathTracker<K, V, PREFIX_LEN>,
{
    // SAFETY: Covered by the safety requirements of this function
    let leaf_bytes = unsafe { leaf_ptr.as_key_ref() }.as_bytes();
    let first_mismatch = unverified_from
        + longest_common_prefix_len(
            &leaf_bytes[unverified_from..verified_depth],
            &key_bytes[unverified_from..verified_depth],
        );

    if first_mismatch >= verified_depth {
        None
    } else {
        // SAFETY: Covered by the safety requirements of this function
        Some(unsafe { locate_skipped_mismatch(root, key_bytes, first_mismatch, leaf_ptr) })
    }
}

/// Find the inner node whose prefix contains `mismatch_depth`, where the key
/// differs from the key of `leaf_ptr`.
///
/// This walks down from the root without comparing any bytes, since the key is
/// known to match the trie up to `mismatch_depth`.
///
/// # Safety
///  - This function cannot be called concurrently with any mutating operation on `root` or any
///    child node of `root`.
///
/// # Panics
///  - Panics if `mismatch_depth` is not inside an inner node prefix on the path of the key.
#[cold]
#[inline(never)]
pub(crate) unsafe fn locate_skipped_mismatch<K, V, const PREFIX_LEN: usize, P>(
    root: OpaqueNodePtr<K, V, PREFIX_LEN>,
    key_bytes: &[u8],
    mismatch_depth: usize,
    leaf_ptr: NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>,
) -> SkippedPrefixMismatch<K, V, PREFIX_LEN, P>
where
    P: PathTracker<K, V, PREFIX_LEN>,
{
    assert!(
        mismatch_depth < key_bytes.len(),
        "a mismatch in a skipped prefix must be inside the key"
    );

    let mut path = P::default();
    let mut current_node = root;
    let mut current_depth = 0;

    loop {
        let step = match_concrete_node_ptr!(match (current_node.to_node_ptr()) {
            InnerNode(inner_ptr) => {
                // SAFETY: The reference is bounded to this block and there are no concurrent
                // writes, covered by the safety requirements of this function
                let inner_node = unsafe { inner_ptr.as_ref() };
                let prefix_len = inner_node.header().prefix_len();
                if mismatch_depth < current_depth + prefix_len {
                    ControlFlow::Break(prefix_len)
                } else {
                    current_depth += prefix_len;
                    ControlFlow::Continue(
                        inner_node
                            .lookup_child(key_bytes[current_depth])
                            .expect("child must exist, it was found by the optimistic descent"),
                    )
                }
            },
            LeafNode(_leaf_ptr) => {
                panic!("the mismatch must be inside the prefix of an inner node")
            },
        });

        match step {
            ControlFlow::Continue(child) => {
                path.visit_inner_node(current_node, key_bytes[current_depth]);
                current_node = child;
                current_depth += 1;
            },
            ControlFlow::Break(node_prefix_len) => {
                return SkippedPrefixMismatch {
                    node: current_node,
                    node_depth: current_depth,
                    node_prefix_len,
                    path,
                    mismatch_depth,
                    leaf_ptr,
                };
            },
        }
    }
}

#[cfg(test)]
mod tests;
