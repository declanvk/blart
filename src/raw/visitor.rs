//! Utilities for inspecting the trie structure.

#[cfg(feature = "std")]
mod pretty_printer;
mod tree_stats;
#[cfg(feature = "std")]
mod well_formed;

#[cfg(feature = "std")]
pub use pretty_printer::*;
pub use tree_stats::*;
#[cfg(feature = "std")]
pub use well_formed::*;

use super::{
    ConcreteNodePtr, InnerNode16, InnerNode4, InnerNode48, InnerNodeDirect, LeafNode, Node,
    NodePtr, NodeType, OpaqueNodePtr,
};
use crate::raw::{match_concrete_node_ptr, InnerNode, InnerNodeCommon};

/// The kind of an inner node in the tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InnerNodeKind {
    /// Node that references between 2 and 4 children.
    Node4,
    /// Node that references between 5 and 16 children.
    Node16,
    /// Node that references between 17 and 48 children.
    Node48,
    /// Node that references between 49 and 256 children.
    Node256,
}

impl InnerNodeKind {
    /// Convert a [`NodeType`] into an [`InnerNodeKind`], returning `None` for [`NodeType::Leaf`].
    pub(crate) fn from_node_type(node_type: NodeType) -> Option<Self> {
        Some(match node_type {
            NodeType::Node4 => InnerNodeKind::Node4,
            NodeType::Node16 => InnerNodeKind::Node16,
            NodeType::Node48 => InnerNodeKind::Node48,
            NodeType::Node256 => InnerNodeKind::Node256,
            NodeType::Leaf => return None,
        })
    }

    /// Convert into [`NodeType`].
    pub(crate) fn to_node_type(self) -> NodeType {
        match self {
            InnerNodeKind::Node4 => NodeType::Node4,
            InnerNodeKind::Node16 => NodeType::Node16,
            InnerNodeKind::Node48 => NodeType::Node48,
            InnerNodeKind::Node256 => NodeType::Node256,
        }
    }
}

/// The `Visitable` trait allows [`Visitor`]s to traverse the structure of the
/// implementing type and produce some output.
pub(crate) trait Visitable<K, T, const PREFIX_LEN: usize> {
    /// This function provides the default traversal behavior for the
    /// implementing type.
    ///
    /// The implementation should call `visit_with(visitor)` for all relevant
    /// sub-fields of the type. If there are no relevant sub-fields, it should
    /// just produce the default output.
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output;

    /// This function will traverse the implementing type and execute any
    /// specific logic from the given [`Visitor`].
    ///
    /// This function should be override for types that have corresponding hooks
    /// in the [`Visitor`] trait. For example the [`Visitable`] implementation
    /// for [`InnerNode4`] looks like:
    ///
    /// ```rust,compile_fail
    /// impl<K, T> Visitable<K, T, PREFIX_LEN> for InnerNode4<K, T> {
    ///     ...
    ///
    ///     fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
    ///         visitor.visit_inner_node(self)
    ///     }
    /// }
    /// ```
    ///
    /// The call to `visitor.visit_inner_node(self)` allows the visitor to
    /// execute specific handling logic.
    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        self.super_visit_with(visitor)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN>
    for OpaqueNodePtr<K, T, PREFIX_LEN>
{
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        match_concrete_node_ptr! {
            match (self.to_node_ptr()) {
                InnerNode(inner) => inner.visit_with(visitor),
                LeafNode(inner) => inner.visit_with(visitor),
            }
        }
    }
}

impl<K, T, const PREFIX_LEN: usize, N: Node<PREFIX_LEN> + Visitable<K, T, PREFIX_LEN>>
    Visitable<K, T, PREFIX_LEN> for NodePtr<PREFIX_LEN, N>
{
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        // FIXME(https://github.com/declanvk/blart/issues/34): This is broken in a couple ways:
        //  1. The `Visitor`/`Visitable` trait methods likely all need to be marked unsafe, since
        //     they are operating on the raw nodes of the tree. The visitor implementations so far
        //     include "Safety" doc-comments requiring read-only access, but it probably should be
        //     recorded in the function signature
        //  2. The `visit_with` functions work better when they're using a reference pointing to the
        //     actual location of `N`, not a local copy on the stack. For example, the DotPrinter
        //     will attempt to print node addresses by converting the given reference into a
        //     pointer, but this only really works if the reference points to the actual node
        //     location.
        // let inner = self.read();
        // inner.visit_with(visitor)
        unsafe { self.as_ref().visit_with(visitor) }
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode4<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_inner_node(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode16<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_inner_node(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode48<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_inner_node(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN>
    for InnerNodeDirect<K, T, PREFIX_LEN>
{
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_inner_node(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for LeafNode<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_leaf(self)
    }
}

/// The `Visitor` trait allows creating new operations on the radix tree by
/// overriding specific handling methods for each of the node types.
pub(crate) trait Visitor<K, V, const PREFIX_LEN: usize>: Sized {
    /// The type of value that the visitor produces.
    type Output;

    /// Produce the default value of the [`Self::Output`] type.
    fn default_output(&self) -> Self::Output;

    /// Combine two instances of the [`Self::Output`] type for this [`Visitor`].
    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output;

    /// Visit an [`InnerNode`].
    fn visit_inner_node<N>(&mut self, t: &N) -> Self::Output
    where
        N: InnerNode<PREFIX_LEN, Key = K, Value = V> + Visitable<K, V, PREFIX_LEN>,
    {
        t.super_visit_with(self)
    }

    /// Visit a [`LeafNode`].
    fn visit_leaf(&mut self, t: &LeafNode<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self)
    }
}

fn combine_inner_node_child_output<K, T, const PREFIX_LEN: usize, V: Visitor<K, T, PREFIX_LEN>>(
    mut iter: impl Iterator<Item = (u8, OpaqueNodePtr<K, T, PREFIX_LEN>)>,
    visitor: &mut V,
) -> V::Output {
    if let Some((_, first)) = iter.next() {
        let mut accum = first.visit_with(visitor);
        for (_, child) in iter {
            let output = child.visit_with(visitor);
            accum = visitor.combine_output(accum, output);
        }

        accum
    } else {
        visitor.default_output()
    }
}
