//! Utilities for inspecting the trie structure.

mod pretty_printer;
mod tree_stats;
mod well_formed;

use crate::{
    ConcreteNodePtr, InnerNode, InnerNode16, InnerNode256, InnerNode4, InnerNode48, LeafNode, Node,
    NodePtr, OpaqueNodePtr,
};
pub use pretty_printer::*;
pub use tree_stats::*;
pub use well_formed::*;

/// The `Visitable` trait allows [`Visitor`]s to traverse the structure of the
/// implementing type and produce some output.
pub trait Visitable<K, T, const PREFIX_LEN: usize> {
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
    ///         visitor.visit_node4(self)
    ///     }
    /// }
    /// ```
    ///
    /// The call to `visitor.visit_node4(self)` allows the visitor to execute
    /// specific handling logic.
    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        self.super_visit_with(visitor)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN>
    for OpaqueNodePtr<K, T, PREFIX_LEN>
{
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        match self.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node16(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node48(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node256(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::LeafNode(inner) => inner.visit_with(visitor),
        }
    }
}

impl<K, T, const PREFIX_LEN: usize, N: Node<PREFIX_LEN> + Visitable<K, T, PREFIX_LEN>>
    Visitable<K, T, PREFIX_LEN> for NodePtr<PREFIX_LEN, N>
{
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        // FIXME: This is broken in a couple ways:
        //  1. The `read` function likely needs to be marked unsafe, since it does not
        //     have any guarantees around concurrent reads or modification
        //  2. The `Visitor`/`Visitable` trait methods likely all need to be marked
        //     unsafe, since they are operating on the raw nodes of the tree. The
        //     visitor implementations so far include "Safety" doc-comments requiring
        //     read-only access, but it probably should be recorded in the function
        //     signature
        let inner = self.read();
        inner.visit_with(visitor)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode4<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node4(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode16<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node16(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode48<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node48(self)
    }
}

impl<K, T, const PREFIX_LEN: usize> Visitable<K, T, PREFIX_LEN> for InnerNode256<K, T, PREFIX_LEN> {
    fn super_visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, PREFIX_LEN>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node256(self)
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
pub trait Visitor<K, V, const PREFIX_LEN: usize>: Sized {
    /// The type of value that the visitor produces.
    type Output;

    /// Produce the default value of the [`Self::Output`] type.
    fn default_output(&self) -> Self::Output;

    /// Combine two instances of the [`Self::Output`] type for this [`Visitor`].
    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output;

    /// Visit a [`InnerNode4`].
    fn visit_node4(&mut self, t: &InnerNode4<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode16`].
    fn visit_node16(&mut self, t: &InnerNode16<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode48`].
    fn visit_node48(&mut self, t: &InnerNode48<K, V, PREFIX_LEN>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode256`].
    fn visit_node256(&mut self, t: &InnerNode256<K, V, PREFIX_LEN>) -> Self::Output {
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
