//! Utilities for inspecting the trie structure.

mod pretty_printer;
mod tree_stats;
mod well_formed;

use crate::{
    header::NodeHeader, AsBytes, ConcreteNodePtr, InnerNode, InnerNode16, InnerNode256, InnerNode4,
    InnerNode48, LeafNode, Node, NodePtr, OpaqueNodePtr,
};
pub use pretty_printer::*;
pub use tree_stats::*;
pub use well_formed::*;

/// The `Visitable` trait allows [`Visitor`]s to traverse the structure of the
/// implementing type and produce some output.
pub trait Visitable<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>> {
    /// This function provides the default traversal behavior for the
    /// implementing type.
    ///
    /// The implementation should call `visit_with(visitor)` for all relevant
    /// sub-fields of the type. If there are no relevant sub-fields, it should
    /// just produce the default output.
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V)
        -> V::Output;

    /// This function will traverse the implementing type and execute any
    /// specific logic from the given [`Visitor`].
    ///
    /// This function should be override for types that have corresponding hooks
    /// in the [`Visitor`] trait. For example the [`Visitable`] implementation
    /// for [`InnerNode4`] looks like:
    ///
    /// ```rust,compile_fail
    /// impl<K, T, H> Visitable<K, T, NUM_PREFIX_BYTES, H> for InnerNode4<K, T, H> {
    ///     ...
    ///  
    ///     fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
    ///         visitor.visit_node4(self)
    ///     }
    /// }
    /// ```
    ///
    /// The call to `visitor.visit_node4(self)` allows the visitor to execute
    /// specific handling logic.
    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        self.super_visit_with(visitor)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for OpaqueNodePtr<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        match self.to_node_ptr() {
            ConcreteNodePtr::Node4(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node16(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node48(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::Node256(inner) => inner.visit_with(visitor),
            ConcreteNodePtr::LeafNode(inner) => inner.visit_with(visitor),
        }
    }
}

impl<
        K: AsBytes,
        T,
        const NUM_PREFIX_BYTES: usize,
        H: NodeHeader<NUM_PREFIX_BYTES>,
        N: Node<NUM_PREFIX_BYTES> + Visitable<K, T, NUM_PREFIX_BYTES, H>,
    > Visitable<K, T, NUM_PREFIX_BYTES, H> for NodePtr<NUM_PREFIX_BYTES, N>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        let inner = self.read();
        inner.visit_with(visitor)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for InnerNode4<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node4(self)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for InnerNode16<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node16(self)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for InnerNode48<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node48(self)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for InnerNode256<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node256(self)
    }
}

impl<K: AsBytes, T, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>
    Visitable<K, T, NUM_PREFIX_BYTES, H> for LeafNode<K, T, NUM_PREFIX_BYTES, H>
{
    fn super_visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(
        &self,
        visitor: &mut V,
    ) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor<K, T, NUM_PREFIX_BYTES, H>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_leaf(self)
    }
}

/// The `Visitor` trait allows creating new operations on the radix tree by
/// overriding specific handling methods for each of the node types.
pub trait Visitor<K: AsBytes, V, const NUM_PREFIX_BYTES: usize, H: NodeHeader<NUM_PREFIX_BYTES>>:
    Sized
{
    /// The type of value that the visitor produces.
    type Output;

    /// Produce the default value of the [`Self::Output`] type.
    fn default_output(&self) -> Self::Output;

    /// Combine two instances of the [`Self::Output`] type for this [`Visitor`].
    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output;

    /// Visit a [`InnerNode4`].
    fn visit_node4(&mut self, t: &InnerNode4<K, V, NUM_PREFIX_BYTES, H>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode16`].
    fn visit_node16(&mut self, t: &InnerNode16<K, V, NUM_PREFIX_BYTES, H>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode48`].
    fn visit_node48(&mut self, t: &InnerNode48<K, V, NUM_PREFIX_BYTES, H>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode256`].
    fn visit_node256(&mut self, t: &InnerNode256<K, V, NUM_PREFIX_BYTES, H>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`LeafNode`].
    fn visit_leaf(&mut self, t: &LeafNode<K, V, NUM_PREFIX_BYTES, H>) -> Self::Output {
        t.super_visit_with(self)
    }
}

fn combine_inner_node_child_output<
    K: AsBytes,
    T,
    const NUM_PREFIX_BYTES: usize,
    H: NodeHeader<NUM_PREFIX_BYTES>,
    V: Visitor<K, T, NUM_PREFIX_BYTES, H>,
>(
    mut iter: impl Iterator<Item = (u8, OpaqueNodePtr<K, T, NUM_PREFIX_BYTES, H>)>,
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
