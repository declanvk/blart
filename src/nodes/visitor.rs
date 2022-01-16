//! Utilities for inspecting the trie structure.

mod pretty_printer;

use crate::{
    InnerNode16, InnerNode256, InnerNode4, InnerNode48, InnerNodePtr, LeafNode, NodePtr,
    OpaqueNodePtr, TaggedNode,
};
pub use pretty_printer::*;

/// The `Visitable` trait allows [`Visitor`]s to traverse the structure of the
/// implementing type and produce some output.
pub trait Visitable<T> {
    /// This function provides the default traversal behavior for the
    /// implementing type.
    ///
    /// The implementation should call `visit_with(visitor)` for all relevant
    /// sub-fields of the type. If there are no relevant sub-fields, it should
    /// just produce the default output.
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output;

    /// This function will traverse the implementing type and execute any
    /// specific logic from the given [`Visitor`].
    ///
    /// This function should be override for types that have corresponding hooks
    /// in the [`Visitor`] trait. For example the [`Visitable`] implementation
    /// for [`InnerNode4`] looks like:
    ///
    /// ```rust,compile_fail
    /// impl<T> Visitable<T> for InnerNode4<T> {
    ///     ...
    ///  
    ///     fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
    ///         visitor.visit_node4(self)
    ///     }
    /// }
    /// ```
    ///
    /// The call to `visitor.visit_node4(self)` allows the visitor to execute
    /// specific handling logic.
    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        self.super_visit_with(visitor)
    }
}

impl<T> Visitable<T> for OpaqueNodePtr<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        match self.to_node_ptr() {
            InnerNodePtr::Node4(inner) => inner.visit_with(visitor),
            InnerNodePtr::Node16(inner) => inner.visit_with(visitor),
            InnerNodePtr::Node48(inner) => inner.visit_with(visitor),
            InnerNodePtr::Node256(inner) => inner.visit_with(visitor),
            InnerNodePtr::LeafNode(inner) => inner.visit_with(visitor),
        }
    }
}

impl<T, N: TaggedNode + Visitable<T>> Visitable<T> for NodePtr<N> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        let inner = self.read();
        inner.visit_with(visitor)
    }
}

impl<T> Visitable<T> for InnerNode4<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node4(self)
    }
}

impl<T> Visitable<T> for InnerNode16<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node16(self)
    }
}

impl<T> Visitable<T> for InnerNode48<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node48(self)
    }
}

impl<T> Visitable<T> for InnerNode256<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        combine_inner_node_child_output(self.iter(), visitor)
    }

    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_node256(self)
    }
}

impl<T> Visitable<T> for LeafNode<T> {
    fn super_visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor<T>>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_leaf(self)
    }
}

/// The `Visitor` trait allows creating new operations on the radix tree by
/// overriding specific handling methods for each of the node types.
pub trait Visitor<V>: Sized {
    /// The type of value that the visitor produces.
    type Output;

    /// Produce the default value of the [`Self::Output`] type.
    fn default_output(&self) -> Self::Output;

    /// Combine two instances of the [`Self::Output`] type for this [`Visitor`].
    fn combine_output(&self, o1: Self::Output, o2: Self::Output) -> Self::Output;

    /// Visit a [`InnerNode4`].
    fn visit_node4(&mut self, t: &InnerNode4<V>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode16`].
    fn visit_node16(&mut self, t: &InnerNode16<V>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode48`].
    fn visit_node48(&mut self, t: &InnerNode48<V>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`InnerNode256`].
    fn visit_node256(&mut self, t: &InnerNode256<V>) -> Self::Output {
        t.super_visit_with(self)
    }

    /// Visit a [`LeafNode`].
    fn visit_leaf(&mut self, t: &LeafNode<V>) -> Self::Output {
        t.super_visit_with(self)
    }
}

fn combine_inner_node_child_output<T, V: Visitor<T>>(
    mut iter: impl Iterator<Item = (u8, OpaqueNodePtr<T>)>,
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
