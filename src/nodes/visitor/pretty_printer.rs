use crate::{Header, NodeType, OpaqueNodePtr};

use super::{Visitable, Visitor};
use std::{
    fmt::Display,
    io::{self, Write},
};

/// A visitor the the radix trie that will print the tree in "dot" notation.
///
/// See ['DOT Language | Graphviz'](https://graphviz.org/doc/info/lang.html) for
/// information about syntax and example of the language.
pub struct DotPrinter<O: Write> {
    output: O,
    next_id: usize,
}

impl<O: Write> DotPrinter<O> {
    /// Write the dot-format of the given tree to the given output.
    pub fn print_tree<V: Display>(output: O, tree: &OpaqueNodePtr<V>) -> io::Result<()> {
        let mut visitor = DotPrinter { output, next_id: 0 };

        visitor.output_prelude()?;
        let _ = tree.visit_with(&mut visitor)?;
        visitor.output_epilogue()
    }

    fn output_prelude(&mut self) -> io::Result<()> {
        writeln!(self.output, "strict digraph G {{")?;
        writeln!(self.output, "node [shape=record]")
    }

    fn output_epilogue(&mut self) -> io::Result<()> {
        writeln!(self.output, "}}")
    }

    fn get_id(&mut self) -> usize {
        let new_id = self.next_id;
        self.next_id += 1;
        new_id
    }

    fn write_node<T: Display, IT: Iterator<Item = (u8, OpaqueNodePtr<T>)>>(
        &mut self,
        node_type: NodeType,
        header: &Header,
        to_children: impl Fn() -> IT,
    ) -> io::Result<usize> {
        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        write!(
            self.output,
            "{{<h0> {:?} | {:?} | {:?}}} | {{",
            node_type,
            header.prefix_size(),
            header.read_prefix()
        )?;
        // write child line
        for (idx, (key_fragment, _)) in to_children().enumerate() {
            if idx == 0 {
                write!(self.output, "<c{idx}> {key_fragment}")?;
            } else {
                write!(self.output, "| <c{idx}> {key_fragment}")?;
            }
        }
        writeln!(self.output, "}}}}\"]")?;

        // write all the edges

        for (key_frag_id, (_, child)) in to_children().enumerate() {
            let child_id = child.visit_with(self)?;

            writeln!(self.output, "n{node_id}:c{key_frag_id} -> n{child_id}:h0")?;
        }

        Ok(node_id)
    }
}

impl<T: Display, O: Write> Visitor<T> for DotPrinter<O> {
    type Output = io::Result<usize>;

    fn default_output(&self) -> Self::Output {
        unimplemented!("this visitor should never use the default output")
    }

    fn combine_output(&self, _: Self::Output, _: Self::Output) -> Self::Output {
        unimplemented!("this visitor should never combine outputs")
    }

    fn visit_node4(&mut self, t: &crate::InnerNode4<T>) -> Self::Output {
        self.write_node(NodeType::Node4, &t.header, || {
            // SAFETY: This iterator lives only for the lifetime of this function, which
            // does not mutate the `InnerNode4` (guaranteed by reference).
            unsafe { crate::InnerBlockNodeIter::new(t) }
        })
    }

    fn visit_node16(&mut self, t: &crate::InnerNode16<T>) -> Self::Output {
        self.write_node(NodeType::Node16, &t.header, || {
            // SAFETY: This iterator lives only for the lifetime of this function, which
            // does not mutate the `InnerNode4` (guaranteed by reference).
            unsafe { crate::InnerBlockNodeIter::new(t) }
        })
    }

    fn visit_node48(&mut self, t: &crate::InnerNode48<T>) -> Self::Output {
        self.write_node(NodeType::Node48, &t.header, || {
            // SAFETY: This iterator lives only for the lifetime of this function, which
            // does not mutate the `InnerNode4` (guaranteed by reference).
            unsafe { crate::InnerNode48Iter::new(t) }
        })
    }

    fn visit_node256(&mut self, t: &crate::InnerNode256<T>) -> Self::Output {
        self.write_node(NodeType::Node256, &t.header, || {
            // SAFETY: This iterator lives only for the lifetime of this function, which
            // does not mutate the `InnerNode4` (guaranteed by reference).
            unsafe { crate::InnerNode256Iter::new(t) }
        })
    }

    fn visit_leaf(&mut self, t: &crate::LeafNode<T>) -> Self::Output {
        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        writeln!(
            self.output,
            "{{<h0> {:?}}} | {{{}}}}}\"]",
            NodeType::Leaf,
            t.value
        )?;

        Ok(node_id)
    }
}
