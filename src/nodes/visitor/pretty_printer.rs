use crate::{
    visitor::{Visitable, Visitor},
    InnerNode, NodeType, OpaqueNodePtr,
};
use std::{
    fmt::Display,
    io::{self, Write},
};

/// Settings which customize the output of the [`DotPrinter`] visitor.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DotPrinterSettings {
    /// Add node address to output in graphs
    pub display_node_address: bool,
}

/// A visitor of the radix trie that will print the tree in "dot" notation.
///
/// See ['DOT Language | Graphviz'](https://graphviz.org/doc/info/lang.html) for
/// information about syntax and example of the language.
pub struct DotPrinter<O: Write> {
    output: O,
    next_id: usize,
    settings: DotPrinterSettings,
}

impl<O: Write> DotPrinter<O> {
    /// Write the dot-format of the given tree to the given output.
    ///
    /// # Safety
    ///  - For the duration of this function, the given node and all its
    ///    children nodes must not get mutated.
    pub unsafe fn print_tree<V: Display>(
        output: O,
        tree: &OpaqueNodePtr<V>,
        settings: DotPrinterSettings,
    ) -> io::Result<()> {
        let mut visitor = DotPrinter {
            output,
            next_id: 0,
            settings,
        };

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

    fn write_inner_node<T: Display, N: InnerNode<Value = T>>(
        &mut self,
        inner_node: &N,
    ) -> io::Result<usize> {
        let header = inner_node.header();
        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        if self.settings.display_node_address {
            write!(
                self.output,
                "{{<h0> {:p}}}  | {{{:?} | {:?} | {:?}}} | {{",
                inner_node as *const _,
                N::TYPE,
                header.prefix_size(),
                header.read_prefix()
            )?;
        } else {
            write!(
                self.output,
                "{{<h0> {:?} | {:?} | {:?}}} | {{",
                N::TYPE,
                header.prefix_size(),
                header.read_prefix()
            )?;
        }

        // SAFETY: The `child_it` does not live beyond the following loop and will not
        // overlap with any mutating access or operation, which is guaranteed by the
        // `print_tree` caller requirements.
        let child_it = unsafe { inner_node.iter() };
        for (idx, (key_fragment, _)) in child_it.enumerate() {
            if idx == 0 {
                write!(self.output, "<c{idx}> {key_fragment}")?;
            } else {
                write!(self.output, "| <c{idx}> {key_fragment}")?;
            }
        }
        writeln!(self.output, "}}}}\"]")?;

        // SAFETY: The `child_it` does not live beyond the following loop and will not
        // overlap with any mutating access or operation, which is guaranteed by the
        // `print_tree` caller requirements.
        let child_it = unsafe { inner_node.iter() };
        for (key_frag_id, (_, child)) in child_it.enumerate() {
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
        self.write_inner_node(t)
    }

    fn visit_node16(&mut self, t: &crate::InnerNode16<T>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_node48(&mut self, t: &crate::InnerNode48<T>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_node256(&mut self, t: &crate::InnerNode256<T>) -> Self::Output {
        self.write_inner_node(t)
    }

    fn visit_leaf(&mut self, t: &crate::LeafNode<T>) -> Self::Output {
        let node_id = self.get_id();
        write!(self.output, "n{node_id} ")?;
        write!(self.output, "[label=\"{{")?;
        // write header line
        if self.settings.display_node_address {
            writeln!(
                self.output,
                "{{<h0> {:p}}} | {{{:?}}} | {{{:?}}} | {{{}}}}}\"]",
                t as *const _,
                NodeType::Leaf,
                t.key,
                t.value
            )?;
        } else {
            writeln!(
                self.output,
                "{{<h0> {:?}}} | {{{:?}}} | {{{}}}}}\"]",
                NodeType::Leaf,
                t.key,
                t.value
            )?;
        }

        Ok(node_id)
    }
}

#[cfg(test)]
mod tests {
    use crate::deallocate_tree;

    use super::*;

    #[test]
    fn simple_tree_output_to_dot() {
        let root = crate::tests_common::setup_tree_from_entries(
            crate::tests_common::generate_key_fixed_length([3, 3])
                .enumerate()
                .map(|(a, b)| (b, a)),
        );
        let mut buffer = Vec::new();

        // SAFETY: There are no concurrent mutation to the tree node or its children
        unsafe {
            DotPrinter::print_tree(
                &mut buffer,
                &root,
                DotPrinterSettings {
                    display_node_address: false,
                },
            )
            .unwrap()
        };

        let output = String::from_utf8(buffer).unwrap();
        assert_eq!(
            output,
            "strict digraph G {
node [shape=record]
n0 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 85| <c2> 170| <c3> 255}}\"]
n1 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 85| <c2> 170| <c3> 255}}\"]
n2 [label=\"{{<h0> Leaf} | {[0, 0]} | {0}}\"]
n1:c0 -> n2:h0
n3 [label=\"{{<h0> Leaf} | {[0, 85]} | {1}}\"]
n1:c1 -> n3:h0
n4 [label=\"{{<h0> Leaf} | {[0, 170]} | {2}}\"]
n1:c2 -> n4:h0
n5 [label=\"{{<h0> Leaf} | {[0, 255]} | {3}}\"]
n1:c3 -> n5:h0
n0:c0 -> n1:h0
n6 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 85| <c2> 170| <c3> 255}}\"]
n7 [label=\"{{<h0> Leaf} | {[85, 0]} | {4}}\"]
n6:c0 -> n7:h0
n8 [label=\"{{<h0> Leaf} | {[85, 85]} | {5}}\"]
n6:c1 -> n8:h0
n9 [label=\"{{<h0> Leaf} | {[85, 170]} | {6}}\"]
n6:c2 -> n9:h0
n10 [label=\"{{<h0> Leaf} | {[85, 255]} | {7}}\"]
n6:c3 -> n10:h0
n0:c1 -> n6:h0
n11 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 85| <c2> 170| <c3> 255}}\"]
n12 [label=\"{{<h0> Leaf} | {[170, 0]} | {8}}\"]
n11:c0 -> n12:h0
n13 [label=\"{{<h0> Leaf} | {[170, 85]} | {9}}\"]
n11:c1 -> n13:h0
n14 [label=\"{{<h0> Leaf} | {[170, 170]} | {10}}\"]
n11:c2 -> n14:h0
n15 [label=\"{{<h0> Leaf} | {[170, 255]} | {11}}\"]
n11:c3 -> n15:h0
n0:c2 -> n11:h0
n16 [label=\"{{<h0> Node4 | 0 | []} | {<c0> 0| <c1> 85| <c2> 170| <c3> 255}}\"]
n17 [label=\"{{<h0> Leaf} | {[255, 0]} | {12}}\"]
n16:c0 -> n17:h0
n18 [label=\"{{<h0> Leaf} | {[255, 85]} | {13}}\"]
n16:c1 -> n18:h0
n19 [label=\"{{<h0> Leaf} | {[255, 170]} | {14}}\"]
n16:c2 -> n19:h0
n20 [label=\"{{<h0> Leaf} | {[255, 255]} | {15}}\"]
n16:c3 -> n20:h0
n0:c3 -> n16:h0
}
"
        );

        unsafe { deallocate_tree(root) };
    }
}
