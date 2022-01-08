use super::*;
use crate::NodeType;

#[test]
fn tests_insert_small_trees() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let new_leaf = LeafNode::new(Box::new([1, 2, 5, 6]), "1256".to_string());

    let tree = &mut first_leaf.to_opaque();
    unsafe { insert(tree, new_leaf) };

    assert_eq!(tree.read().node_type, NodeType::Node4);

    let new_root = tree.cast::<InnerNode4<String>>().unwrap();

    for (_, leaf_node) in new_root.read().iter() {
        let leaf_node = leaf_node.cast::<LeafNode<String>>().unwrap();

        unsafe { NodePtr::deallocate_node(leaf_node) }
    }

    unsafe { NodePtr::deallocate_node(new_root) }
}
