use super::*;
use crate::NodeType;

#[test]
fn insert_to_small_trees() {
    let first_leaf =
        NodePtr::allocate_node(LeafNode::new(Box::new([1, 2, 3, 4]), "1234".to_string()));

    let new_leaf = LeafNode::new(Box::new([1, 2, 5, 6]), "1256".to_string());

    let tree = &mut first_leaf.to_opaque();
    let new_leaf = unsafe { insert(tree, new_leaf) };

    assert_eq!(tree.read().node_type, NodeType::Node4);

    let new_root = tree.cast::<InnerNode4<String>>().unwrap();

    {
        let root = new_root.read();

        assert_eq!(root.header.read_prefix(), &[1, 2]);
        assert_eq!(root.lookup_child(5), Some(new_leaf.to_opaque()));
        assert_eq!(root.lookup_child(3), Some(first_leaf.to_opaque()));
        assert_eq!(root.lookup_child(1), None);
    }
    assert_eq!(
        unsafe { search(new_root.to_opaque(), &[1, 2, 5, 6]).unwrap() },
        "1256"
    );
    assert_eq!(
        unsafe { search(new_root.to_opaque(), &[1, 2, 3, 4]).unwrap() },
        "1234"
    );
    assert_eq!(unsafe { search(new_root.to_opaque(), &[1, 2, 5, 7]) }, None);
    assert_eq!(unsafe { search(new_root.to_opaque(), &[1, 2, 3, 5]) }, None);

    unsafe { deallocate_tree(new_root.to_opaque()) };
}
