#![no_main]

use blart::{
    deallocate_tree, insert_unchecked, search_unchecked, LeafNode, NodePtr, OpaqueNodePtr,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary};

#[derive(Arbitrary, Debug)]
enum Action {
    Insert {
        // the key to insert
        key: Box<[u8]>,
    },
    Search {
        // the key to perform a lookup on
        key: Box<[u8]>,
    },
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut current_root: Option<OpaqueNodePtr<usize>> = None;
    let mut next_value: usize = 0;

    for action in actions {
        match action {
            Action::Insert { key } => {
                let new_key = key.clone();
                current_root = if let Some(old_root) = current_root {
                    match unsafe { insert_unchecked(old_root, new_key, next_value) } {
                        Ok(new_root) => {
                            let search_value =
                                unsafe { search_unchecked(new_root, key.as_ref()).unwrap() };
                            assert_eq!(*search_value, next_value);

                            Some(new_root)
                        },
                        Err(_) => Some(old_root),
                    }
                } else if !key.is_empty() {
                    Some(NodePtr::allocate_node(LeafNode::new(key, next_value)).to_opaque())
                } else {
                    None
                };

                next_value += 1;
            },
            Action::Search { key } => {
                if let Some(root) = current_root {
                    let search_result = unsafe { search_unchecked(root, key.as_ref()) };
                    if let Some(value) = search_result {
                        assert!(*value < next_value);
                    }
                }
            },
        }
    }

    if let Some(root) = current_root {
        unsafe { deallocate_tree(root) };
    }
});
