#![no_main]

use blart::{
    deallocate_tree, delete_unchecked, insert_unchecked, maximum_unchecked, minimum_unchecked,
    search_unchecked, visitor::WellFormedChecker, InsertResult, LeafNode, NodePtr, OpaqueNodePtr,
    TreeIterator,
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
    MinimumMaximumAndIterator,
    Deallocate,
    Delete {
        // the key to delete
        key: Box<[u8]>,
    },
    WellFormedCheck,
}

libfuzzer_sys::fuzz_target!(|actions: Vec<Action>| {
    let mut current_root: Option<OpaqueNodePtr<Box<[u8]>, usize>> = None;
    let mut next_value: usize = 0;

    for action in actions {
        match action {
            Action::Insert { key } => {
                let new_key = key.clone();
                current_root = if let Some(old_root) = current_root {
                    match unsafe { insert_unchecked(old_root, new_key, next_value) } {
                        Ok(InsertResult { new_root, .. }) => {
                            let search_value =
                                unsafe { search_unchecked(new_root, key.as_ref()).unwrap() };
                            assert_eq!(search_value.read().value, next_value);

                            Some(new_root)
                        },
                        Err(_) => Some(old_root),
                    }
                } else if !key.is_empty() {
                    Some(NodePtr::allocate_node_ptr(LeafNode::new(key, next_value)).to_opaque())
                } else {
                    None
                };

                next_value += 1;
            },
            Action::Search { key } => {
                if let Some(root) = current_root {
                    let search_result = unsafe { search_unchecked(root, key.as_ref()) };
                    if let Some(leaf) = search_result {
                        let leaf = leaf.read();
                        assert!(leaf.value < next_value);
                    }
                }
            },
            Action::MinimumMaximumAndIterator => {
                if let Some(root) = current_root {
                    let min_value = unsafe { minimum_unchecked(root) };
                    let max_value = unsafe { maximum_unchecked(root) };
                    if min_value == max_value {
                        // The tree only has a single value, min and max check is not interesting
                        continue;
                    }

                    let mut iterator = unsafe { TreeIterator::<_, _>::new(root) };
                    let min_value_from_iter = iterator.next().unwrap();
                    let max_value_from_iter = iterator.next_back().unwrap();

                    let min_value = unsafe { min_value.as_ref() };
                    let max_value = unsafe { max_value.as_ref() };

                    assert!(min_value.key <= max_value.key);

                    assert_eq!(
                        &min_value.key,
                        unsafe { min_value_from_iter.as_key_value_ref() }.0
                    );
                    assert_eq!(
                        &max_value.key,
                        unsafe { max_value_from_iter.as_key_value_ref() }.0
                    );
                }
            },
            Action::Deallocate => {
                if let Some(root) = current_root {
                    unsafe { deallocate_tree(root) };

                    current_root = None;
                }
            },
            Action::Delete { key } => {
                if let Some(root) = current_root {
                    let delete_result = unsafe { delete_unchecked(root, key.as_ref()) };

                    if let Some(delete_result) = delete_result {
                        assert_eq!(delete_result.deleted_leaf.key, key);
                        current_root = delete_result.new_root;
                    }
                }
            },
            Action::WellFormedCheck => {
                if let Some(root) = current_root {
                    let _ = unsafe { WellFormedChecker::check_tree(&root) }
                        .expect("tree should be well-formed");
                }
            },
        }
    }

    if let Some(root) = current_root {
        unsafe { deallocate_tree(root) };
    }
});
