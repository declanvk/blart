#![no_main]

use blart::{
    deallocate_tree, insert_unchecked, maximum_unchecked, minimum_unchecked, search_unchecked,
    LeafNode, NodePtr, OpaqueNodePtr, TrieRangeFullIter,
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
                            assert_eq!(search_value.read().value, next_value);

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
                    if let Some(leaf) = search_result {
                        let leaf = leaf.read();
                        assert!(leaf.value < next_value);
                    }
                }
            },
            Action::MinimumMaximumAndIterator => {
                if let Some(root) = current_root {
                    let min_value = unsafe { minimum_unchecked(root) }
                        .expect("A non-empty tree should have a minimum");
                    let max_value = unsafe { maximum_unchecked(root) }
                        .expect("A non-empty tree should have a maximum");
                    let mut iterator = unsafe { TrieRangeFullIter::new(root) }
                        .map_err(|mut it| it.next().unwrap());
                    let min_value_from_iter = iterator
                        .as_mut()
                        .map(|it| it.next().unwrap())
                        .unwrap_or_else(|leaf| *leaf);
                    let max_value_from_iter = iterator
                        .map(|mut it| it.next_back().unwrap())
                        .unwrap_or_else(|leaf| leaf);

                    let min_value = unsafe { min_value.as_ref() };
                    let max_value = unsafe { max_value.as_ref() };

                    assert!(min_value.key <= max_value.key);

                    assert_eq!(min_value.key.as_ref() as *const _, min_value_from_iter.0);
                    assert_eq!(max_value.key.as_ref() as *const _, max_value_from_iter.0);
                }
            },
            Action::Deallocate => {
                if let Some(root) = current_root {
                    unsafe { deallocate_tree(root) };

                    current_root = None;
                }
            },
        }
    }

    if let Some(root) = current_root {
        unsafe { deallocate_tree(root) };
    }
});
