use std::ffi::CString;

use crate::{
    raw::visitor::{TreeStats, TreeStatsCollector},
    AsBytes, TreeMap,
};

use super::*;

#[test]
fn iterators_are_send_sync() {
    fn is_send<T: Send>() {}
    fn is_sync<T: Sync>() {}

    fn fuzzy_is_send<K: Sync, V: Sync, A: Sync + Allocator>() {
        is_send::<Fuzzy<K, V, DEFAULT_PREFIX_LEN, A>>();
    }

    fn fuzzy_is_sync<K: Sync, V: Sync, A: Sync + Allocator>() {
        is_sync::<Fuzzy<K, V, DEFAULT_PREFIX_LEN, A>>();
    }

    fuzzy_is_send::<[u8; 3], usize, Global>();
    fuzzy_is_sync::<[u8; 3], usize, Global>();

    fn fuzzy_mut_is_send<K: Send, V: Send, A: Send + Allocator>() {
        is_send::<FuzzyMut<K, V, DEFAULT_PREFIX_LEN, A>>();
    }

    fn fuzzy_mut_is_sync<K: Sync, V: Sync, A: Sync + Allocator>() {
        is_sync::<FuzzyMut<K, V, DEFAULT_PREFIX_LEN, A>>();
    }

    fuzzy_mut_is_send::<[u8; 3], usize, Global>();
    fuzzy_mut_is_sync::<[u8; 3], usize, Global>();
}

#[test]
fn fuzzy() {
    for n in [4, 5, 17, 49] {
        let it = 48u8..48 + n;
        let mut tree: TreeMap<CString, usize> = TreeMap::new();
        let search = CString::new("a").unwrap();
        for c in it.clone() {
            let c = c as char;
            let s = CString::new(format!("a{c}")).unwrap();
            tree.insert(s, 0usize);
        }
        let results: Vec<_> = tree.fuzzy(&search, 1).collect();
        for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
            let c = c as char;
            let s = CString::new(format!("a{c}")).unwrap();
            assert_eq!(k, &s);
        }

        let mut tree: TreeMap<CString, usize> = TreeMap::new();
        let search = CString::new("a").unwrap();
        for c in it.clone() {
            let s = if c % 2 == 0 {
                let c = c as char;
                CString::new(format!("a{c}")).unwrap()
            } else {
                let c = c as char;
                CString::new(format!("a{c}a")).unwrap()
            };
            tree.insert(s, 0usize);
        }
        let results: Vec<_> = tree.fuzzy(&search, 1).collect();
        for ((k, _), c) in results.into_iter().rev().zip((it.clone()).step_by(2)) {
            let c = c as char;
            let s = CString::new(format!("a{c}")).unwrap();
            assert_eq!(k, &s);
        }

        let mut tree: TreeMap<CString, usize> = TreeMap::new();
        let search = CString::new("a").unwrap();
        for c in it.clone() {
            let s = if c % 2 == 0 {
                let c = c as char;
                CString::new(format!("a{c}")).unwrap()
            } else {
                let c = c as char;
                CString::new(format!("a{c}a")).unwrap()
            };
            tree.insert(s, 0usize);
        }
        let results: Vec<_> = tree.fuzzy(&search, 2).collect();
        for ((k, _), c) in results.into_iter().rev().zip(it.clone()) {
            let s = if c % 2 == 0 {
                let c = c as char;
                CString::new(format!("a{c}")).unwrap()
            } else {
                let c = c as char;
                CString::new(format!("a{c}a")).unwrap()
            };
            assert_eq!(k, &s);
        }
    }
}

#[test]
fn test_edit_dist_mutations() {
    let mut tree: TreeMap<Box<[u8]>, u32> = TreeMap::new();
    tree.try_insert(Box::new(*b"apple"), 0).unwrap();
    tree.try_insert(Box::new(*b"apply"), 1).unwrap();

    // Search for "apple", should match "apple" (dist 0) and "apply" (dist 1)
    let results: Vec<_> = tree.fuzzy(b"apple" as &[u8], 1).collect();
    assert_eq!(results.len(), 2);

    // Search for "axple" with dist 1, should match "apple"
    let results2: Vec<_> = tree.fuzzy(b"axple" as &[u8], 1).collect();
    assert_eq!(results2.len(), 1);
    assert_eq!(results2[0].0.as_ref(), b"apple".as_ref());

    // Test a case where distance == max_dist.
    // "booo" vs "book" should be dist 2.
    let mut tree2: TreeMap<Box<[u8]>, u32> = TreeMap::new();
    tree2.try_insert(Box::new(*b"book"), 0).unwrap();
    let results3: Vec<_> = tree2.fuzzy(b"booo" as &[u8], 2).collect();
    assert_eq!(results3.len(), 1);
    // This will fail if `v <= max_edit_dist` becomes `v < max_edit_dist`
    let results4: Vec<_> = tree2.fuzzy(b"booo" as &[u8], 1).collect();
    assert!(!results4.is_empty());
}

#[test]
fn test_stack_arena_pop() {
    let row_width = 5;
    let mut arena = StackArena::new(row_width);

    // Get a pointer to the first pushed row.
    let slice1_ptr = arena.push().as_mut_ptr();

    // Pop the row.
    arena.pop();

    // Push again and get a pointer to the new row.
    let slice2_ptr = arena.push().as_mut_ptr();

    // If pop works correctly, the arena should reuse the memory from the popped
    // row. If pop is a no-op, the second push will allocate new memory, and
    // the pointers will not be equal.
    assert_eq!(
        slice1_ptr, slice2_ptr,
        "arena should reuse memory after pop"
    );
}

fn get_stats<K: AsBytes, V>(tree: &TreeMap<K, V>) -> TreeStats {
    TreeStatsCollector::collect(tree).unwrap()
}

#[test]
fn test_fuzzy_search_node48() {
    let mut tree: TreeMap<Box<[u8]>, u32> = TreeMap::new();
    // Insert enough keys with a common prefix to likely create an InnerNode48
    for i in 0u8..30 {
        let key = vec![0, 0, i];
        tree.try_insert(Box::from(key), i as u32).unwrap();
    }

    // Check that we indeed have a Node48 to make the test meaningful
    let stats = get_stats(&tree);
    assert!(stats.node48.count > 0, "Test requires at least one Node48");

    // Search for a key that doesn't exist to ensure the search can return false
    // This covers the mutation `replace -> bool with false`
    let results: Vec<_> = tree.fuzzy(b"non-existent-key" as &[u8], 1).collect();
    assert!(results.is_empty());

    // Search for a key that exists to ensure search can return true
    // This covers the mutation `replace -> bool with true`
    let results: Vec<_> = tree.fuzzy(&[0, 0, 15u8] as &[u8], 0).collect();
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0.as_ref(), &[0, 0, 15u8]);
}

#[test]
fn test_fuzzy_search_node256() {
    let mut tree: TreeMap<Box<[u8]>, u32> = TreeMap::new();
    // Insert enough keys with a common prefix to create an InnerNode256
    for i in 0u8..100 {
        let key = vec![1, 1, i];
        tree.try_insert(Box::from(key), i as u32).unwrap();
    }

    let stats = get_stats(&tree);
    assert!(
        stats.node256.count > 0,
        "Test requires at least one Node256"
    );

    // Search for a key that doesn't exist to ensure the search can return false
    // This covers the mutation `replace -> bool with false`
    let results: Vec<_> = tree.fuzzy(b"non-existent-key" as &[u8], 1).collect();
    assert!(results.is_empty());

    // Search for a key that exists to ensure search can return true
    // This covers the mutation `replace -> bool with true`
    let results: Vec<_> = tree.fuzzy(&[1, 1, 80u8] as &[u8], 0).collect();
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0.as_ref(), &[1, 1, 80u8]);
}

#[test]
fn test_fuzzy_search_prefix() {
    let mut tree: TreeMap<Box<[u8]>, u32> = TreeMap::new();
    tree.try_insert(Box::new(*b"apple-pie"), 0).unwrap();
    tree.try_insert(Box::new(*b"apple-cider"), 1).unwrap();
    tree.try_insert(Box::new(*b"banana-pie"), 2).unwrap();
    // Add a key that is a fuzzy match but not on the same prefix path
    tree.try_insert(Box::new(*b"apply-pie"), 3).unwrap();

    // Search for a key that matches the prefix and has fuzzy matches down the path
    // This should find results on different branches, testing the `&=` mutation
    let search_key = b"apple-pie".as_slice();
    let results: Vec<_> = tree.fuzzy(search_key, 1).collect();
    // It should match "apple-pie" (dist 0) and "apply-pie" (dist 1)
    assert_eq!(results.len(), 2);
    assert!(results
        .iter()
        .any(|(k, _)| k.as_ref() == b"apple-pie".as_ref()));
    assert!(results
        .iter()
        .any(|(k, _)| k.as_ref() == b"apply-pie".as_ref()));

    // A search that should not find anything, to ensure fuzzy_search_prefix can
    // return false.
    let non_match_key = b"orange".as_slice();
    let non_match_results: Vec<_> = tree.fuzzy(non_match_key, 1).collect();
    assert!(non_match_results.is_empty());
}
