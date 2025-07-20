use super::{OccupiedEntry, SubtreeIter, SubtreeIterMut, TreeMap, VacantEntry, DEFAULT_PREFIX_LEN};
use crate::{
    allocator::{Allocator, Global},
    raw::{ConcreteNodePtr, DeletePoint, LeafNode, NodePtr, OverwritePoint, PrefixInsertPoint},
    AsBytes,
};

/// A view into an occupied subtree in a [`TreeMap`].
///
/// It is part of the [`PrefixOccupied`] enum.
#[derive(Debug)]
pub struct InnerOccupiedEntry<
    'a,
    K,
    V,
    const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN,
    A: Allocator = Global,
> {
    pub(crate) map: &'a mut TreeMap<K, V, PREFIX_LEN, A>,
    pub(crate) key: K,
    pub(crate) overwrite_point: OverwritePoint<K, V, PREFIX_LEN>,
}

// SAFETY: This struct contains a `&mut TreeMap<K, V>` which mean `K` and `V`
// must be `Send` for the struct to be `Send`.
unsafe impl<K: Send, V: Send, const PREFIX_LEN: usize, A: Send + Allocator> Send
    for InnerOccupiedEntry<'_, K, V, PREFIX_LEN, A>
{
}

// SAFETY: This type has no interior mutability, and requires all internally
// referenced types to be `Sync` for the whole thing to be `Sync`.
unsafe impl<K: Sync, V: Sync, const PREFIX_LEN: usize, A: Sync + Allocator> Sync
    for InnerOccupiedEntry<'_, K, V, PREFIX_LEN, A>
{
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> InnerOccupiedEntry<'a, K, V, PREFIX_LEN, A>
where
    K: AsBytes,
{
    fn get_leaf(&self) -> Option<NodePtr<PREFIX_LEN, LeafNode<K, V, PREFIX_LEN>>> {
        match self.overwrite_point.overwrite_point.to_node_ptr() {
            ConcreteNodePtr::LeafNode(leaf) => Some(leaf),
            _ => None,
        }
    }

    /// Gets a reference to the underlying value if there is only a singular
    /// underlying entry.
    pub fn get(&self) -> Option<&V> {
        // SAFETY: This is safe because `Self` has a mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.get_leaf().map(|f| f.as_value_ref()) }
    }

    /// Gets a mutable reference to the underlying value if there is only a
    /// singular underlying entry.
    pub fn get_mut(&mut self) -> Option<&mut V> {
        // SAFETY: This is safe because `Self` has a mutable reference
        // so it's safe to generate a shared reference from this mutable reference
        unsafe { self.get_leaf().map(|f| f.as_value_mut()) }
    }

    /// Gets a reference to the underlying key if there is only a singular
    /// underlying entry.
    pub fn get_key(&self) -> Option<&K> {
        unsafe { self.get_leaf().map(|f| f.as_key_ref()) }
    }

    /// Gets a reference to the underlying key and a mutable reference to the
    /// value if there is only a singular underlying entry.
    pub fn get_key_value_mut(&mut self) -> Option<(&K, &mut V)> {
        unsafe { self.get_leaf().map(|f| f.as_key_ref_value_mut()) }
    }

    /// Returns a reference to the key that will overwrite the underlying
    /// entries.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Returns an iterator over all key value pairs that would be erased upon
    /// insertion.
    pub fn iter(&self) -> SubtreeIter<'_, K, V, PREFIX_LEN, A> {
        // SAFETY: this is safe since we have an exclusive reference to the tree
        // containing this node, this iterator may only live for the lifetime of the
        // reference given to self. Otherwise it is possible to mutate the tree
        // using this entry while the iterator can still be used, causing
        // segmentation faults (if the iterator is actually used).
        unsafe { SubtreeIter::new(self.overwrite_point.overwrite_point) }
    }

    /// Returns a mutable iterator over all key value pairs that would be erased
    /// upon insertion.
    pub fn iter_mut(&mut self) -> SubtreeIterMut<'_, K, V, PREFIX_LEN, A> {
        // SAFETY: this is safe since we have an exclusive reference to the tree
        // containing this node, this iterator may only live for the lifetime of the
        // reference given to self. Otherwise it is possible to mutate the tree
        // using this entry while the iterator can still be used, causing
        // segmentation faults (if the iterator is actually used).
        unsafe { SubtreeIterMut::new(self.overwrite_point.overwrite_point) }
    }

    /// Erase the subtree and insert the value with the previously given key in
    /// its place.
    pub fn insert(self, value: V) -> &'a mut V {
        let entry = self.insert_entry(value);
        entry.into_mut()
    }

    /// Erase the subtree and insert the value with the previously given key in
    /// its place.
    ///
    /// Returns an [OccupiedEntry].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        // no fixup required since an overwrite never changes the parent node.
        let path = self.overwrite_point.path;
        let result = self.map.apply_prefix_insert_point(
            PrefixInsertPoint::OverwritePoint(self.overwrite_point),
            self.key,
            value,
        );

        let delete_point = DeletePoint {
            path,
            leaf_node_ptr: result.leaf_node_ptr,
        };
        OccupiedEntry {
            map: self.map,
            delete_point,
        }
    }
}

/// An occupied entry of a prefix insert operation.
///
/// This entry is either occupied at the [leaf](Self::Leaf) level,
/// where the keys match completely.
/// Or occupied at a [subtree](Self::Inner) level, where the new key is
/// a prefix of existing key(s) or vice versa.
#[derive(Debug)]
pub enum PrefixOccupied<
    'a,
    K,
    V,
    const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN,
    A: Allocator = Global,
> {
    /// An occupied entry where key matched completely.
    Leaf(OccupiedEntry<'a, K, V, PREFIX_LEN, A>),
    /// An occupied entry where the key is a prefix of existing keys or vice
    /// versa.
    Inner(InnerOccupiedEntry<'a, K, V, PREFIX_LEN, A>),
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> PrefixOccupied<'a, K, V, PREFIX_LEN, A>
where
    K: AsBytes,
{
    /// Gets a reference to the underlying value if there is only a singular
    /// underlying entry.
    pub fn get(&self) -> Option<&V> {
        match self {
            Self::Leaf(leaf) => Some(leaf.get()),
            Self::Inner(inner) => inner.get(),
        }
    }

    /// Gets a mutable reference to the underlying value if there is only a
    /// singular underlying entry.
    pub fn get_mut(&mut self) -> Option<&mut V> {
        match self {
            Self::Leaf(leaf) => Some(leaf.get_mut()),
            Self::Inner(inner) => inner.get_mut(),
        }
    }

    /// Sets the value of the entry.
    pub fn insert(self, value: V) -> &'a mut V {
        match self {
            Self::Leaf(mut leaf) => {
                leaf.insert(value);
                leaf.into_mut()
            },
            Self::Inner(inner) => inner.insert_entry(value).into_mut(),
        }
    }

    /// Sets the value of the entry.
    ///
    /// Returns an [OccupiedEntry].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        match self {
            Self::Leaf(mut leaf) => {
                leaf.insert(value);
                leaf
            },
            Self::Inner(inner) => inner.insert_entry(value),
        }
    }

    /// Returns a reference to the key that got used for the creation of this
    /// occupied entry.
    pub fn key(&self) -> &K {
        match self {
            Self::Leaf(leaf) => leaf.key(),
            Self::Inner(inner) => inner.key(),
        }
    }

    /// Gets a reference to the underlying key if there is only a
    /// singular underlying entry.
    pub fn get_key(&self) -> Option<&K> {
        match self {
            Self::Leaf(leaf) => Some(leaf.key()),
            Self::Inner(inner) => inner.get_key(),
        }
    }
}

/// A view into a prefixed entry in a map, which may either be vacant or
/// occupied.
///
/// This enum is constructed from the [`TreeMap::prefix_entry`] method.
#[derive(Debug)]
pub enum PrefixEntry<'a, K, V, const PREFIX_LEN: usize = DEFAULT_PREFIX_LEN, A: Allocator = Global>
{
    /// A view into an occupied prefix entry in a [`TreeMap`].
    Occupied(PrefixOccupied<'a, K, V, PREFIX_LEN, A>),
    /// A view into a vacant entry in a [`TreeMap`].
    Vacant(VacantEntry<'a, K, V, PREFIX_LEN, A>),
}

impl<'a, K, V, const PREFIX_LEN: usize, A: Allocator> PrefixEntry<'a, K, V, PREFIX_LEN, A>
where
    K: AsBytes,
{
    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        match self {
            Self::Occupied(entry) => entry.insert_entry(value),
            Self::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Returns a reference to the key that got used for the creation of this
    /// entry.
    pub fn key(&self) -> &K {
        match self {
            Self::Occupied(entry) => entry.key(),
            Self::Vacant(entry) => entry.key(),
        }
    }

    /// Gets a reference to the underlying key if there is only a
    /// singular underlying entry.
    pub fn get_key(&self) -> Option<&K> {
        match self {
            Self::Occupied(entry) => entry.get_key(),
            Self::Vacant(entry) => Some(entry.key()),
        }
    }

    /// Ensures a leaf is in the entry by inserting the default value if empty
    /// or occupied by a subtree,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf.into_mut(),
            Self::Occupied(PrefixOccupied::Inner(inner)) => inner.insert(Default::default()),
            Self::Vacant(entry) => entry.insert(Default::default()),
        }
    }

    /// Ensures a leaf is in the entry by inserting the default if empty or
    /// occupied by a subtree, and returns a mutable reference to the value
    /// in the entry.
    pub fn or_insert(self, value: V) -> &'a mut V {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf.into_mut(),
            Self::Occupied(PrefixOccupied::Inner(inner)) => inner.insert(value),
            Self::Vacant(entry) => entry.insert(value),
        }
    }

    /// Ensures a leaf is in the entry by inserting the result of the default
    /// function if empty or occupied by a subtree, and returns a mutable
    /// reference to the value in the entry.
    pub fn or_insert_with<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf.into_mut(),
            Self::Occupied(PrefixOccupied::Inner(inner)) => inner.insert(f()),
            Self::Vacant(entry) => entry.insert(f()),
        }
    }

    /// Ensures a leaf is in the entry by inserting, if empty or occupied by a
    /// subtree, the result of the default function. This method allows for
    /// generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the
    /// .entry(key) method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying
    /// the key is unnecessary, unlike with `.or_insert_with(|| ... )`.
    pub fn or_insert_with_key<F>(self, f: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf.into_mut(),
            Self::Occupied(PrefixOccupied::Inner(inner)) => {
                let k = f(inner.key());
                inner.insert(k)
            },
            Self::Vacant(entry) => {
                let k = f(entry.key());
                entry.insert(k)
            },
        }
    }

    /// Similar to [`PrefixEntry::or_default`] but yields an [`OccupiedEntry`]
    pub fn or_default_entry(self) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
    where
        V: Default,
    {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf,
            Self::Occupied(PrefixOccupied::Inner(inner)) => inner.insert_entry(Default::default()),
            Self::Vacant(entry) => entry.insert_entry(Default::default()),
        }
    }

    /// Similar to [`PrefixEntry::or_insert`] but yields an [`OccupiedEntry`]
    pub fn or_insert_entry(self, value: V) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A> {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf,
            Self::Occupied(PrefixOccupied::Inner(inner)) => inner.insert_entry(value),
            Self::Vacant(entry) => entry.insert_entry(value),
        }
    }

    /// Similar to [`PrefixEntry::or_insert_with_key`] but yields an
    /// [`OccupiedEntry`]
    pub fn or_insert_with_key_entry<F>(self, f: F) -> OccupiedEntry<'a, K, V, PREFIX_LEN, A>
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Self::Occupied(PrefixOccupied::Leaf(leaf)) => leaf,
            Self::Occupied(PrefixOccupied::Inner(inner)) => {
                let k = f(inner.key());
                inner.insert_entry(k)
            },
            Self::Vacant(entry) => {
                let k = f(entry.key());
                entry.insert_entry(k)
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::{ffi::CString, string::String};

    use super::*;

    #[test]
    fn prefix_entry_is_send_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        fn entry_is_send<'a, K: Send + 'a, V: Send + 'a, A: Send + Allocator + 'a>() {
            is_send::<PrefixEntry<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        fn entry_is_sync<'a, K: Sync + 'a, V: Sync + 'a, A: Sync + Allocator + 'a>() {
            is_sync::<PrefixEntry<'a, K, V, DEFAULT_PREFIX_LEN, A>>();
        }

        entry_is_send::<[u8; 3], usize, Global>();
        entry_is_sync::<[u8; 3], usize, Global>();
    }

    #[test]
    fn key() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        assert_eq!(*tree.prefix_entry(a.clone()).key(), a);
        assert_eq!(*tree.prefix_entry(b.clone()).key(), b);
        assert_eq!(*tree.prefix_entry(c.clone()).key(), c);
    }

    #[test]
    fn or() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        let d = CString::new("d").unwrap();
        let e = CString::new("e").unwrap();
        let f = CString::new("f").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.prefix_entry(a.clone()).or_insert(String::from("aa"));
        tree.prefix_entry(b.clone()).or_insert(String::from("bb"));
        tree.prefix_entry(c.clone()).or_insert(String::from("cc"));
        tree.prefix_entry(d.clone()).or_default();
        tree.prefix_entry(e.clone())
            .or_insert_with(|| String::from("e"));
        tree.prefix_entry(f.clone())
            .or_insert_with_key(|k| String::from(k.to_str().unwrap()));

        assert_eq!(tree.get(&a).unwrap(), "a");
        assert_eq!(tree.get(&b).unwrap(), "b");
        assert_eq!(tree.get(&c).unwrap(), "cc");
        assert_eq!(tree.get(&d).unwrap(), &String::default());
        assert_eq!(tree.get(&e).unwrap(), "e");
        assert_eq!(tree.get(&f).unwrap(), "f");
    }

    #[test]
    fn insert_entry() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = CString::new("a").unwrap();
        let b = CString::new("b").unwrap();
        let c = CString::new("c").unwrap();
        tree.insert(a.clone(), String::from("a"));
        tree.insert(b.clone(), String::from("b"));

        tree.prefix_entry(a.clone())
            .insert_entry(String::from("aa"));
        tree.prefix_entry(b.clone())
            .insert_entry(String::from("bb"));
        tree.prefix_entry(c.clone())
            .insert_entry(String::from("cc"));

        assert_eq!(tree.get(&a).unwrap(), "aa");
        assert_eq!(tree.get(&b).unwrap(), "bb");
        assert_eq!(tree.get(&c).unwrap(), "cc");
    }

    #[test]
    fn prefix_insert_entry() {
        let mut tree: TreeMap<_, _> = TreeMap::new();
        let a = String::from("abb");
        let b = String::from("b");
        let c = String::from("ab");
        tree.try_insert(a.clone(), String::from("a")).unwrap();
        tree.try_insert(b.clone(), String::from("b")).unwrap();

        tree.prefix_entry(a.clone())
            .insert_entry(String::from("aa"));
        tree.prefix_entry(b.clone())
            .insert_entry(String::from("bb"));
        tree.prefix_entry(c.clone())
            .insert_entry(String::from("cc"));

        assert!(tree.get(&a).is_none());
        assert_eq!(tree.get(&b).unwrap(), "bb");
        assert_eq!(tree.get(&c).unwrap(), "cc");
    }
}
