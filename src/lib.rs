//! `TransientMap` acts as a wrapper for `std::collections::HashMap` which allows for
//! the eviction of unused elements. In addition to the standard hashmap API, it provides
//! the following extra functions:
//! 
//! - `drain_unused` removes all of the elements that have not been inserted or accessed
//! since the previous drain call, returning the elements as an iterator. The entirety of
//! the drain operation takes `O(unused elements)` time. Note that this is faster
//! than the amount of time required to iterate over the entire map, which is `O(capacity)`.
//! - `drain_used` removes all of the elements that have been inserted or accessed since
//! the last drain call. The entirety of the drain operation takes `O(used elements)` time.
//! - `set_all_used` marks all elements as having been accessed in `O(1)` time.
//! - `set_all_unused` marks all elements as not having been accessed in `O(1)` time.
//! 
//! These additional functions make `TransientMap` an ideal choice for applications like
//! caching, where it is desirable to efficiently discard data that has not been used.
//! 
//! The following is a brief example of how to use `TransientMap`:
//! 
//! ```
//! # use transient_map::*;
//! let mut map = TransientMap::new();
//! map.insert_unused(1, "a");
//! map.insert_unused(2, "b");
//! assert_eq!(Some("b"), map.remove(&2));
//! map.insert(3, "c");
//! map.insert(4, "d");
//! assert_eq!(vec!((1, "a")), map.drain_unused().collect::<Vec<_>>());
//! 
//! let mut res = map.drain_unused().collect::<Vec<_>>();
//! res.sort_by(|a, b| a.0.cmp(&b.0));
//! 
//! assert_eq!(vec!((3, "c"), (4, "d")), res);
//! assert_eq!(0, map.len());
//! ```

#![deny(warnings)]
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use std::borrow::*;
use std::cell::*;
use std::collections::*;
use std::collections::hash_map::*;
use std::hash::*;
use std::mem::*;
use std::rc::*;

/// A hashmap wrapper which tracks used and unused entries, allowing
/// for their efficient removal.
pub struct TransientMap<K, V, S = RandomState> {
    /// The map which stores the key-value pairs and satellite tracking data.
    map: HashMap<Rc<K>, TransientMapValue<V>, S>,
    /// The tracker that stores information about which items are used and unused.
    tracker: TransientUsageTracker<K>
}

impl<K, V> TransientMap<K, V, RandomState> {
    /// Creates an empty `TransientMap`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates an empty `TransientMap` with at least the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K, V, S> TransientMap<K, V, S> {
    /// Marks all entries as used. They will not be included
    /// in the next `drain_unused` call. This function is `O(1)`.
    pub fn set_all_used(&mut self) {
        self.tracker.first_used = 0;
    }

    /// Marks all entries as unused. They will be included in the
    /// next `drain_unused` call. This function is `O(1)`.
    pub fn set_all_unused(&mut self) {
        self.tracker.first_used = self.tracker.item_usage.len();
    }

    /// Creates an empty `TransientMap` with at least the specified capacity, using
    /// `hasher` to hash the keys.
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            map: HashMap::with_capacity_and_hasher(capacity, hasher),
            tracker: TransientUsageTracker { first_used: 0, item_usage: VecDeque::new(), usage_offset: 0 }
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`. The iterator visits
    /// all keys silently, meaning that nothing is marked as used.
    pub fn keys_silent(&self) -> impl Iterator<Item = &K> {
        self.map.keys().map(|k| &**k)
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    pub fn into_keys(self) -> impl Iterator<Item = K> {
        self.map.into_keys().map(|k| Rc::try_unwrap(k).ok().expect("Another reference to the key still existed."))
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`. The iterator visits
    /// all keys silently, meaning that nothing is marked as used.
    pub fn values_silent(&self) -> impl Iterator<Item = &V> {
        self.map.values().map(|v| &v.value)
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.iter_mut().map(|(_, v)| v)
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    pub fn into_values(self) -> impl Iterator<Item = V> {
        self.map.into_values().map(|v| v.value)
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`. The iterator visits
    /// all keys silently, meaning that nothing is marked as used.
    pub fn iter_silent(&self) -> impl '_ + Iterator<Item = (&K, &V)> {
        self.map.iter().map(|(k, v)| (&**k, &v.value))
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    pub fn iter_mut(&mut self) -> impl '_ + Iterator<Item = (&K, &mut V)> {
        self.map.iter_mut().map(|(k, v)| {
            Self::promote_item(v, &mut self.tracker);
            (&**k, &mut v.value)
        })
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining key-value pairs. The returned iterator keeps a
    /// mutable borrow on the map to optimize its implementation.
    pub fn drain(&mut self) -> impl '_ + Iterator<Item = (K, V)> {
        self.tracker.first_used = 0;
        self.tracker.usage_offset = 0;
        self.tracker.item_usage.clear();
        self.map.drain().map(|(k, v)| (Rc::try_unwrap(k).ok().expect("Another reference was still out to the stored key."), v.value))
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    pub fn clear(&mut self) {
        self.map.clear();
        self.tracker.first_used = 0;
        self.tracker.usage_offset = 0;
        self.tracker.item_usage.clear();
    }

    /// Returns a reference to the map's [`BuildHasher`].
    pub fn hasher(&self) -> &S {
        self.map.hasher()
    }
    
    /// Demotes the provided item into the unused category if it is currently used.
    fn demote_item(value: &TransientMapValue<V>, tracker: &mut TransientUsageTracker<K>) {
        let idx = value.index.get();
        if tracker.first_used <= idx.wrapping_add(tracker.usage_offset) {
            Self::swap_items(value.index.get(), tracker.first_used.wrapping_sub(tracker.usage_offset), tracker);
            tracker.first_used += 1;
        }
    }

    /// Promotes the provided item into the used category if it is currently unused.
    fn promote_item(value: &TransientMapValue<V>, tracker: &mut TransientUsageTracker<K>) {
        let idx = value.index.get();
        if idx.wrapping_add(tracker.usage_offset) < tracker.first_used {
            Self::swap_items(value.index.get(), (tracker.first_used - 1).wrapping_sub(tracker.usage_offset), tracker);
            tracker.first_used -= 1;
        }
    }

    /// Removes the given item from the usage tracker, returning the stored reference to the key.
    fn remove_item(value: &TransientMapValue<V>, tracker: &mut TransientUsageTracker<K>) -> Rc<K> {
        let idx = value.index.get();
        if idx.wrapping_add(tracker.usage_offset) < tracker.first_used {
            Self::swap_items(idx, 0usize.wrapping_sub(tracker.usage_offset), tracker);
            tracker.usage_offset = tracker.usage_offset.wrapping_sub(1);
            tracker.first_used -= 1;
            tracker.item_usage.pop_front()
        }
        else {
            Self::swap_items(idx, (tracker.item_usage.len() - 1).wrapping_sub(tracker.usage_offset), tracker);
            tracker.item_usage.pop_back()
        }.expect("The item usage deque was empty.").key
    }

    /// Swaps the positions of the two items in the item usage tracker.
    fn swap_items(a: usize, b: usize, tracker: &mut TransientUsageTracker<K>) {
        let a_idx = a.wrapping_add(tracker.usage_offset);
        let b_idx = b.wrapping_add(tracker.usage_offset);

        tracker.item_usage[a_idx].index.set(b);
        tracker.item_usage[b_idx].index.set(a);

        tracker.item_usage.swap(a_idx, b_idx);
    }
}

impl<K, V, S> TransientMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher
{
    /// Removes all entries from the map that were not accessed since the
    /// last call to `drain_used` or `drain_unused`.
    /// 
    /// It takes `O(unused elements)` time to iterate over the results of this call.
    /// Like the standard `hash_map::Drain`, all elements remaining in the iterator
    /// when it is dropped are also dropped.
    pub fn drain_unused(&mut self) -> impl '_ + Iterator<Item = (K, V)> {
        let begin_used = self.tracker.first_used;
        self.tracker.first_used = self.tracker.item_usage.len() - begin_used;
        self.tracker.usage_offset = self.tracker.usage_offset.wrapping_sub(begin_used);
        Drain { map: &mut self.map, iterator: self.tracker.item_usage.drain(..begin_used) }
    }
    
    /// Removes all entries from the map that were accessed since the
    /// last call to `drain_used` or `drain_unused`.
    /// 
    /// It takes `O(used elements)` time to iterate over the results of this call.
    /// Like the standard `hash_map::Drain`, all elements remaining in the iterator
    /// when it is dropped are also dropped.
    pub fn drain_used(&mut self) -> impl '_ + Iterator<Item = (K, V)> {
        Drain { map: &mut self.map, iterator: self.tracker.item_usage.drain(self.tracker.first_used..) }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `TransientMap`. The collection may reserve more space to speculatively
    /// avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
        self.tracker.item_usage.reserve(additional);
    }

    /// Retains only the elements specified by the predicate. Because the predicate
    /// visits all elements, all elements are marked as used.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        for (k, v) in &mut self.map {
            if f(&**k, &mut v.value) {
                Self::promote_item(v, &mut self.tracker);
            }
            else {
                Self::demote_item(v, &mut self.tracker);
            }
        }
        drop(self.drain_unused());
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the `TransientMap`. The collection may reserve more space to speculatively
    /// avoid frequent reallocations. After calling `try_reserve`,
    /// capacity will be greater than or equal to `self.len() + additional` if
    /// it returns `Ok(())`.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.map.try_reserve(additional)?;
        self.tracker.item_usage.try_reserve(additional)?;
        Ok(())
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
        self.tracker.item_usage.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.map.shrink_to(min_capacity);
        self.tracker.item_usage.shrink_to(min_capacity);
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.map.entry(Rc::new(key)) {
            hash_map::Entry::Vacant(e) => Entry::Vacant(VacantEntry {
                inner: e,
                tracker: &mut self.tracker
            }),
            hash_map::Entry::Occupied(e) => Entry::Occupied(OccupiedEntry {
                inner: e,
                tracker: &mut self.tracker
            }),
        }
    }

    /// Returns a reference to the value corresponding to the key. This accesses
    /// the value silently, meaning that nothing is marked as used.
    pub fn get_silent<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value_silent(k).map(|(_, v)| v)
    }

    /// Returns the key-value pair corresponding to the supplied key. This accesses
    /// the pair silently, meaning that nothing is marked as used.
    pub fn get_key_value_silent<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get_key_value(k).map(|(k, h)| (&**k, &h.value))
    }

    /// Returns `true` if the map contains a value for the specified key. This accesses
    /// the value silently, meaning that nothing is marked as used.
    pub fn contains_key_silent<Q: ?Sized>(&self, k: &Q) -> bool
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.contains_key(k)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get_mut(k).map(|value| {
            Self::promote_item(value, &mut self.tracker);
            &mut value.value
        })
    }

    /// Inserts a key-value pair into the map. The inserted key
    /// is automatically treated as used.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.insert_with_mover(k, v, self.tracker.item_usage.len(), 0, Self::promote_item, VecDeque::push_back)
    }
    

    /// Inserts a key-value pair into the map. The inserted key
    /// is initially considered unused.
    pub fn insert_unused(&mut self, k: K, v: V) -> Option<V> {
        self.insert_with_mover(k, v, 0, 1, Self::demote_item, VecDeque::push_front)
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.remove_entry(k).map(|(_, v)| v)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Rc<K>: Borrow<Q>,
        Q: Hash + Eq,
    {
        if let Some(prev) = self.map.remove(k) {
            let key = Self::remove_item(&prev, &mut self.tracker);
            Some((Rc::try_unwrap(key).ok().expect("Another reference was still out to the stored key."), prev.value))
        }
        else {
            None
        }
    }

    /// Inserts the provided key-value pair into the map, using the mover functions
    /// to select an initial position for the usage tracker. Returns the old element if it
    /// already existed.
    fn insert_with_mover(&mut self, k: K, v: V, initial_position: usize, usage_increment: usize, mover: impl Fn(&TransientMapValue<V>, &mut TransientUsageTracker<K>), pusher: impl Fn(&mut VecDeque<TransientMapItemUsage<K>>, TransientMapItemUsage<K>)) -> Option<V> {
        let new_offset = self.tracker.usage_offset.wrapping_add(usage_increment);
        let usage = TransientMapItemUsage {
            key: Rc::new(k),
            index: Rc::new(Cell::new(initial_position.wrapping_sub(new_offset)))
        };
        let value = TransientMapValue {
            value: v,
            index: usage.index.clone()
        };
        
        if let Some(prev) = self.map.insert(usage.key.clone(), value) {
            mover(&prev, &mut self.tracker);
            usage.index.set(prev.index.get());
            self.tracker.item_usage[prev.index.get().wrapping_add(self.tracker.usage_offset)] = usage;
            Some(prev.value)
        }        
        else {
            self.tracker.usage_offset = new_offset;
            self.tracker.first_used += usage_increment;
            pusher(&mut self.tracker.item_usage, usage);
            None
        }
    }
}

impl<K, V, S> Clone for TransientMap<K, V, S>
where
    K: Clone,
    V: Clone,
    S: Clone,
{
    fn clone(&self) -> Self {
        Self { map: self.map.clone(), tracker: TransientUsageTracker { first_used: self.tracker.first_used, item_usage: self.tracker.item_usage.clone(), usage_offset: self.tracker.usage_offset } }
    }
}

impl<K, V, S> Default for TransientMap<K, V, S>
where
    S: Default
{
    fn default() -> Self {
        Self { map: HashMap::default(), tracker: TransientUsageTracker { first_used: 0, item_usage: VecDeque::new(), usage_offset: 0 } }
    }
}

impl<K, V, S> PartialEq for TransientMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<K, V, S> Eq for TransientMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> std::fmt::Debug for TransientMap<K, V, S>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.map, f)
    }
}

unsafe impl<K, V, S> Send for TransientMap<K, V, S>
where
    K: Send,
    V: Send,
    S: Send,
{
}

unsafe impl<K, V, S> Sync for TransientMap<K, V, S>
where
    K: Sync,
    V: Sync,
    S: Sync,
{
}

/// A draining iterator over the entries of a `TransientMap`.
struct Drain<'a, K, V, S, I: Iterator<Item = TransientMapItemUsage<K>>>
where
    K: Eq + Hash,
    S: BuildHasher
{
    /// The map which contains the items to remove.
    map: &'a mut HashMap<Rc<K>, TransientMapValue<V>, S>,
    /// The iterator over the items to remove.
    iterator: I
}

impl<'a, K, V, S, I: Iterator<Item = TransientMapItemUsage<K>>> Iterator for Drain<'a, K, V, S, I>
where
    K: Eq + Hash,
    S: BuildHasher
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let pair = self.iterator.next()?;
        let value = self.map.remove(&pair.key).expect("Could not remove item from map.").value;
        Some((Rc::try_unwrap(pair.key).ok().expect("Another copy of key still existed."), value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iterator.size_hint()
    }
}

impl<'a, K, V, S, I: Iterator<Item = TransientMapItemUsage<K>>> Drop for Drain<'a, K, V, S, I>
where
    K: Eq + Hash,
    S: BuildHasher
{
    fn drop(&mut self) {
        for pair in &mut self.iterator {
            self.map.remove(&pair.key);
        }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, K: 'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

/// A view into a vacant entry in a `TransientMap`.
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    /// A reference to the inner occupied map entry.
    inner: hash_map::VacantEntry<'a, Rc<K>, TransientMapValue<V>>,
    /// The tracker that stores information about which items are used and unused.
    tracker: &'a mut TransientUsageTracker<K>
}

impl<'a, K: 'a, V: 'a> VacantEntry<'a, K, V> {
    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        let usage = TransientMapItemUsage {
            key: self.inner.key().clone(),
            index: Rc::new(Cell::new(self.tracker.item_usage.len().wrapping_sub(self.tracker.usage_offset)))
        };

        let value = TransientMapValue {
            value,
            index: usage.index.clone()
        };

        self.tracker.item_usage.push_back(usage);
        &mut self.inner.insert(value).value
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a mutable reference to it.
    /// The inserted value is initially considered unused.
    pub fn insert_unused(self, value: V) -> &'a mut V {
        let new_offset = self.tracker.usage_offset.wrapping_add(1);
        let usage = TransientMapItemUsage {
            key: self.inner.key().clone(),
            index: Rc::new(Cell::new(0usize.wrapping_sub(new_offset)))
        };

        let value = TransientMapValue {
            value,
            index: usage.index.clone()
        };

        self.tracker.usage_offset = new_offset;
        self.tracker.first_used += 1;
        self.tracker.item_usage.push_front(usage);
        &mut self.inner.insert(value).value
    }

    /// Gets a reference to the key that would be used when inserting a value through the `VacantEntry`.
    pub fn key_silent(&self) -> &K {
        self.inner.key()
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        Rc::try_unwrap(self.inner.into_key()).ok().expect("Another reference was still out to the stored key.")
    }
}

unsafe impl<'a, K, V> Send for VacantEntry<'a, K, V>
where
    K: Send,
    V: Send
{}

unsafe impl<'a, K, V> Sync for VacantEntry<'a, K, V>
where
    K: Sync,
    V: Sync
{}

/// A view into an occupied entry in a `TransientMap`.
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    /// A reference to the inner occupied map entry.
    inner: hash_map::OccupiedEntry<'a, Rc<K>, TransientMapValue<V>>,
    /// The tracker that stores information about which items are used and unused.
    tracker: &'a mut TransientUsageTracker<K>
}

impl<'a, K: 'a, V: 'a> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the value in the entry. This accesses
    /// the value silently, meaning that nothing is marked as used.
    pub fn get_silent(&self) -> &V {
        &self.inner.get().value
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        let res = self.inner.get_mut();
        TransientMap::<_, _, ()>::promote_item(res, self.tracker);
        &mut res.value
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    pub fn insert(&mut self, value: V) -> V {
        replace(self.get_mut(), value)
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    /// The inserted value is initially considered unused.
    pub fn insert_unused(&mut self, value: V) -> V {
        let res = self.inner.get_mut();
        TransientMap::<_, _, ()>::demote_item(res, self.tracker);
        replace(&mut res.value, value)
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry with a lifetime bound to the map itself.
    pub fn into_mut(self) -> &'a mut V {
        let res = self.inner.into_mut();
        TransientMap::<_, _, ()>::promote_item(res, self.tracker);
        &mut res.value
    }

    /// Gets a reference to the key in the entry. This accesses
    /// the value silently, meaning that nothing is marked as used.
    pub fn key_silent(&self) -> &K {
        self.inner.key()
    }

    /// Takes the value out of the entry, and returns it.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Take the ownership of the key and value from the map.
    pub fn remove_entry(self) -> (K, V) {
        let (key, v) = self.inner.remove_entry();
        TransientMap::<_, _, ()>::remove_item(&v, self.tracker);
        (Rc::try_unwrap(key).ok().expect("Another reference was still out to the stored key."), v.value)
    }
}

unsafe impl<'a, K, V> Send for OccupiedEntry<'a, K, V>
where
    K: Send,
    V: Send
{}

unsafe impl<'a, K, V> Sync for OccupiedEntry<'a, K, V>
where
    K: Sync,
    V: Sync
{}

/// Utilized to manage which objects in the transient map have been used since the last drain.
struct TransientUsageTracker<K> {
    /// The queue index of the first used item.
    pub first_used: usize,
    /// The queue that separates unused and used items.
    pub item_usage: VecDeque<TransientMapItemUsage<K>>,
    /// The offset to apply to logical indices to get items' current position in the tracking array.
    pub usage_offset: usize
}

/// Acts as satellite tracking data used to identify an entry in a transient map.
#[derive(Clone)]
struct TransientMapItemUsage<K> {
    /// The key utilized to insert the item into the map.
    pub key: Rc<K>,
    /// A reference to the item's current logical index in the tracking array.
    pub index: Rc<Cell<usize>>
}

/// Stores information about a transient map entry, including
/// the entry value and satellite tracking data.
#[derive(Clone)]
struct TransientMapValue<V> {
    /// The value of the item.
    pub value: V,
    /// A reference to the item's current logical index in the tracking array.
    pub index: Rc<Cell<usize>>
}

impl<V: PartialEq> PartialEq for TransientMapValue<V> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<V: Eq> Eq for TransientMapValue<V> {
}

impl<V: std::fmt::Debug> std::fmt::Debug for TransientMapValue<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.value, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_drain_len() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");
        drop(map.drain_unused());
        map.get_mut(&1);
        map.get_silent(&2);

        let mut res = map.drain_unused().collect::<Vec<_>>();
        res.sort_by(|a, b| a.0.cmp(&b.0));

        assert_eq!(vec!((2, "b"), (3, "c")), res);
        assert_eq!(1, map.len());
    }

    #[test]
    pub fn test_drain_mark_used() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");
        drop(map.drain_unused());
        map.get_mut(&1);
        map.get_silent(&2);
        map.set_all_used();
        drop(map.drain_unused());
        assert_eq!(3, map.len());
    }

    #[test]
    pub fn test_drain_mark_unused() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        map.insert(2, "b");
        map.insert(3, "c");
        map.set_all_unused();
        drop(map.drain_unused());
        assert_eq!(0, map.len());
    }

    #[test]
    pub fn test_insert_overwrite() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        drop(map.drain_unused());
        assert_eq!(Some("a"), map.insert(1, "b"));
        drop(map.drain_unused());
        assert_eq!(1, map.len());
    }

    #[test]
    pub fn test_insert_no_overwrite() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        drop(map.drain_unused());
        drop(map.drain_unused());
        assert_eq!(0, map.len());
    }
    
    #[test]
    pub fn test_insert_unused() {
        let mut map = TransientMap::new();
        map.insert(1, "a");
        map.insert_unused(2, "b");
        assert_eq!(vec!((2, "b")), map.drain_unused().collect::<Vec<_>>());
    }

    #[test]
    pub fn test_add_remove_drop() {
        let mut map = TransientMap::new();
        map.insert_unused(1, "a");
        map.insert_unused(2, "b");
        assert_eq!(Some("b"), map.remove(&2));
        map.insert(3, "c");
        map.insert(4, "d");
        assert_eq!(vec!((1, "a")), map.drain_unused().collect::<Vec<_>>());
        
        let mut res = map.drain_unused().collect::<Vec<_>>();
        res.sort_by(|a, b| a.0.cmp(&b.0));

        assert_eq!(vec!((3, "c"), (4, "d")), res);
        assert_eq!(0, map.len());
    }
}