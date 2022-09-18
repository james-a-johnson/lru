//! Least Recently Used (LRU) cache for making function calls faster
//!
//! The [`LRUCache`] is meant to be similar to the python decorator lru_cache.
//!
//! ```
//! use std::thread::sleep;
//! use std::time::Duration;
//! use lru::LRUCache;
//!
//! fn slow_function(a: usize) -> usize {
//!     sleep(Duration::from_secs(5));
//!     a * a
//! }
//!
//! let mut cached_function = LRUCache::<16, usize, usize>::new(slow_function);
//! // Slow
//! let val = cached_function.get(10);
//! assert_eq!(val, 100);
//! // Fast
//! let val = cached_function.get(10);
//! assert_eq!(val, 100);
//! ```

#![feature(hash_drain_filter)]
#![feature(maybe_uninit_uninit_array)]

#![warn(clippy::pedantic)]
#![warn(clippy::suspicious)]
#![warn(clippy::perf)]
#![warn(clippy::style)]
#![warn(clippy::correctness)]
#![warn(clippy::missing_docs)]

use std::collections::HashMap;
use std::hash::Hash;

mod linked;
use linked::ConstLinkedList;

/// Struct for caching the function call values
///
/// The type parameter N is the size of LRU cache. That is the number of parameter, result values
/// that will be stored at a time.
///
/// Type parameter P is the type of the parameter that the function takes.
///
/// Type parameter V is the type of the return value of the function.
///
/// This struct currently has a problem that the map of parameters to indices in the backing cache
/// can grow unbounded. To keep the property of a get having a constant time access when the
/// parameter is in the cache, old removed values are left in the map and won't necessarily be
/// removed when they are no longer in the cache. To remedy this, you can use the [`LRUCache::map_size`]
/// method to determine the current size of the map and [`LRUCache::purge`] method to get rid of
/// unused values if it's size is getting too large.
pub struct LRUCache<const N: usize, P, V>
where
    P: Hash + Eq,
{
    /// Function that is being cached
    pub func: fn(P) -> V,
    /// Map of parameters to their index in the cache
    map: HashMap<P, usize>,
    /// Cache of parameter value pairs
    cache: Box<ConstLinkedList<N, P, V>>,
}

impl<const N: usize, P, V> LRUCache<N, P, V>
where
    P: Hash + Eq + Clone,
{
    /// Create a new empty cache
    pub fn new(f: fn(P) -> V) -> Self {
        Self {
            func: f,
            map: HashMap::with_capacity(N),
            cache: Box::new(ConstLinkedList::new()),
        }
    }

    /// Get the number of entries in the backing map of the cache
    pub fn map_size(&self) -> usize {
        self.map.len()
    }

    /// Get a reference to the returned value of the function
    ///
    /// If the value is in the cache, a reference to the cached value will be returned. Otherwise,
    /// the value will be calculated by calling the function and that will be cached and a
    /// reference to it will be returned.
    ///
    /// The parameter value pair will become the new most recently used value in the cache.
    pub fn get_ref(&mut self, p: P) -> &V {
        if let Some(i) = self.map.get_mut(&p) {
            // SAFETY: Referencing the index that we got from putting the value into the store.
            // That means that there are at least that many elements in the cache. As the cache can
            // not decrease in the number of elements in it, that index will always be a valid
            // entry even if it does not match the parameter value that is from the map.
            let entry = unsafe { self.cache.get_arr_ref_unchecked(*i) };
            if *entry.0 == p {
                // SAFETY: The safety argument above shows why the index is valid which is all that
                // is required for this method to be safe.
                unsafe { self.cache.make_head(*i) };
                // SAFETY: Same reasoning as above.
                let entry = unsafe { self.cache.get_arr_ref_unchecked(*i) };
                entry.1
            } else {
                let new_val = (self.func)(p.clone());
                self.cache.push_front((p.clone(), new_val));
                *i = self.cache.head_index_unchecked();
                // SAFETY: Just inserted a value into the cache so we know it's the head element
                // and that this will be a valid value.
                unsafe { self.cache.get_head_ref_unchecked() }
            }
        } else {
            let new_val = (self.func)(p.clone());
            self.cache.push_front((p.clone(), new_val));
            self.map.insert(p, self.cache.head_index_unchecked());
            // SAFETY: Just inserted a value into the cache so we know it's the head element
            // and that this will be a valid value.
            unsafe { self.cache.get_head_ref_unchecked() }
        }
    }

    /// Gets a value only if it is in the cache
    ///
    /// If the parameter value pair exists in the cache, a reference to the value will be returned.
    /// This method will not call the underlying function that is being cached. Additionally, the
    /// ordering of the elements in the mapping will not be updated to make the parameter the new
    /// head.
    ///
    /// # Example
    /// ```
    /// use lru::LRUCache;
    ///
    /// fn add_two(a: usize) -> usize {
    ///     a + 2
    /// }
    ///
    /// let mut cache = LRUCache::<16, usize, usize>::new(add_two);
    /// let _ = cache.get(3);
    /// assert_eq!(cache.get_ref_cached(3), Some(&5));
    /// assert_eq!(cache.get_ref_cached(1), None);
    /// ```
    pub fn get_ref_cached(&self, p: P) -> Option<&V> {
        match self.map.get(&p) {
            Some(i) => {
                // SAFETY: The index came from the map which means an element with that index was
                // valid at some point. As the number of elements in the backing cache can never
                // decrease, this index must point to initialized data whether or not it is the
                // node containing the parameter that is being looked for.
                let entry = unsafe { self.cache.get_arr_ref_unchecked(*i) };
                if *entry.0 == p {
                    Some(entry.1)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    /// Purges the backing map of unused mappings
    ///
    /// This method should be used to help solve the problem of the size of the backing map
    /// potentially growing unbounded. This function will purge the backing map of any entries that
    /// do not exist in the backing linked list.
    ///
    /// # Example
    /// ```
    /// use lru::LRUCache;
    ///
    /// fn double(a: usize) -> usize {
    ///     a + a
    /// }
    ///
    /// let mut lru = LRUCache::<16, usize, usize>::new(double);
    /// for i in 0..32 {
    ///     let _ = lru.get(i);
    /// }
    /// assert_eq!(lru.map_size(), 32);
    /// lru.purge();
    /// assert_eq!(lru.map_size(), 16);
    /// ```
    pub fn purge(&mut self) {
        let values = self.cache.key_set();
        self.map = self.map.drain_filter(|k, _v| !values.contains(k)).collect();
    }
}

impl<const N: usize, P, V> LRUCache<N, P, V>
where
    P: Hash +  Copy + Eq,
    V: Copy + Eq,
{
    /// Same as [`LRUCache::get_ref`] but returns a copy of the value
    pub fn get(&mut self, p: P) -> V {
        if let Some(i) = self.map.get_mut(&p) {
            // SAFETY: The index came from the map which means an element with that index was
            // valid at some point. As the number of elements in the backing cache can never
            // decrease, this index must point to initialized data whether or not it is the
            // node containing the parameter that is being looked for.
            let entry = unsafe { self.cache.get_arr_unchecked(*i) };
            if entry.0 == p {
                // SAFETY: The above safety comment shows why this is a valid index. All that is
                // required for the make_head method is that the index is valid so this is safe.
                unsafe { self.cache.make_head(*i) };
                entry.1
            } else {
                let new_val = (self.func)(p);
                self.cache.push_front((p, new_val));
                *i = self.cache.head_index_unchecked();
                new_val
            }
        } else {
            let new_val = (self.func)(p);
            self.cache.push_front((p, new_val));
            self.map.insert(p, self.cache.head_index_unchecked());
            new_val
        }
    }

    /// Same as [`LRUCache::get_ref_cached`] but returns a copy of the value
    pub fn get_cached(&self, p: P) -> Option<V> {
        match self.map.get(&p) {
            Some(i) => {
                // SAFETY: The index came from the map which means an element with that index was
                // valid at some point. As the number of elements in the backing cache can never
                // decrease, this index must point to initialized data whether or not it is the
                // node containing the parameter that is being looked for.
                let entry = unsafe { self.cache.get_arr_unchecked(*i) };
                if entry.0 == p {
                    Some(entry.1)
                } else {
                    None
                }
            },
            None => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn fib(n: usize) -> usize {
        match n {
            0 => 0,
            1 => 1,
            x => fib(x-1) + fib(x-2),
        }
    }

    #[test]
    fn basic() {
        let mut lru = LRUCache::<128, usize, usize>::new(fib);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get(3), 2);
    }

    #[test]
    fn cache_only() {
        let mut lru = LRUCache::<128, usize, usize>::new(fib);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get_cached(10), None);
        assert_eq!(lru.get_cached(0), Some(0));
    }

    #[test]
    fn refs() {
        let mut lru = LRUCache::<128, usize, usize>::new(fib);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get_ref(3), &2);
        assert_eq!(lru.get_ref(4), &3);
    }

    #[test]
    fn cache_ref() {
        let mut lru = LRUCache::<128, usize, usize>::new(fib);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(0), 0);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(1), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(2), 1);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get(3), 2);
        assert_eq!(lru.get_ref_cached(3), Some(&2));
        assert_eq!(lru.get_ref_cached(4), None);
    }

    #[test]
    fn purge() {
        let mut lru = LRUCache::<16, usize, usize>::new(fib);
        for i in 0..32 {
            let _ = lru.get(i);
        }
        assert_eq!(lru.map_size(), 32);
        lru.purge();
        assert_eq!(lru.map_size(), 16);
    }
}
