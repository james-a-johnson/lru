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

use std::hash::Hash;

use bimap::hash::BiHashMap as BiMap;

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
pub struct LRUCache<const N: usize, P, V>
where
    P: Hash + Eq,
{
    /// Function that is being cached
    pub func: fn(P) -> V,
    /// Bi directional map of parameters to their index in the linked list
    map: BiMap<P, usize>,
    /// Cache of parameter value pairs
    cache: Box<ConstLinkedList<N, V>>,
}

impl<const N: usize, P, V> LRUCache<N, P, V>
where
    P: Hash + Eq + Clone,
{
    /// Create a new empty cache
    pub fn new(f: fn(P) -> V) -> Self {
        Self {
            func: f,
            map: BiMap::with_capacity(N),
            cache: Box::new(ConstLinkedList::new()),
        }
    }

    /// Get a reference to the returned value of the function
    ///
    /// If the value is in the cache, a reference to the cached value will be returned. Otherwise,
    /// the value will be calculated by calling the function and that will be cached and a
    /// reference to it will be returned.
    ///
    /// The parameter value pair will become the new most recently used value in the cache.
    pub fn get_ref(&mut self, p: P) -> &V {
        if let Some(i) = self.map.get_by_left(&p) {
            // SAFETY: For the index to be in the map it must be valid and point to the correct
            // index.
            unsafe { self.cache.make_head(*i) };
            unsafe { self.cache.get_arr_ref_unchecked(*i) }
        } else {
            let new_val = (self.func)(p.clone());
            self.cache.push_front(new_val);
            let index = self.cache.head_index_unchecked();
            self.map.insert(p, index);
            // SAFETY: Just inserted something at this index so it must be valid.
            unsafe { self.cache.get_arr_ref_unchecked(index) }
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
        match self.map.get_by_left(&p) {
            Some(i) => {
                // SAFETY: The index can only be in the map if it is valid and refers to the
                // correct parameter.
                unsafe { Some(self.cache.get_arr_ref_unchecked(*i)) }
            },
            None => None,
        }
    }
}

impl<const N: usize, P, V> LRUCache<N, P, V>
where
    P: Hash +  Copy + Eq,
    V: Copy + Eq,
{
    /// Same as [`LRUCache::get_ref`] but returns a copy of the value
    pub fn get(&mut self, p: P) -> V {
        if let Some(i) = self.map.get_by_left(&p) {
            // SAFETY: For the index to be in the map, it must be valid.
            unsafe { self.cache.make_head(*i) };
            unsafe { self.cache.get_arr_unchecked(*i) }
        } else {
            let new_val = (self.func)(p);
            self.cache.push_front(new_val);
            self.map.insert(p, self.cache.head_index_unchecked());
            new_val
        }
    }

    /// Same as [`LRUCache::get_ref_cached`] but returns a copy of the value
    pub fn get_cached(&self, p: P) -> Option<V> {
        match self.map.get_by_left(&p) {
            Some(i) => {
                // SAFETY: For the index to be in the map it must be valid.
                unsafe { Some(self.cache.get_arr_unchecked(*i)) }
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
}
