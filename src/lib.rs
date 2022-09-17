#![feature(hash_drain_filter)]
#![feature(maybe_uninit_uninit_array)]

use std::collections::HashMap;
use std::hash::Hash;

pub mod linked;

use linked::ConstLinkedList;

pub struct LRUCache<const N: usize, P, V>
where
    P: Hash + Clone + Copy + Eq,
    V: Clone + Copy,
{
    pub func: fn(P) -> V,
    map: HashMap<P, usize>,
    cache: ConstLinkedList<N, P, V>,
}

impl<const N: usize, P, V> LRUCache<N, P, V>
where
    P: Hash + Clone + Copy + Eq,
    V: Clone + Copy + Hash + Eq,
{
    pub fn new(f: fn(P) -> V) -> Self {
        Self {
            func: f,
            map: HashMap::with_capacity(N),
            cache: ConstLinkedList::new(),
        }
    }

    pub fn get(&mut self, p: P) -> V {
        match self.map.get(&p) {
            Some(i) => {
                let entry = unsafe { self.cache.get_arr_unchecked(*i) };
                if entry.0 == p {
                    unsafe { self.cache.make_head(*i) };
                    return entry.1;
                } else {
                    self.map.remove(&p);
                    let new_val = (self.func)(p);
                    self.cache.push_front((p, new_val));
                    self.map.insert(p, self.cache.head_index().unwrap());
                    return new_val;
                }
            },
            None => {
                let new_val = (self.func)(p);
                self.cache.push_front((p, new_val));
                self.map.insert(p, self.cache.head_index().unwrap());
                return new_val;
            },
        };
    }

    /// Will not update lru recency.
    pub fn get_cached(&self, p: P) -> Option<V> {
        match self.map.get(&p) {
            Some(i) => {
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

    pub fn map_size(&self) -> usize {
        self.map.len()
    }

    pub fn purge(&mut self) {
        let values = self.cache.key_set();
        self.map = self.map.drain_filter(|k, _v| !values.contains(k)).collect();
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
}
