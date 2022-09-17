use std::default::Default;
use std::iter::{IntoIterator, Iterator, ExactSizeIterator};
use std::mem::MaybeUninit;
use std::collections::HashSet;
use std::hash::Hash;
use std::fmt;

/// Internal struct for holding the values in the linked list array
///
/// This struct should not be exposed in any of the public interfaces.
#[derive(Clone, Copy)]
struct Node<K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    /// Index of the previous entry in the linked list
    pub prev: usize,
    /// Index of the next entry in the linked list
    pub next: usize,
    /// Key value at this node
    pub key: K,
    /// Value at this node
    pub value: V,
}

impl<K, V> Node<K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    /// Creates a new node with the given next and previous indices and value
    pub fn new(key: K, val: V, next: usize, prev: usize) -> Self {
        Self {
            prev,
            next,
            key,
            value: val,
        }
    }
}

impl<K, V> Default for Node<K, V>
where
    K: Default + Clone + Copy,
    V: Default + Clone + Copy,
{
    fn default() -> Self {
        Self {
            prev: 0,
            next: 0,
            key: K::default(),
            value: V::default(),
        }
    }
}

impl<K, V> fmt::Debug for Node<K, V>
where
    K: Clone + Copy + fmt::Debug,
    V: Clone + Copy + fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "Node({}, {}, {:?}, {:?})", self.prev, self.next, self.key, self.value)
    }
}

/// A constant sized linked list
///
/// The design of this collection is for backing an LRU cache.
pub struct ConstLinkedList<const N: usize, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    size: usize,
    head: usize,
    tail: usize,
    nodes: [MaybeUninit<Node<K, V>>; N],
}

impl<const N: usize, K, V> ConstLinkedList<N, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    /// Create a new linked list of default elements
    ///
    /// The size of the linked list will still be zero.
    pub fn new() -> Self {
        Self {
            size: 0,
            head: 0,
            tail: 0,
            nodes: MaybeUninit::uninit_array(),
        }
    }

    /// Get the `index`th element indexing by linked list entry
    ///
    /// Returns `None` if the index is greater than the size.
    pub fn get_linked(&self, index: usize) -> Option<(K, V)> {
        if index >= self.size {
            return None;
        }
        unsafe {
            let mut curr_node = self.nodes[self.head].assume_init_ref();
            let mut curr_index = 0;
            while curr_index < index {
                curr_node = self.nodes[curr_node.next].assume_init_ref();
                curr_index += 1;
            }
            Some((curr_node.key, curr_node.value))
        }
    }

    /// Get the `index`th element indexing directly into the backing array
    ///
    /// Returns `None` if the index is greater than the size.
    pub fn get_arr(&self, index: usize) -> Option<(K, V)> {
        if index >= self.size {
            None
        } else {
            let node = &unsafe { self.nodes[index].assume_init() };
            Some((node.key, node.value))
        }
    }

    /// Same as [`get_arr`] but doesn't check if index is greater than the size of the array
    ///
    /// SAFETY: Caller needs to ensure that the index references a valid in range value.
    pub unsafe fn get_arr_unchecked(&self, index: usize) -> (K, V) {
        let node = &self.nodes[index].assume_init();
        (node.key, node.value)
    }

    /// Adds an element to the front of the linked list
    ///
    /// If the linked list is full, the last element will be removed and replaced with the new one.
    /// The head and tail of the list will then be updated.
    pub fn push_front(&mut self, value: (K, V)) {
        unsafe {
            if self.size < N {
                // Can just place the new node at the first empty spot and then make it the head.
                self.nodes[self.size].write(Node::new(value.0, value.1, self.head, self.tail));
                self.nodes[self.head].assume_init().prev = self.size;
                self.nodes[self.tail].assume_init().next = self.size;
                self.head = self.size;
                self.size += 1;
            } else {
                // Need to replace the tail with the new node and make it the head.
                self.nodes[self.tail].assume_init().key = value.0;
                self.nodes[self.tail].assume_init().value = value.1;
                self.head = self.tail;
                self.tail = self.nodes[self.head].assume_init().prev;
            }
        }
    }

    /// Gets the head element of the list
    ///
    /// Returns `None` if there are no elements in the list.
    pub fn get_head(&self) -> Option<(K, V)> {
        if self.size > 0 {
            let node = &unsafe { self.nodes[self.head].assume_init() };
            Some((node.key, node.value))
        } else {
            None
        }
    }

    /// Get the index of the head element in the backing array
    pub fn head_index(&self) -> Option<usize> {
        if self.size > 0 {
            Some(self.head)
        } else {
            None
        }
    }

    /// Change an index to be the head of the linked list
    ///
    /// SAFETY: This function does not check the index to make sure that the index is valid.
    pub unsafe fn make_head(&mut self, index: usize) {
        if index == self.head { return; }
        let tmp_prev = self.nodes[index].assume_init().prev;
        let tmp_next = self.nodes[index].assume_init().next;
        self.nodes[tmp_prev].assume_init().next = self.nodes[index].assume_init().next;
        self.nodes[tmp_next].assume_init().prev = self.nodes[index].assume_init().prev;
        self.nodes[index].assume_init().next = self.head;
        self.nodes[index].assume_init().prev = self.tail;
        self.nodes[self.head].assume_init().prev = index;
        self.nodes[self.tail].assume_init().next = index;
        self.head = index;
    }
}

impl<const N: usize, K, V> ConstLinkedList<N, K, V>
where
    K: Clone + Copy + Eq + Hash,
    V: Clone + Copy,
{
    pub fn key_set(&self) -> HashSet<K> {
        let mut keys = HashSet::with_capacity(self.size);
        for i in 0..self.size {
            unsafe { keys.insert(self.nodes[i].assume_init().key) };
        }
        keys
    }
}

impl<const N: usize, K, V> IntoIterator for ConstLinkedList<N, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    type Item = V;
    type IntoIter = ListIterator<N, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            curr_index: self.head,
            total_vals: self.size,
            tail_index: self.tail,
            nodes: self.nodes,
        }
    }
}

pub struct ListIterator<const N: usize, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    curr_index: usize,
    total_vals: usize,
    tail_index: usize,
    nodes: [MaybeUninit<Node<K, V>>; N],
}

impl<const N: usize, K, V> Iterator for ListIterator<N, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.nodes[self.curr_index].assume_init().prev == self.tail_index {
                None
            } else {
                let val = self.nodes[self.curr_index].assume_init().value;
                self.curr_index = self.nodes[self.curr_index].assume_init().next;
                Some(val)
            }
        }
    }
}

impl<const N: usize, K, V> ExactSizeIterator for ListIterator<N, K, V>
where
    K: Clone + Copy,
    V: Clone + Copy,
{
    fn len(&self) -> usize {
        self.total_vals
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn push_one() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((10, 10));
        assert_eq!(cache.get_linked(0), Some((10, 10)));
    }

    #[test]
    fn push_size() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        for i in 0..16 {
            cache.push_front((i, i));
        }
        for i in 0..16 {
            assert_eq!(cache.get_linked(i), Some((15-i, 15-i)));
        }
    }

    #[test]
    fn basic_iter() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        for i in 0..16 {
            cache.push_front((i, i));
        }
        for (i, n) in cache.into_iter().enumerate() {
            assert_eq!(n, (15-i));
        }
    }

    #[test]
    fn head_index() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        for i in 0..16 {
            cache.push_front((i, i));
        }
        assert_eq!(cache.head_index(), Some(15));
    }

    #[test]
    fn ejection() {
        let mut cache = ConstLinkedList::<10, usize, usize>::new();
        for i in 0..100 {
            cache.push_front((i, i));
        }
        for v in cache {
            assert!((90..100).contains(&v));
        }
    }

    #[test]
    fn make_head() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        for i in 0..16 {
            cache.push_front((i, i));
        }
        assert_eq!(cache.get_head(), Some((15, 15)));
        unsafe { cache.make_head(0); }
        assert_eq!(cache.get_head(), Some((0, 0)));
    }
}
