//! This module is an internal structure for storing the linked list that will remember the order
//! in which elements should be removed from the LRU cache.

use std::default::Default;
use std::iter::{IntoIterator, Iterator, ExactSizeIterator};
use std::mem::MaybeUninit;
use std::collections::HashSet;
use std::hash::Hash;
use std::fmt;

/// Internal struct for holding the values in the linked list array
///
/// This struct should not be exposed in any of the public interfaces.
/// This struct is generic over both the key and value that a LRU cache might use. The key is the
/// parameter type that is passed to a function and the value is the return value of that function.
#[derive(Clone, Copy)]
struct Node<K, V> {
    /// Index of the previous entry in the linked list
    prev: usize,
    /// Index of the next entry in the linked list
    next: usize,
    /// Key value at this node
    key: K,
    /// Value at this node
    value: V,
}

impl<K, V> Node<K, V> {
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
    K: Default,
    V: Default,
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
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "Node({}, {}, {:?}, {:?})", self.prev, self.next, self.key, self.value)
    }
}

/// A constant sized doubly linked circular list
///
/// The design of this collection is for backing an LRU cache. It will keep track of the key, value
/// pairs that a function can produce. The key needs to be kept track of in this structure because
/// the actual LRU cache will not remove the key, index pairs from the hash map when that index is
/// assigned a new pair.
///
/// This collection is designed to have constant time operations for all operations that the LRU
/// cache requires. Adding a new as the head and getting a specific array index are both constant
/// time operations. These are the main two operations that the LRU cache will require and so this
/// structure was optimized for those operations.
///
/// As the linked list is a constant size, it is represented as a statically sized array of nodes
/// to speed up all of the operations. The linked list can then give out indices to specific
/// elements that the LRU cache can remember and directly index to to quickly get a specific node.
/// By keeping track of the head and the tail indices, a new head can be inserted in constant time
/// by ejecting the tail and updating the index references of neighboring nodes.
///
/// Another important operation for the LRU cache is updating an element to be the new head of the
/// linked list. That indicates that an element was recently accessed and should be the new most
/// recent elemtn of the list. This can also be done in constant time if the index of the element
/// that should be the new head is known. To do this operation, that index is removed from the
/// linked list and reinserted as the head.
///
/// # Safety
/// This collection uses a lot of unsafe code. I'm fairly certain that there is no
/// undefined behavior but this library should not be used in an y production environment where
/// that is a worry. The main reason for all of the unsafe code is that the underlying array of
/// elements consists of [`MaybeUninit`] values of the [`Node`] structure so that they don't all
/// have to be initialized when the collection is made. In addition, that underlying array has to
/// remain as potentially uninitialized values because they may never be initialized if fewere than
/// N elements are ever inserted into the linked list. Because of that, every time an element is
/// accessed from the list, it needs to be assumed as initialized which is an unsafe operation.
///
/// All of the safe methods on this collection should never incorrectly access or return an
/// uninitialized value from the backing array. The number of elements added to the array is kept
/// track of internally. Any time an index past that size is accessed the method should return a
/// None value. However, the unsafe functions do not check that the index is valid and may access,
/// modify, or return an uninitialized value.
///
/// One of the ways that safety is maintained is that new entries are always populated into the
/// first unitialized element in the backing array until it is full. This ensures the invariant
/// that the first `self.size` elements are initialized at any point in time. This invariant is
/// used in many of the methods of the linked list to ensure safety and quick operations on the
/// linked list.
pub struct ConstLinkedList<const N: usize, K, V> {
    /// Number of elements currently in the array
    size: usize,
    /// Index of the head element
    head: usize,
    /// Index of the tail element
    tail: usize,
    /// Backing storage of each of the nodes in the array
    nodes: [MaybeUninit<Node<K, V>>; N],
}

impl<const N: usize, K, V> Default for ConstLinkedList<N, K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize, K, V> ConstLinkedList<N, K, V> {
    /// Creates a new linked list with all of the elements left uninitialized
    #[must_use]
    pub fn new() -> Self {
        Self {
            size: 0,
            head: 0,
            tail: 0,
            nodes: MaybeUninit::uninit_array(),
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

    /// Retrieves the index of the head element in the backing array
    ///
    /// This function does not check to ensure an element has been inserted into the array and just
    /// blindly returns the index of the head element. This function is safe because it cannot on
    /// its own cause any undefined behavior or break any of rust's safety rules. To actually do
    /// something unsafe with the value returned you would have to call another unsafe function
    /// with this value. As the user would have to still call an unsafe method after calling this
    /// method, it has not been marked unsafe.
    ///
    /// You may use the [`ConstLinkedList::head_index`] method as a safer version of this method.
    pub fn head_index_unchecked(&self) -> usize {
        self.head
    }

    /// Adds an element to the front of the linked list
    ///
    /// If the linked list is full, the last element will be removed and replaced with the new one.
    /// The head and tail of the list will then be updated.
    pub fn push_front(&mut self, value: (K, V)) {
        unsafe {
            if self.size < N {
                // Can just place the new node at the first empty spot and then make it the head.
                //
                // SAFETY: The first thing that is done is insert a new node into the linked list.
                // That means that there is a valid element in the list and that head and tail will
                // necessarily point to initialized elements as if there were initially no elements
                // they will both be pointing to the newly inserted element. The following accesses
                // will then only dereference initialized values making everything safe.
                self.nodes[self.size].write(Node::new(value.0, value.1, self.head, self.tail));
                self.nodes[self.head].assume_init_mut().prev = self.size;
                self.nodes[self.tail].assume_init_mut().next = self.size;
                self.head = self.size;
                self.size += 1;
            } else {
                // Need to replace the tail with the new node and make it the head.
                //
                // SAFETY: In this branch of the if else clause, we know all of the elements of the
                // array are initialized and valid so assuming anything is initialized is correct.
                self.nodes[self.tail].assume_init_mut().key = value.0;
                self.nodes[self.tail].assume_init_mut().value = value.1;
                self.head = self.tail;
                self.tail = self.nodes[self.head].assume_init_ref().prev;
            }
        }
    }

    /// Change an index to be the head of the linked list
    ///
    /// # Safety
    /// This function does not check the index to make sure that the index is valid.
    pub unsafe fn make_head(&mut self, index: usize) {
        if index == self.head { return; }
        let tmp_prev = self.nodes[index].assume_init_ref().prev;
        let tmp_next = self.nodes[index].assume_init_ref().next;
        self.nodes[tmp_prev].assume_init_mut().next = self.nodes[index].assume_init_ref().next;
        self.nodes[tmp_next].assume_init_mut().prev = self.nodes[index].assume_init_ref().prev;
        self.nodes[index].assume_init_mut().next = self.head;
        self.nodes[index].assume_init_mut().prev = self.tail;
        self.nodes[self.head].assume_init_mut().prev = index;
        self.nodes[self.tail].assume_init_mut().next = index;
        self.head = index;
    }

    /// Same as [`ConstLinkedList::get_linked`] but returns a reference to the key value pair
    ///
    /// Returns `None` if the index is invalid.
    pub fn get_linked_ref(&self, index: usize) -> Option<(&K, &V)> {
        if index >= self.size {
            return None;
        }
        // SAFETY: No node can reference an unitialized node. Therefore is is safe to iterate
        // through them as a linked list as none of them will cause an initialized node to be
        // referenced.
        unsafe {
            let mut curr_node = self.nodes[self.head].assume_init_ref();
            let mut curr_index = 0;
            while curr_index < index {
                curr_node = self.nodes[curr_node.next].assume_init_ref();
                curr_index += 1;
            }
            Some((&curr_node.key, &curr_node.value))
        }
    }

    /// Get a reference to a value based on the index of the backing array
    ///
    /// This method will check to ensure that the index is valid and will return None if there is
    /// not a valid element at that address.
    pub fn get_arr_ref(&self, index: usize) -> Option<(&K, &V)> {
        if index >= self.size {
            None
        } else {
            // SAFETY: There is at least one element in the list so the head will point to a valid
            // initialized node.
            let node = unsafe { self.nodes[index].assume_init_ref() };
            Some((&node.key, &node.value))
        }
    }

    /// Same as [`ConstLinkedList::get_arr_ref`] but does not check to ensure that the index is
    /// valid
    ///
    /// # Safety
    /// Caller must assure that the index references a valid entry in the backing list.
    pub unsafe fn get_arr_ref_unchecked(&self, index: usize) -> (&K, &V) {
        let node = self.nodes[index].assume_init_ref();
        (&node.key, &node.value)
    }

    /// Get a reference to the head element of the list
    ///
    /// # Safety
    /// Caller must assure that there is at least one element that has been inserted into the list.
    pub unsafe fn get_head_ref_unchecked(&self) -> &V {
        unsafe { &self.nodes[self.head].assume_init_ref().value }
    }
}

impl<const N: usize, K, V> ConstLinkedList<N, K, V>
where
    K: Copy,
    V: Copy,
{
    /// Get the `index`th element indexing by linked list entry
    ///
    /// Returns `None` if the index is greater than the size.
    pub fn get_linked(&self, index: usize) -> Option<(K, V)> {
        if index >= self.size {
            return None;
        }
        // SAFETY: No node can reference an unitialized node. Therefore is is safe to iterate
        // through them as a linked list as none of them will cause an initialized node to be
        // referenced.
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
            // SAFETY: There is at least one element in the list so the head will point to a valid
            // initialized node.
            let node = unsafe { self.nodes[index].assume_init_ref() };
            Some((node.key, node.value))
        }
    }

    /// Same as [`ConstLinkedList::get_arr`] but doesn't check if `index` is a valid value
    ///
    /// # Safety
    /// Caller needs to ensure that the index references an initialized value in the
    /// backing array.
    pub unsafe fn get_arr_unchecked(&self, index: usize) -> (K, V) {
        let node = self.nodes[index].assume_init_ref();
        (node.key, node.value)
    }

    /// Gets the head element of the list
    ///
    /// Returns `None` if there are no elements in the list.
    pub fn get_head(&self) -> Option<(K, V)> {
        if self.size > 0 {
            // SAFETY: There is at least one element in the list so head must point to a valid
            // initialized node.
            let node = unsafe { self.nodes[self.head].assume_init_ref() };
            Some((node.key, node.value))
        } else {
            None
        }
    }
}

impl<const N: usize, K, V> ConstLinkedList<N, K, V>
where
    K: Clone + Eq + Hash,
{
    /// Get a set of the the keys in the linked list
    pub fn key_set(&self) -> HashSet<K> {
        let mut keys = HashSet::with_capacity(self.size);
        for i in 0..self.size {
            // SAFETY: The fist `self.size` elements are the ones that have been initialized. It is
            // therefore safe to assume they are initialized and access them.
            unsafe { keys.insert(self.nodes[i].assume_init_ref().key.clone()) };
        }
        keys
    }
}

impl<const N: usize, K, V> Drop for ConstLinkedList<N, K, V> {
    // The backing storage of the nodes is always [`MaybeUninit`] which means they won't
    // automatically get dropped when the collection is dropped. We need to go through all of the
    // initialized elements and manually drop them.
    fn drop(&mut self) {
        for i in 0..self.size {
            // SAFETY: The first `self.size` elements are the ones that have been initialized with
            // actual data so those ones are safe to assume are initialized and then drop.
            unsafe { self.nodes[i].assume_init_drop() };
        }
    }
}

// This trait implementation is not really necessary. Having it just makes some testing easier
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
            iter_index: 0,
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
    iter_index: usize,
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
            if self.total_vals == self.iter_index {
                return None;
            } else {
                let val = self.nodes[self.curr_index].assume_init_ref().value;
                self.curr_index = self.nodes[self.curr_index].assume_init_ref().next;
                self.iter_index += 1;
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
        self.total_vals - self.iter_index
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

    #[test]
    fn empty_iterator() {
        // I found some ub with iterating over a linked list when it has zero elements in it. This
        // test should check to make sure that doesn't happen again.
        let cache = ConstLinkedList::<16, usize, usize>::new();
        for _n in cache {
            assert!(false);
        }
        assert!(true);
    }

    #[test]
    fn single_iterator() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((1, 1));
        let mut iter = cache.into_iter();
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn linked_index() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((1, 1));
        let val = cache.get_linked(0);
        assert_eq!(val, Some((1, 1)));
    }

    #[test]
    fn linked_ref_index() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((1, 1));
        let val = cache.get_linked_ref(0);
        assert_eq!(val, Some((&1, &1)));
    }

    #[test]
    fn arr_index() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((1, 1));
        let val = cache.get_arr(0);
        assert_eq!(val, Some((1, 1)));
    }

    #[test]
    fn arr_ref_index() {
        let mut cache = ConstLinkedList::<16, usize, usize>::new();
        cache.push_front((1, 1));
        let val = cache.get_arr_ref(0);
        assert_eq!(val, Some((&1, &1)));
    }
}
