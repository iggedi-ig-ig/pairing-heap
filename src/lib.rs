use std::{
    cell::OnceCell,
    collections::VecDeque,
    fmt::{Debug, Display},
    vec,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingHeapNode<V: Clone> {
    key: i32,
    value: V,
    left_or_parent: Option<*mut Self>,
    right: Option<*mut Self>,
    one_child: Option<*mut Self>,
}

impl<V> Copy for PairingHeapNode<V> where V: Copy + Clone {}

impl<V: Clone> PairingHeapNode<V> {
    fn new(key: i32, value: V) -> Self {
        Self {
            key,
            value,
            left_or_parent: None,
            right: None,
            one_child: None,
        }
    }

    unsafe fn insert_right(&mut self, right: *mut Self) {
        if let Some(old_right) = self.right {
            (*old_right).left_or_parent = Some(right);
            (*right).left_or_parent = Some(self as *mut Self);
            (*right).right = Some(old_right);
            self.right = Some(right);
        } else {
            self.right = Some(right);
            (*right).left_or_parent = Some(self as *mut Self);
        }
    }

    unsafe fn insert_child(&mut self, child: *mut Self) {
        if let Some(one_child) = self.one_child {
            self.one_child = Some(child);
            (*child).insert_right(one_child);
        } else {
            (*child).left_or_parent = Some(self as _);
            self.one_child = Some(child);
        }
    }

    // returns the child pointer, because that has to be attached somewhere else manually.
    unsafe fn destroy(&mut self) -> Option<*mut Self> {
        let left_or_parent = self.left_or_parent;
        let right = self.right;
        let one_child = self.one_child;

        if let Some(left_or_parent) = left_or_parent {
            if self.is_left_parent() {
                if let Some(child) = one_child {
                    (*left_or_parent).insert_child(child);
                } else {
                    (*left_or_parent).one_child = None;
                }
            } else {
                (*left_or_parent).right = right;
            }
        }

        if let Some(right) = right {
            (*right).left_or_parent = left_or_parent;
        }

        one_child
    }

    unsafe fn union(a: *mut Self, b: *mut Self) {
        if (*a).key() > (*b).key() {
            std::ptr::swap(a, b);
        }

        (*a).insert_child(b);
    }

    fn is_left_parent(&self) -> bool {
        !self
            .left_or_parent
            .is_some_and(|pointer| pointer as *const _ != self as *const _)
    }

    fn siblings_iter<'a>(&'a mut self) -> SiblingsRightIter<V> {
        SiblingsRightIter {
            current: Some(self as _),
        }
    }

    pub fn key(&self) -> i32 {
        self.key
    }

    pub fn value(&self) -> &V {
        &self.value
    }

    pub fn key_value(&self) -> (i32, V) {
        (self.key, self.value.clone())
    }
}

impl<V: Clone + Debug> Display for PairingHeapNode<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.key_value())
    }
}

/// An [`Iterator`] over all children of a given [`PairingHeapNode`].
/// They are traversed in bfs order.
pub struct ChildIter<'a, V: Clone> {
    stack: VecDeque<&'a PairingHeapNode<V>>,
}

impl<'a, V: Clone> Iterator for ChildIter<'a, V> {
    type Item = &'a PairingHeapNode<V>;

    fn next(&mut self) -> Option<Self::Item> {
        let front = self.stack.pop_front();
        front
    }
}

/// An [`Iterator`] over all siblings to the right of a given [`PairingHeapNode`].
pub struct SiblingsRightIter<V: Clone> {
    current: Option<*mut PairingHeapNode<V>>,
}

impl<V: Clone> Iterator for SiblingsRightIter<V> {
    type Item = *mut PairingHeapNode<V>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current;
        self.current = current.and_then(|node| unsafe { (*node).right });
        current
    }
}

#[derive(Clone, Debug)]
pub struct PairingHeap<V: Clone> {
    root: Option<*mut PairingHeapNode<V>>,
    curr_min: Option<*mut PairingHeapNode<V>>,
}

impl<V: Clone> PairingHeap<V> {
    /// Creates a new, empty [`PairingHeap`]
    pub fn new() -> Self {
        Self {
            root: None,
            curr_min: None,
        }
    }

    /// Inserts a new element to the heap.
    /// Runtime Complexity: O(1)
    pub fn insert(&mut self, key: i32, value: V) -> *mut PairingHeapNode<V> {
        let node = Box::into_raw(Box::new(PairingHeapNode::new(key, value)));

        if let Some(root) = self.root {
            self.root = Some(node);
            unsafe {
                (*node).insert_right(root);
                self.update_min(node);
            }
        } else {
            self.root = Some(node);
            self.curr_min = Some(node);
        }
        node
    }

    /// Removes an element from the heap, returning it if it was present.
    /// Runtime complexity: Between O(log log n) and O(log n)
    pub fn remove(&mut self, element: *mut PairingHeapNode<V>) -> Option<(i32, V)> {
        if let Some(children) = unsafe { (*element).destroy() } {}

        // drop element
        self.pairwise_union();
        todo!()
    }

    /// Returns the smallest element from the heap.
    /// Runtime complexity: O(1)
    pub fn get_min(&self) -> Option<(i32, V)> {
        unsafe { self.curr_min.map(|min| (*min).key_value()) }
    }

    /// Returns the smallest element from the heap, removing it from it in the process.
    /// Runtime complexity: Between O(log log n) and O(log n)
    pub fn pop_min(&mut self) -> Option<(i32, V)> {
        self.pairwise_union();
        self.find_new_min();
        todo!()
    }

    /// Decreases the key of a given element of the heap.
    /// Runtime complexity: O(1)
    pub fn decrease_key(&mut self, new_key: i32, handle: *mut PairingHeapNode<V>) {
        todo!()
    }

    /// Merges two [`PairingHeap`]s into one, returning it.
    /// Runtime complexity: O(1)
    pub fn merge(mut self, mut other: Self) -> Self {
        let mut new_root = self.root.or(other.root);

        todo!()
    }

    /// Returns an iterator over the roots of this [`PairingHeap`].
    pub fn roots_iter<'a>(&self) -> SiblingsRightIter<V> {
        SiblingsRightIter { current: self.root }
    }

    fn pairwise_union(&mut self) {
        let mut last = None;
        let mut iter = self.roots_iter().collect::<Vec<_>>().into_iter();

        while let Some(next) = iter.next() {
            if let Some(previous) = last {
                unsafe { PairingHeapNode::union(next, previous) };
                last = None;
            } else {
                last = Some(next)
            }
        }
    }

    unsafe fn update_min(&mut self, new_element: *mut PairingHeapNode<V>) {
        self.curr_min = Some(self.curr_min.map_or(new_element, |value| {
            if (*value).key() > (*new_element).key() {
                value
            } else {
                new_element
            }
        }))
    }

    fn find_new_min(&mut self) {
        self.curr_min = self.roots_iter().min_by_key(|ptr| unsafe { (**ptr).key() });
    }
}

#[cfg(test)]
mod test {
    use crate::PairingHeap;

    #[test]
    fn test_roots() {
        let mut pairing_heap = PairingHeap::new();

        pairing_heap.insert(5, "world");
        pairing_heap.insert(4, "hello");
        pairing_heap.insert(6, "hello");
        pairing_heap.insert(4, "yeah");
        pairing_heap.insert(1, "smol");

        let mut roots_iter = pairing_heap.roots_iter().map(|ptr| unsafe { &*ptr });

        assert_eq!(roots_iter.next().map(|node| *node.value()), Some("smol"));
        assert_eq!(roots_iter.next().map(|node| *node.value()), Some("yeah"));
        assert_eq!(roots_iter.next().map(|node| *node.value()), Some("hello"));
        assert_eq!(roots_iter.next().map(|node| *node.value()), Some("hello"));
        assert_eq!(roots_iter.next().map(|node| *node.value()), Some("world"));
        assert_eq!(roots_iter.next(), None);

        for root in pairing_heap.roots_iter().map(|ptr| unsafe { &*ptr }) {
            println!("{}", root);
        }
    }
}
