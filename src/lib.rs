use std::{
    collections::VecDeque,
    fmt::{Debug, Display},
    io::Cursor,
};

use derive_more::Deref;
use thiserror::Error;

/// This is what traits a type must implement so it can be used as a key of a [`PairingHeap`].
pub trait Comparable: Copy + Clone + PartialEq + Eq + PartialOrd + Ord {}

impl<T> Comparable for T where T: Copy + Clone + PartialEq + Eq + PartialOrd + Ord {}

/// A Pairing Heap is an addressable priority queue data structure.
/// It implements the following operations with their (amortized) time complexities:
///
/// # Operations
/// ## Insert - O(1)
/// Inserts a new element to the heap, returning a handle to it.
///
/// ## Remove - O(log n)
/// Removes an element from the heap, given a handle to it.
///
/// ## Merge - O(1)
/// Merges two [`PairingHeap`]s into one larger [`PairingHeap`]
///
/// ## Get Min - O(1)
/// Returns the smallest element from the heap
///
/// ## Pop Min - O(log n)
/// Returns the smallest element from the heap and removes it, updating its state accordingly
///
/// ## Decrease Key - Exact Complexity unknown, between O(log log n) and O(log n)
/// Decreases the priority of an element from the heap, given a pointer to it, and the new key.
#[derive(Default)]
pub struct PairingHeap<T>
where
    T: Comparable,
{
    root: Option<*mut PairingHeapNode<T>>,
    min_ptr: Option<*mut PairingHeapNode<T>>,
}

#[derive(Deref)]
pub struct Handle<T>(*mut PairingHeapNode<T>)
where
    T: Comparable;

impl<T> PairingHeap<T>
where
    T: Comparable,
{
    pub fn insert(&mut self, entry: T) -> Handle<T> {
        self.new_tree(entry)
    }

    pub fn decrease_key(&mut self, h: Handle<T>, new_key: T) -> Result<(), DecreaseKeyError> {
        unsafe {
            let old_key = ***h;
            if old_key < new_key {
                return Err(DecreaseKeyError::KeyLarger);
            }

            (**h).data = new_key;

            if !self.min_ptr.is_some_and(|ptr| **ptr <= new_key) {
                self.min_ptr = Some(*h);
            }

            self.cut(h);
            Ok(())
        }
    }

    pub fn remove(&mut self, h: Handle<T>) {
        unsafe {
            let ptr = *h;
        }
    }

    fn new_tree(&mut self, item: T) -> Handle<T> {
        let new_root = Box::into_raw(Box::new(PairingHeapNode::new_unlinked(item)));

        if let Some(root) = self.root {
            // # Safety
            // This is safe, because
            // - `new_root` was just created using `Box::into_raw` and thus is not null.
            // - if `root` is not `None`, then it was created by us, using `Box::into_raw` and thus also is not null.
            unsafe {
                (*new_root).right_sibling = Some(root);
                (*root).left_sibling_or_parent = Some(new_root);

                self.root = Some(new_root);

                if !self
                    .min_ptr
                    .is_some_and(|current_min| (**current_min) < item)
                {
                    self.min_ptr = Some(new_root);
                }
            }
        } else {
            self.root = Some(new_root);
            self.min_ptr = Some(new_root);
        }

        Handle(new_root)
    }

    fn cut(&mut self, h: Handle<T>) {
        unsafe {
            let ptr = *h;

            if let Some(left_or_parent) = (*ptr).left_sibling_or_parent {
                if (*left_or_parent)
                    .one_child
                    .is_some_and(|child| child == ptr)
                {
                    // I represent all chlidren of my parent. Therefore I need to check if there are more children of my parent, and
                    // if this is the case I need to update my parents child pointer to the next child.

                    if let Some(next_child) = (*ptr).right_sibling {
                        // I have a sibling to the right of me, therefore I need to update its left_or_parent pointer and my parent's one_child pointer.
                        (*left_or_parent).one_child = Some(next_child);
                        (*next_child).left_sibling_or_parent = Some(left_or_parent);
                    } else {
                        (*left_or_parent).one_child = None;
                    }
                } else {
                    // if I am not the `one_child` of my parent, I only need to update the children linked list.
                    if let Some(right) = (*ptr).right_sibling {
                        (*left_or_parent).right_sibling = Some(right);
                        (*right).left_sibling_or_parent = Some(left_or_parent);
                    } else {
                        // if I don't have a right sibling, my left sibling won't have a right sibling after me being cut out anymore.
                        (*left_or_parent).right_sibling = None;
                    }
                }
            } else {
                // If I don't have a parent, I am the left-most root node, thus already a root and therefore don't need to update
                // my left and right pointers.
                return;
            }

            // move sub-tree to be left-most root node.
            self.insert_left(ptr);
        }
    }

    unsafe fn update_min_ptr(&mut self) {
        let mut curr = self.root;
        let mut min = self.min_ptr;
        while let Some(ptr) = curr {
            if !min.is_some_and(|min_ptr| **min_ptr >= **ptr) {
                min = Some(ptr);
            }
            curr = (*ptr).right_sibling;
        }

        self.min_ptr = min;
    }

    unsafe fn pairwise_union(&mut self) {
        let mut curr = self.root;
        let mut last = None;
        while let Some(ptr) = curr {
            if let Some(last_ptr) = last {
                self.union(ptr, last_ptr);
            }
            last = curr;
            curr = (*ptr).right_sibling;
        }
    }

    unsafe fn union(&mut self, a: *mut PairingHeapNode<T>, b: *mut PairingHeapNode<T>) {
        if **a > **b {
            std::ptr::swap(a, b);
        }

        if let Some(child) = (*a).one_child {
            // if a has a child already, we just put b as the right child of that.
        }
    }

    unsafe fn insert_left(&mut self, node: *mut PairingHeapNode<T>) {
        if let Some(root) = self.root {
            (*root).left_sibling_or_parent = Some(node);
            (*node).right_sibling = Some(root);

            if **node < **root {
                self.min_ptr = Some(node);
            }
        } else {
            self.root = Some(node);
            self.min_ptr = Some(node);
        }
    }
}

impl<T> Display for PairingHeap<T>
where
    T: Comparable + Display + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe {
            writeln!(f, "{:?}", self.min_ptr.map(|ptr| **ptr))?;

            let mut curr = self.root;
            while let Some(ptr) = curr {
                write!(f, "{}\t", **ptr)?;
                curr = (*ptr).right_sibling;
            }
            writeln!(f, "")?;
        }
        Ok(())
    }
}

#[derive(Deref)]
pub struct PairingHeapNode<T>
where
    T: Comparable,
{
    #[deref]
    data: T,
    left_sibling_or_parent: Option<*mut Self>,
    right_sibling: Option<*mut Self>,
    one_child: Option<*mut Self>,
}

impl<T> PairingHeapNode<T>
where
    T: Comparable,
{
    pub fn new_unlinked(item: T) -> Self {
        Self {
            data: item,
            left_sibling_or_parent: None,
            right_sibling: None,
            one_child: None,
        }
    }

    unsafe fn insert_left(&mut self, b: *mut Self) {
        if let Some(old_left) = self.left_sibling_or_parent {
            // if I have something left of me, the right pointer of that (which used to be me) has to be updated.
            (*old_left).right_sibling = Some(b);
            self.left_sibling_or_parent = Some(b);
            (*b).right_sibling = (*old_left).right_sibling;
        }
    }
}

/// This enum represents the possilbe errors that can occurr in an invocation of `decrease_key` on a [`PairingHeap`].
#[derive(Error, Debug)]
pub enum DecreaseKeyError {
    #[error("The new key was larger than the original key.")]
    KeyLarger,
}

#[test]
fn test() {
    let mut heap = PairingHeap::default();

    heap.insert(5usize);
    heap.insert(4);
    heap.insert(3);
    let ten = heap.insert(10);

    heap.decrease_key(ten, 1).unwrap();

    println!("{}", heap);
}
