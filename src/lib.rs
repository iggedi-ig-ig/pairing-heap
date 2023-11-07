use derive_more::Deref;
use thiserror::Error;

/// This is what traits a type must implement so it can be used as a key of a [`PairingHeap`].
pub trait Comparable: Copy + Clone + PartialEq + Eq + PartialOrd + Ord {}

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

    pub fn decrease_key(&mut self, h: Handle<T>, new_key: T) {
        unsafe {
            let old_key = ***h;
            if old_key < new_key {
                // TODO: return Err()
                panic!("Invalid argument: new_key must be smaller than the old key.")
            }
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
                    .is_some_and(|current_min| (**current_min) > item)
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

    fn cut(&mut self, h: Handle<T>) {}
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
}

/// This enum represents the possilbe errors that can occurr in an invocation of `decrease_key` on a [`PairingHeap`].
#[derive(Error, Debug)]
pub enum DecreaseKeyError {
    #[error("The new key was larger than the original key.")]
    KeyLarger,
}
