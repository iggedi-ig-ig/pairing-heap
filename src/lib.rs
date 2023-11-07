use std::ops::Deref;

use derive_more::Deref;
pub trait Comparable: Copy + Clone + PartialEq + Eq + PartialOrd + Ord {}

pub struct PairingHeap<T>
where
    T: Comparable,
{
    root: Option<*mut PairingHeapNode<T>>,
    min_ptr: Option<*mut PairingHeapNode<T>>,
}

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

    fn cut(&mut self, h: Handle<T>) {
        
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
}
