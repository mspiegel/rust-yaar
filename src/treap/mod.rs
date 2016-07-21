use rand;

use std::cmp::Ordering;
use std::mem;

#[derive(Default, Debug)]
pub struct Treap {
    root: Option<Box<Node>>,
}

#[derive(Debug)]
struct Node {
    key: i32,
    val: i32,
    priority: u64,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Treap {
    /// Makes a new empty Treap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::treap::Treap;
    ///
    /// let mut map = Treap::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, 1);
    /// ```
    pub fn new() -> Treap {
        Default::default()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::treap::Treap;
    ///
    /// let mut a = Treap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, 1);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::treap::Treap;
    ///
    /// let mut map = Treap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.get(1), Some(1));
    /// assert_eq!(map.get(2), None);
    /// ```
    pub fn get(&self, key: i32) -> Option<i32> {
        self.root.get(key)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::treap::Treap;
    ///
    /// let mut map = Treap::new();
    /// assert_eq!(map.insert(37, 1), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, 2);
    /// assert_eq!(map.insert(37, 3), Some(2));
    /// ```
    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = self.root.insert(key, value);
        self.check();
        prev
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::treap::Treap;
    ///
    /// let mut map = Treap::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(1), Some(1));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: i32) -> Option<i32> {
        let prev = self.root.remove(key);
        self.check();
        prev
    }

    /// Returns true if the tree satisfies the binary
    /// search tree propery of a treap.
    fn is_bst(&self) -> bool {
        self.root.is_bst(None, None)
    }

    /// Returns true if the tree satisfies the
    /// heap propery of a treap.
    fn is_heap(&self) -> bool {
        self.root.is_heap()
    }

    /// Applies all the invariant tests on the
    /// binary search tree. Tests are only
    /// applied in the debug! context.
    fn check(&self) {
        debug_assert!(self.is_bst(), "Not a binary search tree");
        debug_assert!(self.is_heap(), "Not a heap");
    }
}

impl Node {
    fn leaf(key: i32, val: i32) -> Node {
        Node {
            key: key,
            val: val,
            priority: rand::random(),
            left: None,
            right: None,
        }
    }

    fn left(&self) -> &Box<Node> {
        self.left.as_ref().unwrap()
    }

    fn right(&self) -> &Box<Node> {
        self.right.as_ref().unwrap()
    }

    fn left_rotate(&mut self) {
        let mut child = self.right.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.right, &mut self.left);
        self.left = Some(child);
    }

    fn right_rotate(&mut self) {
        let mut child = self.left.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.left, &mut self.right);
        self.right = Some(child);
    }
}

trait OptionBoxNode {
    fn get(&self, key: i32) -> Option<i32>;
    fn insert(&mut self, key: i32, value: i32) -> Option<i32>;
    fn remove(&mut self, key: i32) -> Option<i32>;
    fn rotate_to_leaf(&mut self);
    fn is_bst(&self, min: Option<i32>, max: Option<i32>) -> bool;
    fn is_heap(&self) -> bool;
    fn mutate(&mut self) -> &mut Box<Node>;
    fn key(&self) -> i32;
    fn val(&self) -> i32;
    fn left(&mut self) -> &mut Option<Box<Node>>;
    fn right(&mut self) -> &mut Option<Box<Node>>;
}

impl OptionBoxNode for Option<Box<Node>> {
    fn get(&self, key: i32) -> Option<i32> {
        match *self {
            None => None,
            Some(ref node) => {
                match key.cmp(&node.key) {
                    Ordering::Equal => Some(node.val),
                    Ordering::Less => node.left.get(key),
                    Ordering::Greater => node.right.get(key),
                }
            }
        }
    }

    fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        match *self {
            None => {
                *self = new_leaf(key, value);
                None
            }
            Some(ref mut node) => {
                let priority = node.priority;
                match key.cmp(&node.key) {
                    Ordering::Equal => {
                        let prev = node.val;
                        node.val = value;
                        Some(prev)
                    }
                    Ordering::Less => {
                        let prev = node.left.insert(key, value);
                        if node.left().priority.lt(&priority) {
                            node.right_rotate();
                        }
                        prev
                    }
                    Ordering::Greater => {
                        let prev = node.right.insert(key, value);
                        if node.right().priority.lt(&priority) {
                            node.left_rotate();
                        }
                        prev
                    }
                }
            }
        }
    }

    fn remove(&mut self, key: i32) -> Option<i32> {
        match *self {
            None => None,
            Some(_) => {
                let target = self.key();
                let val = self.val();
                match key.cmp(&target) {
                    Ordering::Equal => {
                        self.rotate_to_leaf();
                        Some(val)
                    }
                    Ordering::Less => self.left().remove(key),
                    Ordering::Greater => self.right().remove(key),
                }
            }
        }
    }

    fn rotate_to_leaf(&mut self) {
        if self.left().is_none() && self.right().is_none() {
            *self = None;
        } else if self.left().is_none() {
            self.mutate().left_rotate();
            self.left().rotate_to_leaf();
        } else if self.right().is_none() {
            self.mutate().right_rotate();
            self.right().rotate_to_leaf();
        } else {
            let lkey = self.left().key();
            let rkey = self.right().key();
            if lkey.lt(&rkey) {
                self.mutate().right_rotate();
                self.right().rotate_to_leaf();
            } else {
                self.mutate().left_rotate();
                self.left().rotate_to_leaf();
            }
        }
    }

    fn mutate(&mut self) -> &mut Box<Node> {
        self.as_mut().unwrap()
    }

    fn key(&self) -> i32 {
        self.as_ref().unwrap().key
    }

    fn val(&self) -> i32 {
        self.as_ref().unwrap().val
    }

    fn left(&mut self) -> &mut Option<Box<Node>> {
        &mut self.as_mut().unwrap().left
    }

    fn right(&mut self) -> &mut Option<Box<Node>> {
        &mut self.as_mut().unwrap().right
    }

    fn is_heap(&self) -> bool {
        match *self {
            None => true,
            Some(ref node) => {
                let priority = node.priority;
                if node.left.is_some() && node.left().priority.lt(&priority) {
                    return false;
                }
                if node.right.is_some() && node.right().priority.lt(&priority) {
                    return false;
                }
                node.left.is_heap() && node.right.is_heap()
            }
        }
    }

    fn is_bst(&self, min: Option<i32>, max: Option<i32>) -> bool {
        match *self {
            None => true,
            Some(ref node) => {
                if min.is_some() && node.key.cmp(&min.unwrap()) != Ordering::Greater {
                    return false;
                }
                if max.is_some() && node.key.cmp(&max.unwrap()) != Ordering::Less {
                    return false;
                }
                node.left.is_bst(min, Some(node.key)) && node.right.is_bst(Some(node.key), max)
            }
        }
    }
}

fn new_leaf(key: i32, val: i32) -> Option<Box<Node>> {
    Some(Box::new(Node::leaf(key, val)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_construction() {
        let mut tree = Treap::new();
        assert_eq!(tree.get(0), None);
        assert_eq!(tree.insert(0, 1), None);
        assert_eq!(tree.insert(0, 2), Some(1));
        assert_eq!(tree.get(0), Some(2));
    }

    #[test]
    fn insert_sequence() {
        let mut tree = Treap::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.get(i), Some(i));
        }
    }

    #[test]
    fn remove() {
        let mut tree = Treap::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove(i), Some(i));
            assert_eq!(tree.remove(i), None);
        }
    }

}
