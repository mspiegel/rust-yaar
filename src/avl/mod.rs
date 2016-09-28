use std::cmp;
use std::cmp::Ordering;
use std::mem;

#[derive(Default, Debug)]
pub struct AVLTree {
    root: Option<Box<Node>>,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
enum Children {
    Empty,
    Leaf,
    Left,
    Right,
    Full,
}

#[derive(Debug)]
struct Node {
    key: i32,
    val: i32,
    height: u32,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl AVLTree {
    /// Makes a new empty AVLTree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::avl::AVLTree;
    ///
    /// let mut map = AVLTree::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, 1);
    /// ```
    pub fn new() -> AVLTree {
        Default::default()
    }

    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::avl::AVLTree;
    ///
    /// let mut map = AVLTree::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.get(1), Some(1));
    /// assert_eq!(map.get(2), None);
    /// ```
    pub fn get(&self, key: i32) -> Option<i32> {
        self.root.get(key)
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::avl::AVLTree;
    ///
    /// let mut a = AVLTree::new();
    /// assert!(a.is_empty());
    /// a.insert(1, 1);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
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
    /// use yaar::avl::AVLTree;
    ///
    /// let mut map = AVLTree::new();
    /// assert_eq!(map.insert(37, 1), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, 2);
    /// assert_eq!(map.insert(37, 3), Some(2));
    /// ```
    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        self.root.insert(key, value)
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::avl::AVLTree;
    ///
    /// let mut map = AVLTree::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(1), Some(1));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: i32) -> Option<i32> {
        self.root.remove(key)
    }
}

impl Node {
    fn leaf(key: i32, val: i32) -> Node {
        Node {
            key: key,
            val: val,
            height: 1,
            left: None,
            right: None,
        }
    }

    fn min(&self) -> (i32, i32) {
        match self.left {
            None => (self.key, self.val),
            Some(ref left) => left.min(),
        }
    }

    fn balance(&self) -> i32 {
        let left = self.left.height() as i32;
        let right = self.right.height() as i32;
        left - right
    }

    fn update_height(&mut self) {
        self.height = cmp::max(self.left.height(), self.right.height()) + 1;
    }

    fn insert_rebalance(&mut self, key: i32) {
        let balance = self.balance();
        if balance > 1 {
            match key.cmp(&self.left.key()) {
                Ordering::Less => self.right_rotate(),
                Ordering::Equal => panic!("key {} appears more than once", key),
                Ordering::Greater => self.left_right_rotate(),
            }
        } else if balance < -1 {
            match key.cmp(&self.right.key()) {
                Ordering::Less => self.right_left_rotate(),
                Ordering::Equal => panic!("key {} appears more than once", key),
                Ordering::Greater => self.left_rotate(),
            }
        }
    }

    fn delete_rebalance(&mut self) {
        let balance = self.balance();
        if balance > 1 {
            if self.left.balance() >= 0 {
                self.right_rotate();
            } else {
                self.left_right_rotate();
            }
        } else if balance < -1 {
            if self.right.balance() <= 0 {
                self.left_rotate();
            } else {
                self.right_left_rotate();
            }
        }
    }

    fn left_rotate(&mut self) {
        let mut child = self.right.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.right, &mut self.left);
        child.update_height();
        self.left = Some(child);
        self.update_height();
    }

    fn right_rotate(&mut self) {
        let mut child = self.left.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.left, &mut self.right);
        child.update_height();
        self.right = Some(child);
        self.update_height();
    }

    fn left_right_rotate(&mut self) {
        self.left.mutate().left_rotate();
        self.right_rotate();
    }

    fn right_left_rotate(&mut self) {
        self.right.mutate().right_rotate();
        self.left_rotate();
    }
}

trait OptionBoxNode {
    fn get(&self, key: i32) -> Option<i32>;
    fn height(&self) -> u32;
    fn balance(&self) -> i32;
    fn insert(&mut self, key: i32, val: i32) -> Option<i32>;
    fn remove(&mut self, key: i32) -> Option<i32>;
    fn reference(&self) -> &Box<Node>;
    fn mutate(&mut self) -> &mut Box<Node>;
    fn key(&self) -> i32;
    fn children(&self) -> Children;
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

    fn height(&self) -> u32 {
        match *self {
            None => 0,
            Some(ref node) => node.height,
        }
    }

    fn balance(&self) -> i32 {
        match *self {
            None => 0,
            Some(ref node) => node.balance(),
        }
    }

    fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = match *self {
            None => {
                *self = new_leaf(key, value);
                None
            }
            Some(ref mut node) => {
                match key.cmp(&node.key) {
                    Ordering::Equal => {
                        let prev = node.val;
                        node.val = value;
                        Some(prev)
                    }
                    Ordering::Less => node.left.insert(key, value),
                    Ordering::Greater => node.right.insert(key, value),
                }
            }
        };
        let node = self.mutate();
        node.update_height();
        node.insert_rebalance(key);
        prev
    }

    fn remove(&mut self, key: i32) -> Option<i32> {
        if self.is_none() {
            return None;
        }
        let cmp = key.cmp(&self.key());
        let children = self.children();
        let prev = match cmp {
            Ordering::Equal => {
                let prev = self.reference().val;
                match children {
                    Children::Empty => panic!("unexpected missing node"),
                    Children::Leaf => {
                        self.take();
                    }
                    Children::Left => {
                        *self = self.mutate().left.take();
                    }
                    Children::Right => {
                        *self = self.mutate().right.take();
                    }
                    Children::Full => {
                        let node = self.mutate();
                        let succ = node.right.reference().min();
                        node.key = succ.0;
                        node.val = succ.1;
                        node.right.remove(succ.0);
                    }
                };
                Some(prev)
            }
            Ordering::Less => self.mutate().left.remove(key),
            Ordering::Greater => self.mutate().right.remove(key),
        };
        if self.is_some() {
            let node = self.mutate();
            node.update_height();
            node.delete_rebalance();
        }
        prev
    }

    fn key(&self) -> i32 {
        self.as_ref().unwrap().key
    }

    fn reference(&self) -> &Box<Node> {
        self.as_ref().unwrap()
    }

    fn mutate(&mut self) -> &mut Box<Node> {
        self.as_mut().unwrap()
    }

    fn children(&self) -> Children {
        match *self {
            None => Children::Empty,
            Some(ref node) => {
                if node.left.is_none() && node.right.is_none() {
                    Children::Leaf
                } else if node.right.is_none() {
                    Children::Left
                } else if node.left.is_none() {
                    Children::Right
                } else {
                    Children::Full
                }
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
        let mut tree = AVLTree::new();
        assert_eq!(tree.get(0), None);
        assert_eq!(tree.insert(0, 1), None);
        assert_eq!(tree.insert(0, 2), Some(1));
        assert_eq!(tree.get(0), Some(2));
    }

    #[test]
    fn insert_sequence() {
        let mut tree = AVLTree::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.get(i), Some(i));
        }
    }

    #[test]
    fn remove() {
        let mut tree = AVLTree::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove(i), Some(i));
            assert_eq!(tree.remove(i), None);
        }
    }

}
