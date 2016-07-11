//! A naive implementation of left-leaning red-black trees
//! that are isomorphic to 2-3 trees. This implementation
//! borrows heavily from https://www.cs.princeton.edu/~rs/talks/LLRB/LLRB.pdf
//! and https://github.com/rcatolino/rbtree-rust.
//! Debug assertions borrow heavily from the implementations
//! at http://algs4.cs.princeton.edu/33balanced.

// I have spent a lot of hours trying all possible ways to
// implement this data structure. Most of the attemps
// led to confusing compilation errors. The heart of the
// issue is how to represent the Option<Box<Node>>.

// I tried using the newtype pattern
// https://doc.rust-lang.org/book/structs.html#tuple-structs.
// I (and others) had difficulty writing the
// destructuring lets correctly. See
// https://www.reddit.com/r/rust/comments/2cmjfn/how_to_do_typedefsnewtypes

// I tried creating a struct with a single field
// but had trouble accessing the field correctly
// ("let", "let ref", "let mut", "let ref mut").
// In addition the dummy field obfuscated the implementation.

// I tried using a type alias but then it's not
// possible to implement Display and Debug.

// Eventually I settled on using no abstraction for
// Option<Box<Node>>. The implementation became
// much easier to write.

// Also the implementation became much easier after I
// saw from rcatolino that some methods should be defined
// on a trait that wraps Option<Box<Node>>.

use std::cmp::Ordering;
use std::mem;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
enum Color {
    Red,
    Black,
}

#[derive(Default, Debug)]
pub struct RedBlackTree {
    root: Option<Box<Node>>,
}

#[derive(Debug)]
struct Node {
    key: i32,
    val: i32,
    color: Color,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl RedBlackTree {
    /// Makes a new empty RedBlackTree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut map = RedBlackTree::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, 1);
    /// ```
    pub fn new() -> RedBlackTree {
        Default::default()
    }

    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut map = RedBlackTree::new();
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
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut a = RedBlackTree::new();
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
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut map = RedBlackTree::new();
    /// assert_eq!(map.insert(37, 1), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, 2);
    /// assert_eq!(map.insert(37, 3), Some(2));
    /// ```
    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = self.root.insert(key, value);
        self.root.set_color(Color::Black);
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
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut map = RedBlackTree::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(1), Some(1));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: i32) -> Option<i32> {
        let prev = self.root.get(key);
        if prev.is_none() {
            return prev;
        }
        if !self.root.left().is_red() && !self.root.right().is_red() {
            self.root.set_color(Color::Red);
        }
        self.root.remove(key);
        if self.root.is_some() {
            self.root.set_color(Color::Black);
        }
        self.check();
        prev
    }

    /// Removes the minimum element from the map,
    /// returning the (key,value) pair of the minimum
    /// if the tree is not empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::llredblack::RedBlackTree;
    ///
    /// let mut map = RedBlackTree::new();
    /// map.insert(1, 1);
    /// assert_eq!(map.remove_min(), Some((1,1)));
    /// assert_eq!(map.remove_min(), None);
    /// ```
    pub fn remove_min(&mut self) -> Option<(i32, i32)> {
        if self.root.is_none() {
            None
        } else {
            if !self.root.left().is_red() && !self.root.right().is_red() {
                self.root.set_color(Color::Red);
            }
            let min = self.root.remove_min();
            if self.root.is_some() {
                self.root.set_color(Color::Black);
            }
            self.check();
            min
        }
    }

    /// Returns true if the tree satisfies the ordered
    // propery of a binary search tree.
    fn is_bst(&self) -> bool {
        self.root.is_bst(None, None)
    }

    /// Returns true if the tree is isomorphic to a 2-3 tree.
    fn is_23(&self) -> bool {
        self.root.is_23(true)
    }

    /// Returns true if he path from the root to the
    // farthest leaf is no more than twice as long as
    // the path from the root to the nearest leaf.
    fn is_balanced(&self) -> bool {
        let mut black = 0;
        let mut next = &self.root;
        loop {
            match *next {
                None => break,
                Some(ref node) => {
                    if !node.is_red() {
                        black += 1;
                    }
                    next = &node.left;
                }
            }
        }
        self.root.is_balanced(black)
    }

    /// Applies all the invariant tests on the
    /// binary search tree. Tests are only
    // applied in the debug! context.
    fn check(&self) {
        debug_assert!(self.is_bst(), "Not a binary search tree");
        debug_assert!(self.is_23(), "Not a 2-3 tree");
        debug_assert!(self.is_balanced(), "Not balanced");
    }
}

impl Node {
    fn leaf(key: i32, val: i32) -> Node {
        Node {
            key: key,
            val: val,
            color: Color::Red,
            left: None,
            right: None,
        }
    }

    fn is_red(&self) -> bool {
        self.color == Color::Red
    }

    fn left_rotate(&mut self) {
        debug_assert!(self.right.is_red());
        let mut child = self.right.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.right, &mut self.left);
        self.color = child.color;
        child.color = Color::Red;
        self.left = Some(child);
    }

    fn right_rotate(&mut self) {
        debug_assert!(self.left.is_red());
        let mut child = self.left.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.left, &mut self.right);
        self.color = child.color;
        child.color = Color::Red;
        self.right = Some(child);
    }

    fn flip_colors(&mut self) {
        debug_assert!(self.left.is_some());
        debug_assert!(self.right.is_some());
        debug_assert!(self.color != self.left.color());
        debug_assert!(self.color != self.right.color());
        self.color.flip();
        self.left.mutate().color.flip();
        self.right.mutate().color.flip();
    }

    // Assuming that self is red and both self.left and self.left.left
    // are black, make self.left or one of its children red.
    fn move_red_to_left(&mut self) {
        debug_assert!(self.is_red());
        debug_assert!(!self.left.is_red());
        debug_assert!(!self.left.left().is_red());
        self.flip_colors();
        if self.right.left().is_red() {
            self.right.mutate().right_rotate();
            self.left_rotate();
            self.flip_colors();
        }
    }

    // Assuming that self is red and both self.right and self.right.left
    // are black, make self.right or one of its children red.
    fn move_red_to_right(&mut self) {
        debug_assert!(self.is_red());
        debug_assert!(!self.right.is_red());
        debug_assert!(!self.right.left().is_red());
        self.flip_colors();
        if self.left.left().is_red() {
            self.right_rotate();
            self.flip_colors();
        }
    }

    fn remove(&mut self, key: i32) -> bool {
        if key.cmp(&self.key) == Ordering::Less {
            if !self.left.is_red() && !self.left.left().is_red() {
                self.move_red_to_left();
            }
            self.left.remove(key);
        } else {
            if self.left.is_red() {
                self.right_rotate();
            }
            if key.cmp(&self.key) == Ordering::Equal && self.right.is_none() {
                return true;
            }
            if !self.right.is_red() && !self.right.left().is_red() {
                self.move_red_to_right();
            }
            if key.cmp(&self.key) == Ordering::Equal {
                let min = self.right.remove_min().unwrap();
                self.key = min.0;
                self.val = min.1;
            } else {
                self.right.remove(key);
            }
        }
        self.post_remove_balance();
        false
    }

    fn post_insert_balance(&mut self) {
        if !self.left.is_red() && self.right.is_red() {
            self.left_rotate();
        }
        if self.left.is_red() && self.left.left().is_red() {
            self.right_rotate();
        }
        if self.left.is_red() && self.right.is_red() {
            self.flip_colors();
        }
    }

    fn post_remove_balance(&mut self) {
        if self.right.is_red() {
            self.left_rotate();
        }
        if self.left.is_red() && self.left.left().is_red() {
            self.right_rotate();
        }
        if self.left.is_red() && self.right.is_red() {
            self.flip_colors();
        }
    }
}

trait OptionBoxNode {
    fn get(&self, key: i32) -> Option<i32>;
    fn is_red(&self) -> bool;
    fn color(&self) -> Color;
    fn insert(&mut self, key: i32, val: i32) -> Option<i32>;
    fn reference(&self) -> &Box<Node>;
    fn mutate(&mut self) -> &mut Box<Node>;
    fn left(&self) -> &Option<Box<Node>>;
    fn right(&self) -> &Option<Box<Node>>;
    fn set_color(&mut self, color: Color);
    fn remove_min(&mut self) -> Option<(i32, i32)>;
    fn remove(&mut self, key: i32);
    fn is_bst(&self, min: Option<i32>, max: Option<i32>) -> bool;
    fn is_23(&self, root: bool) -> bool;
    fn is_balanced(&self, black: i32) -> bool;
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

    fn is_red(&self) -> bool {
        match *self {
            None => false,
            Some(ref node) => node.is_red(),
        }
    }

    fn color(&self) -> Color {
        self.as_ref().unwrap().color
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
        self.mutate().post_insert_balance();
        prev
    }

    fn remove_min(&mut self) -> Option<(i32, i32)> {
        if self.is_none() {
            None
        } else if self.reference().left.is_none() {
            let min = self.take().unwrap();
            Some((min.key, min.val))
        } else {
            let node = self.mutate();
            if !node.left.is_red() && !node.left.left().is_red() {
                node.move_red_to_left();
            }
            let min = node.left.remove_min();
            node.post_remove_balance();
            min
        }
    }

    fn remove(&mut self, key: i32) {
        if self.is_none() {
            panic!("Attempt to remove on empty node")
        }
        let del = self.mutate().remove(key);
        if del {
            self.take();
        }
    }

    fn reference(&self) -> &Box<Node> {
        self.as_ref().unwrap()
    }

    fn mutate(&mut self) -> &mut Box<Node> {
        self.as_mut().unwrap()
    }

    fn left(&self) -> &Option<Box<Node>> {
        &self.as_ref().unwrap().left
    }

    fn right(&self) -> &Option<Box<Node>> {
        &self.as_ref().unwrap().right
    }

    fn set_color(&mut self, color: Color) {
        self.as_mut().unwrap().color = color;
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

    fn is_23(&self, root: bool) -> bool {
        match *self {
            None => true,
            Some(ref node) => {
                if node.right.is_red() {
                    return false;
                }
                if !root && node.is_red() && node.left.is_red() {
                    return false;
                }
                node.left.is_23(false) && node.right.is_23(false)
            }
        }
    }

    fn is_balanced(&self, mut black: i32) -> bool {
        match *self {
            None => black == 0,
            Some(ref node) => {
                if !node.is_red() {
                    black -= 1;
                }
                node.left.is_balanced(black) && node.right.is_balanced(black)
            }
        }
    }
}

impl Color {
    fn flip(&mut self) {
        match *self {
            Color::Red => *self = Color::Black,
            Color::Black => *self = Color::Red,
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
        let mut tree = RedBlackTree::new();
        assert_eq!(tree.get(0), None);
        assert_eq!(tree.insert(0, 1), None);
        assert_eq!(tree.insert(0, 2), Some(1));
        assert_eq!(tree.get(0), Some(2));
    }

    #[test]
    fn insert_sequence() {
        let mut tree = RedBlackTree::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.get(i), Some(i));
        }
    }

    #[test]
    fn remove_min() {
        let mut tree = RedBlackTree::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove_min(), Some((i, i)));
        }
        assert_eq!(tree.remove_min(), None);
    }

    #[test]
    fn remove() {
        let mut tree = RedBlackTree::new();
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove(i), Some(i));
            assert_eq!(tree.remove(i), None);
        }
    }
}
