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
// on a trait that wraps Box<Node> and other method
// should be defined on a trait that wraps Option<Box<Node>>.

use std::cmp::Ordering;
use std::fmt;
use std::mem;

#[derive(PartialEq, Eq, Copy, Clone)]
enum Color {
    Red,
    Black,
}

// This instance of the newtype pattern
// https://doc.rust-lang.org/book/structs.html#tuple-structs
// is used only for fmt::Display and fmt::Debug.
struct Link<'a>(&'a Option<Box<Node>>);

pub struct LLRBTree {
    root: Option<Box<Node>>,
}

struct Node {
    key: i32,
    val: i32,
    color: Color,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl LLRBTree {
    pub fn new() -> Self {
        LLRBTree { root: None }
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        self.root.get(key)
    }

    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = self.root.insert(key, value);
        self.root.mutate().color = Color::Black;
        debug_assert!(self.check());
        prev
    }

    fn is_bst(&self) -> bool {
        self.root.is_bst(None, None)
    }

    fn is_23(&self) -> bool {
        self.root.is_23(true)
    }

    fn is_balanced(&self) -> bool {
        let mut black = 0;
        let mut next = &self.root;
        loop {
            match next {
                &None => break,
                &Some(ref node) => {
                    if !node.is_red() {
                        black += 1;
                    }
                    next = &node.left;
                }
            }
        }
        self.root.is_balanced(black)
    }

    fn check(&self) -> bool {
        debug_assert!(self.is_bst(), "Not a binary search tree");
        debug_assert!(self.is_23(), "Not a 2-3 tree");
        debug_assert!(self.is_balanced(), "Not balanced");
        true
    }
}

impl fmt::Display for LLRBTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", Link(&self.root))
    }
}

impl fmt::Debug for LLRBTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", Link(&self.root))
    }
}

impl Node {
    fn new(key: i32, val: i32) -> Self {
        Node {
            key: key,
            val: val,
            color: Color::Red,
            left: None,
            right: None,
        }
    }
}

trait BoxNode {
    fn is_red(&self) -> bool;
    fn left_rotate(&mut self);
    fn right_rotate(&mut self);
    fn flip_colors(&mut self);
}

impl BoxNode for Box<Node> {
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
}

trait OptionBoxNode {
    fn get(&self, key: i32) -> Option<i32>;
    fn is_red(&self) -> bool;
    fn color(&self) -> Color;
    fn insert(&mut self, key: i32, val: i32) -> Option<i32>;
    fn reference(&mut self) -> &Box<Node>;
    fn mutate(&mut self) -> &mut Box<Node>;
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
        let node = self.mutate();
        if !node.left.is_red() && node.right.is_red() {
            node.left_rotate();
        }
        if node.left.is_red() && node.left.reference().left.is_red() {
            node.right_rotate();
        }
        if node.left.is_red() && node.right.is_red() {
            node.flip_colors();
        }
        prev
    }

    fn reference(&mut self) -> &Box<Node> {
        self.as_ref().unwrap()
    }

    fn mutate(&mut self) -> &mut Box<Node> {
        self.as_mut().unwrap()
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

impl<'a> fmt::Display for Link<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Link(ref link) = *self;
        match *link {
            &None => write!(f, "nil"),
            &Some(ref node) => {
                write!(f,
                       "({} {} {})",
                       node.key,
                       Link(&node.left),
                       Link(&node.right))
            }
        }
    }
}

impl<'a> fmt::Debug for Link<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Link(ref link) = *self;
        match *link {
            &None => write!(f, "nil"),
            &Some(ref node) => {
                write!(f,
                       "({},{},{} {:?} {:?})",
                       node.key,
                       node.val,
                       node.color,
                       Link(&node.left),
                       Link(&node.right))
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

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Color::Red => write!(f, "red"),
            Color::Black => write!(f, "black"),
        }
    }
}

fn new_leaf(key: i32, val: i32) -> Option<Box<Node>> {
    Some(Box::new(Node::new(key, val)))
}

#[test]
fn basic_construction() {
    let mut tree = LLRBTree::new();
    assert_eq!(tree.get(0), None);
    assert_eq!(tree.insert(0, 1), None);
    assert_eq!(tree.insert(0, 2), Some(1));
    assert_eq!(tree.get(0), Some(2));
}

#[test]
fn insert_sequence() {
    let mut tree = LLRBTree::new();
    for i in 0..256 {
        assert_eq!(tree.insert(i, i), None);
    }
    for i in 0..256 {
        assert_eq!(tree.get(i), Some(i));
    }
}
