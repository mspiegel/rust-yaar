//! A naive implementation of left-leaning red-black trees
//! that are isomorphic to 2-3 trees. This implementation
//! borrows heavily from https://www.cs.princeton.edu/~rs/talks/LLRB/LLRB.pdf
//! and https://github.com/rcatolino/rbtree-rust.

use std::cmp::Ordering;
use std::mem;

#[derive(PartialEq, Eq, Copy, Clone)]
enum Color {
    Red,
    Black,
}

pub struct RBTree {
    root: Option<Box<Node>>,
}

struct Node {
    key: i32,
    val: i32,
    color: Color,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Color {
    fn flip(self) -> Color {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red
        }
    }
}

impl RBTree {

    pub fn new() -> Self {
        RBTree { root: None }
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        self.root.get(key)
    }

    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = self.root.insert(key, value);
        self.root.mutate().color = Color::Black;
        prev
    }

    #[allow(dead_code)]
    fn to_string(&self) -> String {
        to_string(&self.root)
    }

}

fn new_leaf(key: i32, val: i32) -> Option<Box<Node>> {
    Some(Box::new(Node::new(key, val)))
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

trait Link {
    fn left_rotate(&mut self);
    fn right_rotate(&mut self);
    fn flip_colors(&mut self);
}

impl Link for Box<Node> {

    fn left_rotate(&mut self) {
        let mut child = self.right.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.right, &mut self.left);
        self.color = child.color;
        child.color = Color::Red;
        self.left = Some(child);
    }

    fn right_rotate(&mut self) {
        let mut child = self.left.take().unwrap();
        mem::swap(self, &mut child);
        mem::swap(&mut child.left, &mut self.right);
        self.color = child.color;
        child.color = Color::Red;
        self.right = Some(child);
    }

    fn flip_colors(&mut self) {
        self.color.flip();
        self.left.mutate().color.flip();
        self.right.mutate().color.flip();
    }
}

trait OptionLink {
    fn get(&self, key: i32) -> Option<i32>;
    fn is_red(&self) -> bool;
    fn insert(&mut self, key: i32, val: i32) -> Option<i32>;
    fn reference(&mut self) -> & Box<Node>;
    fn mutate(&mut self) -> &mut Box<Node>;
}

impl OptionLink for Option<Box<Node>> {

    fn get(&self, key: i32) -> Option<i32> {
        match *self {
            None => None,
            Some(ref node) => match key.cmp(&node.key) {
                Ordering::Equal => Some(node.val),
                Ordering::Less => node.left.get(key),
                Ordering::Greater => node.right.get(key)
            }
        }
    }

    fn is_red(&self) -> bool {
        match *self {
            None => false,
            Some(ref node) => (node.color == Color::Red)
        }
    }

    fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = match *self {
            None => {
                *self = new_leaf(key, value);
                None
            },
            Some(ref mut node) => {
                match key.cmp(&node.key) {
                    Ordering::Equal => {
                        let prev = node.val;
                        node.val = value;
                        Some(prev)
                    },
                    Ordering::Less => node.left.insert(key, value),
                    Ordering::Greater => node.right.insert(key, value),
                }
            }
        };
        let ref mut node = self.mutate();
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

    fn reference(&mut self) -> & Box<Node> {
        self.as_ref().unwrap()
    }

    fn mutate(&mut self) -> &mut Box<Node> {
        self.as_mut().unwrap()
    }

}

#[allow(dead_code)]
fn to_string(link: &Option<Box<Node>>) -> String {
    match *link {
        None => String::from("nil"),
        Some(ref node) => format!("{} ({}) ({})",
            node.key,
            to_string(&node.left),
            to_string(&node.right))
    }
}

#[test]
fn basic_construction() {
    let mut tree = RBTree::new();
    assert_eq!(tree.get(0), None);
    assert_eq!(tree.insert(0, 1), None);
    assert_eq!(tree.insert(0, 2), Some(1));
    assert_eq!(tree.get(0), Some(2));
 }
