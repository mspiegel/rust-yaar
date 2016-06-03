use std::cmp::Ordering;
use std::mem;

#[derive(PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

pub struct RBTree {
    root: Link,
}

struct Link(Option<Box<Node>>);

struct Node {
    key: i32,
    val: i32,
    color: Color,
    left: Link,
    right: Link,
}

impl RBTree {

    pub fn new() -> Self {
        RBTree { root: Link(None) }
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        self.root.get(key)
    }

    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let prev = self.root.insert(key, value);
        let Link(ref mut node) = self.root;
        node.as_mut().unwrap().color = Color::Black;
        prev
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
            left: Link(None),
            right: Link(None),
        }
    }
}

impl Link {

    fn is_red(&self) -> bool {
        let Link(ref node_option) = *self;
        match *node_option {
            None => false,
            Some(ref node) => node.color == Color::Red,
        }
    }

    fn get(&self, key: i32) -> Option<i32> {
        let Link(ref node_option) = *self;
        match *node_option {
            None => None,
            Some(ref node) => match key.cmp(&node.key) {
                Ordering::Equal => Some(node.val),
                Ordering::Less => node.left.get(key),
                Ordering::Greater => node.right.get(key),
            }
        }
    }

    fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        let Link(ref mut node_option) = *self;
        match *node_option {
            None => {
                *node_option = new_leaf(key, value);
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
        }
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
