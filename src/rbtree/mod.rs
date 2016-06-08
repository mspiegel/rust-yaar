use std::cmp::Ordering;
use std::mem;

#[derive(PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

type Link = Box<Node>;
type LinkOrEmpty = Option<Link>;

pub struct RBTree {
    root: LinkOrEmpty,
}

struct Node {
    key: i32,
    val: i32,
    color: Color,
    left: LinkOrEmpty,
    right: LinkOrEmpty,
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
        self.root.as_mut().unwrap().color = Color::Black;
        prev
    }

}

fn new_leaf(key: i32, val: i32) -> LinkOrEmpty {
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

trait BoxNode {
    fn left_rotate(&mut self) -> ();
}

impl BoxNode for Link {

    fn left_rotate(&mut self) -> () {
        let mut y = self.right.take().unwrap();
        mem::swap(&mut self.right, &mut y.left);
        mem::swap(self, &mut y.left.take().unwrap());
    }
}

trait PtrNode {
    fn get(&self, key: i32) -> Option<i32>;
    fn insert(&mut self, key: i32, val: i32) -> Option<i32>;
}

impl PtrNode for LinkOrEmpty {

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

    fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        match *self {
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
