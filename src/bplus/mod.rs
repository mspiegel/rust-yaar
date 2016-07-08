
use std::cmp;
use std::cmp::Ordering;
use std::mem;

#[derive(PartialEq, Eq, Copy, Clone)]
enum Neighbor {
    Less,
    Greater
}

struct Node {
    keys: Vec<i32>,
    vals: Option<Vec<i32>>,
    children: Option<Vec<Box<Node>>>
}

struct KeyNodePair(i32, Box<Node>);

pub struct BTree {
    root: Option<Box<Node>>,
    max: usize
}

impl BTree {
    /// Makes a new empty BTree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::btree::BTree;
    ///
    /// let mut map = BTree::new(16);
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, 1);
    /// ```
    pub fn new(max: usize) -> BTree {
        BTree{ root: None, max: max }
    }

    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::btree::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// map.insert(1, 1);
    /// assert_eq!(map.get(1), Some(1));
    /// assert_eq!(map.get(2), None);
    /// ```
    pub fn get(&self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(ref node) => node.get(key)
        }
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::btree::BTree;
    ///
    /// let mut a = BTree::new(16);
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
    /// use yaar::btree::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// assert_eq!(map.insert(37, 1), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, 2);
    /// assert_eq!(map.insert(37, 3), Some(2));
    /// ```
    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        match self.root {
            None => {
                self.root = Node::new_leaf(key, value);
                None
            },
            Some(_) => {
                let (prev, split) = self.root.as_mut().unwrap().insert(key, value, self.max);
                if split.is_some() {
                    let KeyNodePair(key, child) = split.unwrap();
                    let children = vec![self.root.take().unwrap(), child];
                    self.root = Node::new_root(key, children);
                }
                prev
            }
        }
    }

    pub fn remove(&mut self, key: i32) -> Option<i32> {
        let min = self.max / 2;
        if self.root.is_some() {
            let (prev, empty) = {
                let node = self.root.as_mut().unwrap();
                let (prev, _) = node.remove(key, min);
                match node.children {
                    None => (prev, node.keys.len() == 0),
                    Some(ref children) => (prev, children.len() == 1)
                }
            };
            if empty {
                let node = self.root.take().unwrap();
                if node.children.is_some() {
                    self.root = Some(node.children.unwrap().remove(0));
                }
            }
            prev
        } else {
            None
        }
    }
}

impl KeyNodePair {
    fn new(
        key: i32,
        keys: Vec<i32>,
        vals: Option<Vec<i32>>,
        children: Option<Vec<Box<Node>>>) -> KeyNodePair {
            KeyNodePair(key, Box::new(Node{keys:keys, vals:vals, children: children}))
    }
}

impl Node {

    fn new_leaf(key: i32, value: i32) -> Option<Box<Node>> {
        Some(Box::new(Node { keys: vec![key], vals: Some(vec![value]), children: None }))
    }

    fn new_root(key: i32, children: Vec<Box<Node>>) -> Option<Box<Node>> {
        Some(Box::new(Node { keys: vec![key], vals: None, children: Some(children) }))
    }

    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        if self.vals.is_none() {
            let index = Node::index(position);
            self.child(index).get(key)
        } else {
            match position {
                Ok(index) => Some(self.value(index)),
                Err(_) => None
            }
        }
    }

    fn split(&mut self, max: usize) -> Option<KeyNodePair> {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            match self.children {
                Some(ref mut children) => {
                    let mut newkeys = self.keys.split_off(partition);
                    let newchildren = children.split_off(partition + 1);
                    let newkey = newkeys.remove(0);
                    Some(KeyNodePair::new(newkey, newkeys, None, Some(newchildren)))
                },
                None => {
                    let newkeys = self.keys.split_off(partition);
                    let newvals = Some(self.mut_values().split_off(partition));
                    Some(KeyNodePair::new(newkeys[0], newkeys, newvals, None))
                }
            }
        } else {
            None
        }
    }

    fn insert(&mut self, key: i32, value: i32, max: usize) -> (Option<i32>, Option<KeyNodePair>) {
        let position = self.keys.binary_search(&key);
        let prev = match self.children {
            Some(ref mut children) => {
                let index = Node::index(position);
                let (prev, newchild) = children[index].insert(key, value, max);
                if newchild.is_some() {
                    let KeyNodePair(key, newchild) = newchild.unwrap();
                    let index = Node::index(self.keys.binary_search(&key));
                    self.keys.insert(index, key);
                    children.insert(index + 1, newchild);
                }
                prev
            },
            None => {
                let prev = match position {
                    Ok(index) => Some(self.value(index)),
                    Err(_) => None
                };
                match position {
                    Ok(index) => {
                        self.mut_values()[index] = value;
                    },
                    Err(index) => {
                        self.keys.insert(index, value);
                        self.mut_values().insert(index, value);
                    }
                };
                prev
            }
        };
        (prev, self.split(max))
    }

    fn needs_merge(&self, min: usize) -> bool {
        self.keys.len() < min
    }

    fn merge_select_sibling(&self, index: usize) -> Neighbor {
        let leftsize = if index > 0 {
            self.ref_children()[index - 1].keys.len()
        } else { 0 };
        let rightsize = if index < self.ref_children().len() - 1 {
            self.ref_children()[index + 1].keys.len()
        } else { 0 };
        if leftsize == 0 && rightsize == 0 {
            panic!("left and right children are empty");
        }
        match rightsize.cmp(&leftsize) {
            Ordering::Less | Ordering::Equal => Neighbor::Less,
            Ordering::Greater => Neighbor::Greater
        }
    }

    fn neighbor(index: usize, ord: Neighbor) -> usize {
        match ord {
            Neighbor::Less => {
                index - 1
            },
            Neighbor::Greater => {
                index + 1
            }
        }
    }

    fn partition(&mut self, index: usize, ord: Neighbor) -> (&mut Node, &mut Node) {
        match ord {
            Neighbor::Less => {
                let (left, right) = self.mut_children().split_at_mut(index);
                let index = left.len() - 1;
                (&mut right[0], &mut left[index])
            },
            Neighbor::Greater => {
                let (left, right) = self.mut_children().split_at_mut(index + 1);
                let index = left.len() - 1;
                (&mut left[index], &mut right[0])
            }
        }
    }

    fn get_parent_key(&self, index: usize, ord: Neighbor) -> i32 {
        match ord {
            Neighbor::Less => {
                self.keys[index - 1]
            },
            Neighbor::Greater => {
                self.keys[index]
            }
        }
    }

    fn set_parent_key(&mut self, key: Option<i32>, index: usize, ord: Neighbor) {
        match key {
            Some(value) => match ord {
                Neighbor::Less => {
                    self.keys[index - 1] = value;
                },
                Neighbor::Greater => {
                    self.keys[index] = value;
                }
            },
            None => {}
        }
    }

    fn pre_redistribute(sibling: &mut Vec<i32>, key: i32, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                sibling.push(key);
            },
            Neighbor::Greater => {
                sibling.insert(0, key);
            }
        }
    }

    fn redistribute<T>(src: &mut Vec<T>, dest: &mut Vec<T>, ord: Neighbor, count: usize) {
        match ord {
            Neighbor::Less => {
                let position = src.len() - count;
                let mut newdest = src.split_off(position);
                newdest.append(dest);
                *dest = newdest;
            },
            Neighbor::Greater => {
                let newsrc = src.split_off(count);
                dest.append(src);
                *src = newsrc;
            }
        }
    }

    fn post_redistribute(sibling: &mut Vec<i32>, ord: Neighbor) -> i32 {
        match ord {
            Neighbor::Less => {
                sibling.pop().unwrap()
            },
            Neighbor::Greater => {
                sibling.remove(0)
            }
        }
    }

    fn merge_redistribute(&mut self, index: usize, ord: Neighbor, min: usize) {
        let pkey = self.get_parent_key(index, ord);
        let ckey = {
            let (mut child, mut sibling) = self.partition(index, ord);
            let sibling_len = sibling.keys.len();
            let count = cmp::max(1, (sibling_len - min) / 2);
            if child.children.is_none() {
                Node::redistribute(&mut sibling.keys, &mut child.keys, ord, count);
                Node::redistribute(&mut sibling.mut_values(), &mut child.mut_values(), ord, count);
                None
            } else {
                Node::pre_redistribute(&mut sibling.keys, pkey, ord);
                Node::redistribute(&mut sibling.keys, &mut child.keys, ord, count);
                Node::redistribute(&mut sibling.mut_children(), &mut child.mut_children(), ord, count);
                Some(Node::post_redistribute(&mut sibling.keys, ord))
            }
        };
        self.set_parent_key(ckey, index, ord);
    }

    fn collapse<T>(sibling: &mut Vec<T>, child: &mut Vec<T>, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                sibling.append(child);
            },
            Neighbor::Greater => {
                child.append(sibling);
                mem::swap(child, sibling);
            }
        }
    }

    fn merge_collapse(&mut self, index: usize, ord: Neighbor) {
        {
            let (mut child, mut sibling) = self.partition(index, ord);
            if child.children.is_some() {
                debug_assert_eq!(child.keys.len() + 1, child.ref_children().len());
            } else {
                debug_assert_eq!(child.keys.len(), child.ref_values().len());
            }
            Node::collapse(&mut sibling.keys, &mut child.keys, ord);
            if child.children.is_some() {
                Node::collapse(&mut sibling.mut_children(), &mut child.mut_children(), ord);
            } else {
                Node::collapse(&mut sibling.mut_values(), &mut child.mut_values(), ord);
            }
        }
        self.mut_children().remove(index);
        match ord {
            Neighbor::Less => {
                self.keys.remove(index - 1);
            },
            Neighbor::Greater => {
                self.keys.remove(index);
            }
        }
    }

    fn merge_child(&mut self, index: usize, min: usize) {
        let ord = self.merge_select_sibling(index);
        let sib_index = Node::neighbor(index, ord);
        let sib_len = self.ref_children()[sib_index].keys.len();
        if sib_len > min {
            self.merge_redistribute(index, ord, min);
        } else {
            //self.merge_collapse(index, ord);
        }
    }

    fn remove(&mut self, key: i32, min: usize) -> (Option<i32>, bool) {
        let position = self.keys.binary_search(&key);
        let (prev, child_merge) = match self.children {
            Some(ref mut children) => {
                let index = Node::index(position);
                children[index].remove(key, min)
            },
            None => {
                match position {
                    Ok(index) => {
                        self.keys.remove(index);
                        (Some(self.mut_values().remove(index)), false)
                    }
                    Err(_) => (None, false)
                }
            }
        };
        if child_merge {
            self.merge_child(Node::index(position), min);
        }
        (prev, self.needs_merge(min))
    }

    fn index(position: Result<usize,usize>) -> usize {
        match position {
            Ok(index) => index + 1,
            Err(index) => index,
        }
    }

    fn ref_values(&self) -> &Vec<i32> {
        self.vals.as_ref().unwrap()
    }

    fn mut_values(&mut self) -> &mut Vec<i32> {
        self.vals.as_mut().unwrap()
    }

    fn ref_children(&self) -> &Vec<Box<Node>> {
        self.children.as_ref().unwrap()
    }

    fn mut_children(&mut self) -> &mut Vec<Box<Node>> {
        self.children.as_mut().unwrap()
    }

    fn value(&self, index: usize) -> i32 {
        *self.ref_values().get(index).unwrap()
    }

    fn child(&self, index: usize) -> &Box<Node> {
        self.ref_children().get(index).unwrap()
    }
}

#[test]
fn redistribute() {
    let mut vec1 = vec![1, 2, 3];
    let mut vec2 = vec![4, 5, 6];
    Node::redistribute(&mut vec1, &mut vec2, Neighbor::Less, 2);
    assert_eq!(vec1, vec![1]);
    assert_eq!(vec2, vec![2, 3, 4, 5, 6]);

    let mut vec3 = vec![1, 2, 3];
    let mut vec4 = vec![4, 5, 6];
    Node::redistribute(&mut vec4, &mut vec3, Neighbor::Greater, 2);
    assert_eq!(vec3, vec![1, 2, 3, 4, 5]);
    assert_eq!(vec4, vec![6]);
}

fn testnode() -> Box<Node> {
    Node::new_leaf(0,0).unwrap()
}

#[test]
fn redistribute_children_left() {
    let left = Box::new(Node{keys: vec![1, 2, 3, 4, 5, 6], vals: None,
        children: Some(vec![testnode(), testnode()])});
    let right = Box::new(Node{keys: vec![70], vals: None,
        children: Some(vec![testnode(), testnode(), testnode(),
        testnode(), testnode(), testnode(), testnode()])});
    let mut parent = Node{keys: vec![50], vals: None, children: Some(vec!(left, right))};
    parent.merge_redistribute(1, Neighbor::Less, 2);
    assert_eq!(parent.keys, vec![5]);
    assert_eq!(parent.ref_children()[0].keys, vec![1, 2, 3, 4]);
    assert_eq!(parent.ref_children()[1].keys, vec![6, 50, 70]);
}

#[test]
fn redistribute_children_right() {
    let left = Box::new(Node{keys: vec![15], vals: None,
        children: Some(vec![testnode(), testnode()])});
    let right = Box::new(Node{keys: vec![20, 30, 40, 50, 60, 70], vals: None,
        children: Some(vec![testnode(), testnode(), testnode(),
        testnode(), testnode(), testnode(), testnode()])});
    let mut parent = Node{keys: vec![18], vals: None, children: Some(vec!(left, right))};
    parent.merge_redistribute(0, Neighbor::Greater, 2);
    assert_eq!(parent.keys, vec![30]);
    assert_eq!(parent.ref_children()[0].keys, vec![15, 18, 20]);
    assert_eq!(parent.ref_children()[1].keys, vec![40, 50, 60, 70]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_construction() {
        let mut tree = BTree::new(4);
        assert_eq!(tree.get(0), None);
        assert_eq!(tree.insert(0, 1), None);
        assert_eq!(tree.insert(0, 2), Some(1));
        assert_eq!(tree.get(0), Some(2));
    }

    #[test]
    fn insert_sequence() {
        let mut tree = BTree::new(4);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
            assert_eq!(tree.get(i), Some(i));
        }
    }

/*
    #[test]
    fn remove() {
        let mut tree = BTree::new(4);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove(i), Some(i));
            assert_eq!(tree.remove(i), None);
        }
    }
*/

}
