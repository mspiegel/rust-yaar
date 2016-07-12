use std::cmp;
use std::cmp::Ordering;
use std::fmt;
use std::mem;

#[derive(Debug)]
struct LeafNode {
    keys: Vec<i32>,
    vals: Vec<i32>,
}

#[derive(Debug)]
struct InternalNode {
    keys: Vec<i32>,
    children: Vec<Box<Node>>,
}

enum NodeWrap<'a> {
    Leaf(&'a mut LeafNode),
    Internal(&'a mut InternalNode)
}

#[derive(Debug)]
pub struct BTree {
    root: Option<Box<Node>>,
    max: usize,
    min: usize,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
enum Neighbor {
    Less,
    Greater,
}

struct KeyNodePair(i32, Box<Node>);

impl BTree {
    /// Makes a new empty BTree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::bplus::BTree;
    ///
    /// let mut map = BTree::new(16);
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, 1);
    /// ```
    pub fn new(max: usize) -> BTree {
        BTree {
            root: None,
            max: max,
            min: max / 2,
        }
    }

    /// Returns the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::bplus::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// map.insert(1, 1);
    /// assert_eq!(map.get(1), Some(1));
    /// assert_eq!(map.get(2), None);
    /// ```
    pub fn get(&self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(ref node) => node.get(key),
        }
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::bplus::BTree;
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
    /// use yaar::bplus::BTree;
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
                self.root = LeafNode::new_leaf(key, value);
                None
            }
            Some(_) => {
                let (prev, split) = self.root.as_mut().unwrap().insert(key, value, self.max);
                if split.is_some() {
                    let KeyNodePair(key, child) = split.unwrap();
                    let children = vec![self.root.take().unwrap(), child];
                    self.root = InternalNode::new_root(key, children);
                }
                prev
            }
        }
    }

    pub fn remove(&mut self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(_) => {
                let (prev, shrink) = {
                    let node = self.root.as_mut().unwrap();
                    let (prev, _) = node.remove(key, self.min);
                    (prev, node.keys().is_empty())
                };
                if shrink {
                    let mut node = self.root.take().unwrap();
                    self.root = node.shrink();
                }
                prev
            }
        }
    }

}

trait Node : fmt::Debug {

    fn keys(&self) -> &[i32];
    fn wrap(&mut self) -> NodeWrap;
    fn shrink(&mut self) -> Option<Box<Node>>;

    fn get(&self, key: i32) -> Option<i32>;
    fn split(&mut self, max: usize) -> Option<KeyNodePair>;
    fn insert(&mut self, key: i32, value: i32, max: usize) -> (Option<i32>, Option<KeyNodePair>);
    fn remove(&mut self, key: i32, min: usize) -> (Option<i32>, bool);

    fn child_redistribute(&mut self, sibling: NodeWrap, pkey: i32, ord: Neighbor, min: usize) -> i32;
    fn child_collapse(&mut self, sibling: NodeWrap, pkey:i32, ord: Neighbor);

    fn needs_merge(&self, min: usize) -> bool {
        self.keys().len() < min
    }
}

impl Node for LeafNode {

    fn keys(&self) -> &[i32]{
        return &self.keys;
    }

    fn wrap(&mut self) -> NodeWrap {
        NodeWrap::Leaf(self)
    }

    fn shrink(&mut self) -> Option<Box<Node>> {
        None
    }

    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        match position {
            Ok(index) => Some(self.vals[index]),
            Err(_) => None,
        }
    }

    fn insert(&mut self, key: i32, value: i32, max: usize) -> (Option<i32>, Option<KeyNodePair>) {
        let position = self.keys.binary_search(&key);
        let prev = match position {
            Ok(index) => Some(self.vals[index]),
            Err(_) => None,
        };
        match position {
            Ok(index) => {
                self.vals[index] = value;
            }
            Err(index) => {
                self.keys.insert(index, value);
                self.vals.insert(index, value);
            }
        };
        (prev, self.split(max))
    }

    fn remove(&mut self, key: i32, min: usize) -> (Option<i32>, bool) {
        let position = self.keys.binary_search(&key);
        let prev = match position {
            Ok(index) => {
                self.keys.remove(index);
                Some(self.vals.remove(index))
            },
            Err(_) => None
        };
        (prev, self.needs_merge(min))
    }

    fn split(&mut self, max: usize) -> Option<KeyNodePair> {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            let newkeys = self.keys.split_off(partition);
            let newvals = self.vals.split_off(partition);
            Some(KeyNodePair(newkeys[0], Box::new(LeafNode{keys: newkeys, vals: newvals})))
        } else {
            None
        }
    }

    #[allow(unused_variables)]
    fn child_redistribute(&mut self, sibling: NodeWrap, pkey: i32, ord: Neighbor, min: usize) -> i32 {
        match sibling {
            NodeWrap::Internal(_) => panic!("child and sibling are not on same level"),
            NodeWrap::Leaf(sibling) => {
                let sibling_len = sibling.keys.len();
                let count = cmp::max(1, (sibling_len - min) / 2);
                Node::redistribute(&mut sibling.keys, &mut self.keys, ord, count);
                Node::redistribute(&mut sibling.vals, &mut self.vals, ord, count);
                LeafNode::post_redistribute_get(&sibling.keys, ord)
            }
        }
    }

    #[allow(unused_variables)]
    fn child_collapse(&mut self, sibling: NodeWrap, pkey: i32, ord: Neighbor) {
        match sibling {
            NodeWrap::Internal(_) => panic!("child and sibling are not on same level"),
            NodeWrap::Leaf(sibling) => {
                Node::collapse(&mut sibling.keys, &mut self.keys, ord);
                Node::collapse(&mut sibling.vals, &mut self.vals, ord);
            }
        }
    }

}

impl Node for InternalNode {

    fn keys(&self) -> &[i32] {
        return &self.keys;
    }

    fn wrap(&mut self) -> NodeWrap {
        NodeWrap::Internal(self)
    }

    fn shrink(&mut self) -> Option<Box<Node>> {
        Some(self.children.remove(0))
    }

    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        let index = InternalNode::index(position);
        self.children[index].get(key)
    }

    fn insert(&mut self, key: i32, value: i32, max: usize) -> (Option<i32>, Option<KeyNodePair>) {
        let position = self.keys.binary_search(&key);
        let prev = {
            let index = InternalNode::index(position);
            let (prev, newchild) = self.children[index].insert(key, value, max);
            if newchild.is_some() {
                let KeyNodePair(key, newchild) = newchild.unwrap();
                let index = InternalNode::index(self.keys.binary_search(&key));
                self.keys.insert(index, key);
                self.children.insert(index + 1, newchild);
            }
            prev
        };
        (prev, self.split(max))
    }

    fn remove(&mut self, key: i32, min: usize) -> (Option<i32>, bool) {
        let position = self.keys.binary_search(&key);
        let index = InternalNode::index(position);
        let (prev, child_merge) = self.children[index].remove(key, min);
        if child_merge {
            self.merge_child(InternalNode::index(position), min);
        }
        (prev, self.needs_merge(min))
    }

    fn split(&mut self, max: usize) -> Option<KeyNodePair> {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            let mut newkeys = self.keys.split_off(partition);
            let newchildren = self.children.split_off(partition + 1);
            let newkey = newkeys.remove(0);
            Some(KeyNodePair(newkey, Box::new(InternalNode{keys: newkeys, children: newchildren})))
        } else {
            None
        }
    }

    fn child_redistribute(&mut self, sibling: NodeWrap, pkey: i32, ord: Neighbor, min: usize) -> i32 {
        match sibling {
            NodeWrap::Leaf(_) => panic!("child and sibling are not on same level"),
            NodeWrap::Internal(sibling) => {
                let sibling_len = sibling.keys.len();
                let count = cmp::max(1, (sibling_len - min) / 2);
                InternalNode::pre_redistribute(&mut sibling.keys, pkey, ord);
                Node::redistribute(&mut sibling.keys, &mut self.keys, ord, count);
                Node::redistribute(&mut sibling.children, &mut self.children, ord, count);
                InternalNode::post_redistribute_take(&mut sibling.keys, ord)
            }
        }
    }

    fn child_collapse(&mut self, sibling: NodeWrap, pkey: i32, ord: Neighbor) {
        match sibling {
            NodeWrap::Leaf(_) => panic!("child and sibling are not on same level"),
            NodeWrap::Internal(sibling) => {
                Node::collapse_with_middle(&mut sibling.keys, &mut self.keys, pkey, ord);
                Node::collapse(&mut sibling.children, &mut self.children, ord);
            }
        }
    }

}

impl LeafNode {

    fn new_leaf(key: i32, value: i32) -> Option<Box<Node>> {
        Some(Box::new(LeafNode {
            keys: vec![key],
            vals: vec![value],
        }))
    }

    fn post_redistribute_get(sibling: &[i32], ord: Neighbor) -> i32 {
        match ord {
            Neighbor::Less => {
                let len = sibling.len();
                sibling[len - 1]
            }
            Neighbor::Greater => sibling[0],
        }
    }

}

impl InternalNode {

    fn new_root(key: i32, children: Vec<Box<Node>>) -> Option<Box<Node>> {
        Some(Box::new(InternalNode {
            keys: vec![key],
            children: children,
        }))
    }

    fn index(position: Result<usize, usize>) -> usize {
        match position {
            Ok(index) => index + 1,
            Err(index) => index,
        }
    }

    fn neighbor(index: usize, ord: Neighbor) -> usize {
        match ord {
            Neighbor::Less => index - 1,
            Neighbor::Greater => index + 1,
        }
    }

    fn merge_select_sibling(&self, index: usize) -> Neighbor {
        let leftsize = if index > 0 {
            self.children[index - 1].keys().len()
        } else {
            0
        };
        let rightsize = if index < self.children.len() - 1 {
            self.children[index + 1].keys().len()
        } else {
            0
        };
        if leftsize == 0 && rightsize == 0 {
            panic!("left and right children are empty");
        }
        match rightsize.cmp(&leftsize) {
            Ordering::Less | Ordering::Equal => Neighbor::Less,
            Ordering::Greater => Neighbor::Greater,
        }
    }

    fn merge_child(&mut self, index: usize, min: usize) {
        let ord = self.merge_select_sibling(index);
        let sib_index = InternalNode::neighbor(index, ord);
        let sib_len = self.children[sib_index].keys().len();
        if sib_len > min {
            self.merge_redistribute(index, ord, min);
        } else {
            self.merge_collapse(index, ord);
        }
    }

    fn merge_redistribute(&mut self, index: usize, ord: Neighbor, min: usize) {
        let pkey = self.get_parent_key(index, ord);
        let ckey = {
            let (mut child, sibling) = self.partition(index, ord);
            child.child_redistribute(sibling, pkey, ord, min)
        };
        self.set_parent_key(ckey, index, ord);
    }

    fn merge_collapse(&mut self, index: usize, ord: Neighbor) {
        let pkey = self.get_parent_key(index, ord);
        {
            let (mut child, sibling) = self.partition(index, ord);
            child.child_collapse(sibling, pkey, ord);
        }
        self.drop_parent_key(index, ord);
        self.children.remove(index);
    }

    fn get_parent_key(&self, index: usize, ord: Neighbor) -> i32 {
        match ord {
            Neighbor::Less => self.keys[index - 1],
            Neighbor::Greater => self.keys[index],
        }
    }

    fn set_parent_key(&mut self, key: i32, index: usize, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                self.keys[index - 1] = key;
            }
            Neighbor::Greater => {
                self.keys[index] = key;
            }
        }
    }

    fn drop_parent_key(&mut self, index: usize, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                self.keys.remove(index - 1);
            }
            Neighbor::Greater => {
                self.keys.remove(index);
            }
        }
    }

    fn partition(&mut self, index: usize, ord: Neighbor) -> (&mut Box<Node>, NodeWrap) {
        match ord {
            Neighbor::Less => {
                let (left, right) = self.children.split_at_mut(index);
                let index = left.len() - 1;
                (&mut right[0], left[index].wrap())
            }
            Neighbor::Greater => {
                let (left, right) = self.children.split_at_mut(index + 1);
                let index = left.len() - 1;
                (&mut left[index], right[0].wrap())
            }
        }
    }

    fn pre_redistribute(sibling: &mut Vec<i32>, key: i32, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                sibling.push(key);
            }
            Neighbor::Greater => {
                sibling.insert(0, key);
            }
        }
    }

    fn post_redistribute_take(sibling: &mut Vec<i32>, ord: Neighbor) -> i32 {
        match ord {
            Neighbor::Less => sibling.pop().unwrap(),
            Neighbor::Greater => sibling.remove(0),
        }
    }
}

impl Node {

    fn redistribute<T>(src: &mut Vec<T>, dest: &mut Vec<T>, ord: Neighbor, count: usize) {
        match ord {
            Neighbor::Less => {
                let position = src.len() - count;
                let mut newdest = src.split_off(position);
                newdest.append(dest);
                *dest = newdest;
            }
            Neighbor::Greater => {
                let newsrc = src.split_off(count);
                dest.append(src);
                *src = newsrc;
            }
        }
    }

    fn collapse<T>(sibling: &mut Vec<T>, child: &mut Vec<T>, ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                sibling.append(child);
            }
            Neighbor::Greater => {
                child.append(sibling);
                mem::swap(child, sibling);
            }
        }
    }

    fn collapse_with_middle<T>(sibling: &mut Vec<T>,
                               child: &mut Vec<T>,
                               middle: T,
                               ord: Neighbor) {
        match ord {
            Neighbor::Less => {
                sibling.push(middle);
                sibling.append(child);
            }
            Neighbor::Greater => {
                child.push(middle);
                child.append(sibling);
                mem::swap(child, sibling);
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Node;
    use super::InternalNode;
    use super::LeafNode;
    use super::Neighbor;

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
        LeafNode::new_leaf(0, 0).unwrap()
    }

    #[test]
    fn redistribute_children_left() {
        let left = Box::new(InternalNode {
            keys: vec![1, 2, 3, 4, 5, 6],
            children: vec![testnode(), testnode(), testnode(), testnode(), testnode(),
                                testnode(), testnode()],
        });
        let right = Box::new(InternalNode{
            keys: vec![70],
            children: vec![testnode(), testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right],
        };
        parent.merge_redistribute(1, Neighbor::Less, 2);
        assert_eq!(parent.keys(), [5]);
        assert_eq!(parent.children[0].keys(), [1, 2, 3, 4]);
        assert_eq!(parent.children[1].keys(), [6, 50, 70]);
    }

    #[test]
    fn redistribute_children_right() {
        let left = Box::new(InternalNode {
            keys: vec![15],
            children: vec![testnode(), testnode()],
        });
        let right = Box::new(InternalNode {
            keys: vec![20, 30, 40, 50, 60, 70],
            children: vec![testnode(), testnode(), testnode(), testnode(), testnode(),
                testnode(), testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![18],
            children: vec![left, right],
        };
        parent.merge_redistribute(0, Neighbor::Greater, 2);
        assert_eq!(parent.keys(), [30]);
        assert_eq!(parent.children[0].keys(), [15, 18, 20]);
        assert_eq!(parent.children[1].keys(), [40, 50, 60, 70]);
    }

    #[test]
    fn collapse_children_left() {
        let left = Box::new(InternalNode {
            keys: vec![1, 2, 3],
            children: vec![testnode(), testnode(), testnode(), testnode()]
        });
        let right = Box::new(InternalNode {
            keys: vec![70],
            children: vec![testnode(), testnode()]
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right]
        };
        parent.merge_collapse(1, Neighbor::Less);
        assert_eq!(parent.keys(), []);
        assert_eq!(parent.children[0].keys(), [1, 2, 3, 50, 70]);
    }

    #[test]
    fn collapse_children_right() {
        let left = Box::new(InternalNode {
            keys: vec![1],
            children: vec![testnode(), testnode()]
        });
        let right = Box::new(InternalNode {
            keys: vec![70, 80, 90],
            children: vec![testnode(), testnode(), testnode(), testnode()]
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right]
        };
        parent.merge_collapse(0, Neighbor::Greater);
        assert_eq!(parent.keys(), []);
        assert_eq!(parent.children[0].keys(), [1, 50, 70, 80, 90]);
    }

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

    #[test]
    fn remove_reverse() {
        let mut tree = BTree::new(4);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in (0..256).rev() {
            assert_eq!(tree.remove(i), Some(i));
            assert_eq!(tree.remove(i), None);
        }
    }

    #[test]
    fn remove_even() {
        let mut tree = BTree::new(4);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..128 {
            assert_eq!(tree.remove(i * 2), Some(i * 2));
            assert_eq!(tree.remove(i * 2), None);
            assert_eq!(tree.get(i * 2 + 1), Some(i * 2 + 1));
        }
    }

}
