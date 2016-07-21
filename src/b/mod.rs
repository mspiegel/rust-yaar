use std::cmp;
use std::cmp::Ordering;
use std::mem;

/// A B tree node
#[derive(Debug)]
struct Node {
    keys: Vec<i32>,
    vals: Vec<i32>,
    children: Option<Vec<Box<Node>>>,
}

/// A B tree is defined by its root node and the
/// min and max bounds on node size.
#[derive(Debug)]
pub struct BTree {
    root: Option<Box<Node>>,
    max: usize,
    min: usize,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
enum Sibling {
    Less,
    Greater,
}

/// Outcomes of an insert operation.
enum InsertResult {
    /// The pair (key, old) was replaced by (key, new).
    /// Node splitting cannot occur at value replacement.
    Replace(i32),
    /// Pair (key, new) insertion caused the node to split.
    Split(i32, i32, Box<Node>),
    /// Pair (key, new) insertion did not cause the node to split.
    None,
}

/// Outcomes of a remove operation.
enum RemoveResult<T: Copy> {
    /// The pair (key, val) was removed. The node is too small.
    Shrink(T),
    /// The pair (key, val) was removed. The node is not too small.
    NoShrink(T),
    /// No pair was removed.
    None,
}

impl BTree {
    /// Makes a new empty BTree.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::b::BTree;
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
    /// use yaar::b::BTree;
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
    /// use yaar::b::BTree;
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
    /// use yaar::b::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// assert_eq!(map.insert(37, 1), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, 2);
    /// assert_eq!(map.insert(37, 3), Some(2));
    /// ```
    pub fn insert(&mut self, key: i32, value: i32) -> Option<i32> {
        if self.root.is_none() {
            self.root = Node::new_leaf(key, value);
            None
        } else {
            let max = self.max;
            let result = self.mut_root().insert(key, value, max);
            match result {
                // grow the height of the tree if necessary
                InsertResult::Split(key, value, child) => {
                    let children = vec![self.take_root(), child];
                    self.root = Node::new_root(key, value, children);
                    None
                }
                InsertResult::Replace(value) => Some(value),
                InsertResult::None => None,
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::b::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(1), Some(1));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: i32) -> Option<i32> {
        if self.root.is_none() {
            None
        } else {
            let min = self.min;
            let prev = self.mut_root().remove(key, min);
            if self.ref_root().keys.is_empty() {
                // shrink the height of the tree if necessary
                self.root = self.take_root().shrink();
            }
            prev.result()
        }
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
            let min = self.min;
            let prev = self.mut_root().remove_min(min);
            if self.ref_root().keys.is_empty() {
                // shrink the height of the tree if necessary
                self.root = self.take_root().shrink();
            }
            prev.result()
        }
    }

    fn ref_root(&self) -> &Box<Node> {
        self.root.as_ref().unwrap()
    }

    fn mut_root(&mut self) -> &mut Box<Node> {
        self.root.as_mut().unwrap()
    }

    fn take_root(&mut self) -> Box<Node> {
        self.root.take().unwrap()
    }
}

impl Node {
    /// Returns true if the number of keys is less than min.
    fn needs_merge(&self, min: usize) -> bool {
        self.keys.len() < min
    }

    /// Reduce the height of a tree. Used only by the root of the tree.
    fn shrink(&mut self) -> Option<Box<Node>> {
        debug_assert!(self.keys.is_empty());
        match self.children {
            Some(ref mut children) => Some(children.remove(0)),
            None => None,
        }
    }

    /// Returns the value (if exists) corresponding to the key.
    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        match position {
            Ok(index) => Some(self.vals[index]),
            Err(index) => {
                match self.children {
                    Some(ref children) => children[index].get(key),
                    None => None,
                }
            }
        }
    }

    /// Insert a (key, value) pair into the tree.
    fn insert(&mut self, key: i32, value: i32, max: usize) -> InsertResult {
        let position = self.keys.binary_search(&key);
        match position {
            Ok(index) => {
                let prev = self.vals[index];
                self.vals[index] = value;
                InsertResult::Replace(prev)
            }
            Err(index) => {
                if self.children.is_some() {
                    let recursive = self.mut_children()[index].insert(key, value, max);
                    match recursive {
                        InsertResult::Split(key, value, newchild) => {
                            let index = self.keys.binary_search(&key).err().unwrap();
                            self.keys.insert(index, key);
                            self.vals.insert(index, value);
                            self.mut_children().insert(index + 1, newchild);
                            self.split(max)
                        }
                        _ => recursive,
                    }
                } else {
                    self.keys.insert(index, key);
                    self.vals.insert(index, value);
                    self.split(max)
                }
            }
        }
    }

    /// Remove a (key, value) pair from the tree.
    fn remove(&mut self, key: i32, min: usize) -> RemoveResult<i32> {
        let position = self.keys.binary_search(&key);
        match position {
            Ok(index) => {
                match self.children {
                    Some(_) => {
                        let len = self.keys.len();
                        let prev = self.vals[index];
                        let recursive = if index == len - 1 {
                            self.mut_children()[len].remove_min(min)
                        } else {
                            self.mut_children()[index].remove_max(min)
                        };
                        let pair = recursive.result().unwrap();
                        self.keys[index] = pair.0;
                        self.vals[index] = pair.1;
                        self.post_remove(recursive.transform(prev), index, min)
                    }
                    None => {
                        self.keys.remove(index);
                        let prev = self.vals.remove(index);
                        RemoveResult::generate(self, min, prev)
                    }
                }
            }
            Err(index) => {
                match self.children {
                    Some(_) => {
                        let recursive = self.mut_children()[index].remove(key, min);
                        self.post_remove(recursive, index, min)
                    }
                    None => RemoveResult::None,
                }
            }
        }
    }

    /// If necessary shrink the child node at the end
    /// of a remove operation.
    fn post_remove<T: Copy>(&mut self,
                            prev: RemoveResult<T>,
                            index: usize,
                            min: usize)
                            -> RemoveResult<T> {
        match prev {
            RemoveResult::Shrink(val) => {
                self.merge_child(index, min);
                RemoveResult::generate(self, min, val)
            }
            _ => prev,
        }
    }

    /// Split the node if the number of keys is greater than max.
    fn split(&mut self, max: usize) -> InsertResult {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            let mut newkeys = self.keys.split_off(partition);
            let mut newvals = self.vals.split_off(partition);
            let newkey = newkeys.remove(0);
            let newval = newvals.remove(0);
            let newchildren = match self.children {
                Some(ref mut children) => Some(children.split_off(partition + 1)),
                None => None,
            };
            InsertResult::Split(newkey,
                                newval,
                                Box::new(Node {
                                    keys: newkeys,
                                    vals: newvals,
                                    children: newchildren,
                                }))
        } else {
            InsertResult::None
        }
    }

    /// Remove the minimum (key, val) pair from this subtree.
    fn remove_min(&mut self, min: usize) -> RemoveResult<(i32, i32)> {
        match self.children {
            Some(_) => {
                let recursive = self.mut_children()[0].remove_min(min);
                self.post_remove(recursive, 0, min)
            }
            None => {
                let key = self.keys.remove(0);
                let val = self.vals.remove(0);
                RemoveResult::generate(self, min, (key, val))
            }
        }
    }

    /// Remove the maximum (key, val) pair from this subtree.
    fn remove_max(&mut self, min: usize) -> RemoveResult<(i32, i32)> {
        match self.children {
            Some(_) => {
                let i = self.keys.len() - 1;
                let recursive = self.mut_children()[i].remove_max(min);
                self.post_remove(recursive, i, min)
            }
            None => {
                let key = self.keys.pop().unwrap();
                let val = self.vals.pop().unwrap();
                RemoveResult::generate(self, min, (key, val))
            }
        }
    }

    /// Move some elements from a sibling node onto this node.
    /// Return value is the new partition between this node and sibling node.
    /// Return value will replace an existing key in the parent.
    fn shuffle(&mut self,
               sibling: &mut Box<Node>,
               parent: (i32, i32),
               ord: Sibling,
               min: usize)
               -> (i32, i32) {
        let sibling_len = sibling.keys.len();
        let count = cmp::max(1, (sibling_len - min) / 2);
        Node::pre_shuffle(&mut sibling.keys, parent.0, ord);
        Node::pre_shuffle(&mut sibling.vals, parent.1, ord);
        Node::vec_shuffle(&mut sibling.keys, &mut self.keys, ord, count);
        Node::vec_shuffle(&mut sibling.vals, &mut self.vals, ord, count);
        if self.children.is_some() {
            let mut children = self.mut_children();
            let mut sibling_children = sibling.mut_children();
            Node::vec_shuffle(&mut sibling_children, &mut children, ord, count);
        }
        sibling.post_shuffle_take(ord)
    }

    /// Move all elements from this node to a sibling. This node will be deleted.
    fn collapse(&mut self, sibling: &mut Box<Node>, parent: (i32, i32), ord: Sibling) {
        Node::vec_collapse_with_middle(&mut sibling.keys, &mut self.keys, parent.0, ord);
        Node::vec_collapse_with_middle(&mut sibling.vals, &mut self.vals, parent.1, ord);
        if self.children.is_some() {
            let mut children = self.mut_children();
            let mut sibling_children = sibling.mut_children();
            Node::vec_collapse(&mut sibling_children, &mut children, ord);
        }
    }

    /// Given an index and the direction of a sibling return
    /// the index of the sibling.
    fn sibling(index: usize, ord: Sibling) -> usize {
        match ord {
            Sibling::Less => index - 1,
            Sibling::Greater => index + 1,
        }
    }

    /// Inspect the left and right siblings of a node
    /// and return the larger sibling. Select the left
    /// sibling in case of a tie.
    fn merge_select_sibling(&self, index: usize) -> Sibling {
        let children = self.ref_children();
        let leftsize = if index > 0 {
            children[index - 1].keys.len()
        } else {
            0
        };
        let rightsize = if index < children.len() - 1 {
            children[index + 1].keys.len()
        } else {
            0
        };
        if leftsize == 0 && rightsize == 0 {
            panic!("left and right children are empty");
        }
        match rightsize.cmp(&leftsize) {
            Ordering::Less | Ordering::Equal => Sibling::Less,
            Ordering::Greater => Sibling::Greater,
        }
    }

    /// The number of keys in a child node is less than
    /// the minimum. Either shuffle elements from a sibling
    /// node or collapse this node into a sibling.
    fn merge_child(&mut self, index: usize, min: usize) {
        let ord = self.merge_select_sibling(index);
        let sib_index = Node::sibling(index, ord);
        let sib_len = self.ref_children()[sib_index].keys.len();
        if sib_len > min {
            self.merge_shuffle(index, ord, min);
        } else {
            self.merge_collapse(index, ord);
        }
    }

    /// Move some elements from a sibling node onto this node.
    fn merge_shuffle(&mut self, index: usize, ord: Sibling, min: usize) {
        let pkeyval = self.get_parent_pair(index, ord);
        let ckeyval = {
            let (mut child, mut sibling) = self.partition(index, ord);
            child.shuffle(sibling, pkeyval, ord, min)
        };
        self.set_parent_pair(ckeyval, index, ord);
    }

    /// Move all elements from this node to a sibling. This node will be deleted.
    fn merge_collapse(&mut self, index: usize, ord: Sibling) {
        let pkeyval = self.get_parent_pair(index, ord);
        {
            let (mut child, mut sibling) = self.partition(index, ord);
            child.collapse(sibling, pkeyval, ord);
        }
        self.drop_parent_pair(index, ord);
        self.mut_children().remove(index);
    }

    /// Get the partition pair associated with a child node to be merged.
    /// The partition pair is used when merging internal nodes and is
    /// unused when merging leaf nodes.
    fn get_parent_pair(&self, index: usize, ord: Sibling) -> (i32, i32) {
        match ord {
            Sibling::Less => (self.keys[index - 1], self.vals[index - 1]),
            Sibling::Greater => (self.keys[index], self.vals[index]),
        }
    }

    /// Replace a pair in the parent node at completion of a shuffle operation.
    /// This is the second half of a swap operation. The first half is
    /// performed by InternalNode::pre_shuffle().
    fn set_parent_pair(&mut self, pair: (i32, i32), index: usize, ord: Sibling) {
        match ord {
            Sibling::Less => {
                self.keys[index - 1] = pair.0;
                self.vals[index - 1] = pair.1;
            }
            Sibling::Greater => {
                self.keys[index] = pair.0;
                self.vals[index] = pair.1;
            }
        }
    }

    /// Eliminate a pair associated with a child node that is deleted.
    /// The child node is deleted when it has too few elements and
    /// its left and right siblings do not have extra elements to donate.
    fn drop_parent_pair(&mut self, index: usize, ord: Sibling) {
        match ord {
            Sibling::Less => {
                self.keys.remove(index - 1);
                self.vals.remove(index - 1);
            }
            Sibling::Greater => {
                self.keys.remove(index);
                self.vals.remove(index);
            }
        }
    }

    /// Return a pair of references - the child node that is to
    /// be merged and the sibling of the child node.
    fn partition(&mut self, index: usize, ord: Sibling) -> (&mut Box<Node>, &mut Box<Node>) {
        match ord {
            Sibling::Less => {
                let (left, right) = self.mut_children().split_at_mut(index);
                let index = left.len() - 1;
                (&mut right[0], &mut left[index])
            }
            Sibling::Greater => {
                let (left, right) = self.mut_children().split_at_mut(index + 1);
                let index = left.len() - 1;
                (&mut left[index], &mut right[0])
            }
        }
    }

    /// Extract the new partition pair from a child node. The pair
    /// will be inserted into the parent of this node. The
    /// insertion is performed by InternalNode::set_parent_pair().
    fn post_shuffle_take(&mut self, ord: Sibling) -> (i32, i32) {
        match ord {
            Sibling::Less => (self.keys.pop().unwrap(), self.vals.pop().unwrap()),
            Sibling::Greater => (self.keys.remove(0), self.vals.remove(0)),
        }
    }

    /// Copy a value from the parent node into a child node prior to shuffle operation.
    /// This is the first half of a swap operation. The second half is
    /// performed by InternalNode::set_parent_pair().
    fn pre_shuffle(sibling: &mut Vec<i32>, value: i32, ord: Sibling) {
        match ord {
            Sibling::Less => {
                sibling.push(value);
            }
            Sibling::Greater => {
                sibling.insert(0, value);
            }
        }
    }

    /// Move some elements from the source vector to the destination vector.
    /// The Sibling direction determines whether elements are moved
    /// from the head or tail of the source vector.
    fn vec_shuffle<T>(src: &mut Vec<T>, dest: &mut Vec<T>, ord: Sibling, count: usize) {
        match ord {
            Sibling::Less => {
                let position = src.len() - count;
                let mut newdest = src.split_off(position);
                newdest.append(dest);
                *dest = newdest;
            }
            Sibling::Greater => {
                let newsrc = src.split_off(count);
                dest.append(src);
                *src = newsrc;
            }
        }
    }

    /// Move all elements from the child vector to the sibling vector.
    /// The Sibling direction determines whether elements are moved
    /// onto the head or tail of the sibling vector.
    fn vec_collapse<T>(sibling: &mut Vec<T>, child: &mut Vec<T>, ord: Sibling) {
        match ord {
            Sibling::Less => {
                sibling.append(child);
            }
            Sibling::Greater => {
                child.append(sibling);
                mem::swap(child, sibling);
            }
        }
    }

    /// Move all elements from the child vector to the sibling vector.
    /// A partition element is inserted between the old and new elements.
    fn vec_collapse_with_middle<T>(sibling: &mut Vec<T>,
                                   child: &mut Vec<T>,
                                   middle: T,
                                   ord: Sibling) {
        match ord {
            Sibling::Less => {
                sibling.push(middle);
                sibling.append(child);
            }
            Sibling::Greater => {
                child.push(middle);
                child.append(sibling);
                mem::swap(child, sibling);
            }
        }
    }

    fn new_leaf(key: i32, value: i32) -> Option<Box<Node>> {
        Some(Box::new(Node {
            keys: vec![key],
            vals: vec![value],
            children: None,
        }))
    }

    fn new_root(key: i32, value: i32, children: Vec<Box<Node>>) -> Option<Box<Node>> {
        Some(Box::new(Node {
            keys: vec![key],
            vals: vec![value],
            children: Some(children),
        }))
    }

    fn ref_children(&self) -> &Vec<Box<Node>> {
        self.children.as_ref().unwrap()
    }

    fn mut_children(&mut self) -> &mut Vec<Box<Node>> {
        self.children.as_mut().unwrap()
    }
}

impl<T: Copy> RemoveResult<T> {
    /// Extract the value stored by the RemoveResult
    fn result(&self) -> Option<T> {
        match *self {
            RemoveResult::Shrink(val) |
            RemoveResult::NoShrink(val) => Some(val),
            RemoveResult::None => None,
        }
    }

    /// Generate a RemoveResult that stores a value
    fn generate(node: &Node, min: usize, val: T) -> RemoveResult<T> {
        if node.needs_merge(min) {
            RemoveResult::Shrink(val)
        } else {
            RemoveResult::NoShrink(val)
        }
    }

    /// Generate a RemoveResult with value of a different type
    fn transform<U: Copy>(&self, val: U) -> RemoveResult<U> {
        match *self {
            RemoveResult::Shrink(_) => RemoveResult::Shrink(val),
            RemoveResult::NoShrink(_) => RemoveResult::NoShrink(val),
            RemoveResult::None => RemoveResult::None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Node;
    use super::Sibling;

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
    fn vec_shuffle() {
        let mut vec1 = vec![1, 2, 3];
        let mut vec2 = vec![4, 5, 6];
        Node::vec_shuffle(&mut vec1, &mut vec2, Sibling::Less, 2);
        assert_eq!(vec1, vec![1]);
        assert_eq!(vec2, vec![2, 3, 4, 5, 6]);

        let mut vec3 = vec![1, 2, 3];
        let mut vec4 = vec![4, 5, 6];
        Node::vec_shuffle(&mut vec4, &mut vec3, Sibling::Greater, 2);
        assert_eq!(vec3, vec![1, 2, 3, 4, 5]);
        assert_eq!(vec4, vec![6]);
    }

    fn testnode() -> Box<Node> {
        Node::new_leaf(0, 0).unwrap()
    }

    #[test]
    fn redistribute_children_left() {
        let left = Box::new(Node {
            keys: vec![1, 2, 3, 4, 5, 6],
            vals: vec![1, 2, 3, 4, 5, 6],
            children: Some(vec![testnode(), testnode(), testnode(), testnode(), testnode(),
                                testnode(), testnode()]),
        });
        let right = Box::new(Node {
            keys: vec![70],
            vals: vec![70],
            children: Some(vec![testnode(), testnode()]),
        });
        let mut parent = Node {
            keys: vec![50],
            vals: vec![50],
            children: Some(vec![left, right]),
        };
        parent.merge_shuffle(1, Sibling::Less, 2);
        assert_eq!(parent.keys, [5]);
        assert_eq!(parent.ref_children()[0].keys, [1, 2, 3, 4]);
        assert_eq!(parent.ref_children()[1].keys, [6, 50, 70]);
    }

    #[test]
    fn redistribute_children_right() {
        let left = Box::new(Node {
            keys: vec![15],
            vals: vec![15],
            children: Some(vec![testnode(), testnode()]),
        });
        let right = Box::new(Node {
            keys: vec![20, 30, 40, 50, 60, 70],
            vals: vec![20, 30, 40, 50, 60, 70],
            children: Some(vec![testnode(), testnode(), testnode(), testnode(), testnode(),
                                testnode(), testnode()]),
        });
        let mut parent = Node {
            keys: vec![18],
            vals: vec![18],
            children: Some(vec![left, right]),
        };
        parent.merge_shuffle(0, Sibling::Greater, 2);
        assert_eq!(parent.keys, [30]);
        assert_eq!(parent.ref_children()[0].keys, [15, 18, 20]);
        assert_eq!(parent.ref_children()[1].keys, [40, 50, 60, 70]);
    }

    #[test]
    fn collapse_children_left() {
        let left = Box::new(Node {
            keys: vec![1, 2, 3],
            vals: vec![1, 2, 3],
            children: Some(vec![testnode(), testnode(), testnode(), testnode()]),
        });
        let right = Box::new(Node {
            keys: vec![70],
            vals: vec![70],
            children: Some(vec![testnode(), testnode()]),
        });
        let mut parent = Node {
            keys: vec![50],
            vals: vec![50],
            children: Some(vec![left, right]),
        };
        parent.merge_collapse(1, Sibling::Less);
        assert_eq!(parent.keys, []);
        assert_eq!(parent.ref_children()[0].keys, [1, 2, 3, 50, 70]);
    }

    #[test]
    fn collapse_children_right() {
        let left = Box::new(Node {
            keys: vec![1],
            vals: vec![1],
            children: Some(vec![testnode(), testnode()]),
        });
        let right = Box::new(Node {
            keys: vec![70, 80, 90],
            vals: vec![70, 80, 90],
            children: Some(vec![testnode(), testnode(), testnode(), testnode()]),
        });
        let mut parent = Node {
            keys: vec![50],
            vals: vec![50],
            children: Some(vec![left, right]),
        };
        parent.merge_collapse(0, Sibling::Greater);
        assert_eq!(parent.keys, []);
        assert_eq!(parent.ref_children()[0].keys, [1, 50, 70, 80, 90]);
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
        assert!(tree.is_empty());
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
        assert!(tree.is_empty());
    }

    #[test]
    fn remove_even() {
        let mut tree = BTree::new(4);
        for i in 0..16 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..8 {
            assert_eq!(tree.remove(i * 2), Some(i * 2));
            assert_eq!(tree.remove(i * 2), None);
            println!("{:?}", tree);
            assert_eq!(tree.get(i * 2 + 1), Some(i * 2 + 1));
        }
    }

    #[test]
    fn remove_min() {
        let mut tree = BTree::new(4);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
        }
        for i in 0..256 {
            assert_eq!(tree.remove_min(), Some((i, i)));
        }
        assert_eq!(tree.remove_min(), None);
    }

}
