use std::cmp;
use std::cmp::Ordering;
use std::fmt;
use std::mem;

/// A B+ tree node with height zero.
/// Leaf nodes store values.
#[derive(Debug)]
struct LeafNode {
    keys: Vec<i32>,
    vals: Vec<i32>,
}

/// A B+ tree node with height greater than zero.
/// Internal nodes store children.
#[derive(Debug)]
struct InternalNode {
    keys: Vec<i32>,
    children: Vec<Box<Node>>,
}

/// A B+ tree is defined by its root node and the
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
    Split(i32, Box<Node>),
    /// Pair (key, new) insertion did not cause the node to split.
    None,
}

/// Outcomes of a remove operation.
enum RemoveResult {
    /// The pair (key, val) was removed. The node is too small.
    Shrink(i32),
    /// The pair (key, val) was removed. The node is not too small.
    NoShrink(i32),
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
                let result = self.root.as_mut().unwrap().insert(key, value, self.max);
                match result {
                    // grow the height of the tree if necessary
                    InsertResult::Split(key, child) => {
                        let children = vec![self.root.take().unwrap(), child];
                        self.root = InternalNode::new_root(key, children);
                        None
                    }
                    InsertResult::Replace(value) => Some(value),
                    InsertResult::None => None,
                }
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
    /// use yaar::bplus::BTree;
    ///
    /// let mut map = BTree::new(16);
    /// map.insert(1, 1);
    /// assert_eq!(map.remove(1), Some(1));
    /// assert_eq!(map.remove(1), None);
    /// ```
    pub fn remove(&mut self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(_) => {
                let (prev, shrink) = {
                    let node = self.root.as_mut().unwrap();
                    let prev = node.remove(key, self.min);
                    (prev, node.keys().is_empty())
                };
                if shrink {
                    // shrink the height of the tree if necessary
                    let mut node = self.root.take().unwrap();
                    self.root = node.shrink();
                }
                prev.result()
            }
        }
    }
}

trait Node: fmt::Debug {
    /// Returns the value (if exists) corresponding to the key.
    fn get(&self, key: i32) -> Option<i32>;
    /// Insert a (key, value) pair into the tree.
    fn insert(&mut self, key: i32, value: i32, max: usize) -> InsertResult;
    /// Remove a (key, value) pair from the tree.
    fn remove(&mut self, key: i32, min: usize) -> RemoveResult;
    /// Split the node if the number of keys is greater than max.
    fn split(&mut self, max: usize) -> InsertResult;

    /// Move some elements from a sibling node onto this node.
    /// Return value is the new partition between this node and sibling node.
    /// Return value will replace an existing key in the parent.
    fn shuffle(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling, min: usize) -> i32;
    /// Move all elements from this node to a sibling. This node will be deleted.
    fn collapse(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling);
    /// Reduce the height of a tree. Used only by the root of the tree.
    fn shrink(&mut self) -> Option<Box<Node>>;

    /// Accessor function for the keys of a node
    fn keys(&self) -> &[i32];

    /// Returns true if the number of keys is less than min.
    fn needs_merge(&self, min: usize) -> bool {
        self.keys().len() < min
    }

    /// Assert this value is a leaf node or panic on internal node
    fn as_leaf(&mut self) -> &mut LeafNode;
    /// Assert this value is an internal node or panic on leaf node
    fn as_internal(&mut self) -> &mut InternalNode;
}

impl Node for LeafNode {
    /// Accessor function for the keys of a node
    fn keys(&self) -> &[i32] {
        &self.keys
    }

    /// Assert this value is a leaf node or panic on internal node
    fn as_leaf(&mut self) -> &mut LeafNode {
        self
    }

    /// Assert this value is an internal node or panic on leaf node
    fn as_internal(&mut self) -> &mut InternalNode {
        panic!("attempt to convert leaf node into internal node");
    }

    /// Reduce the height of a tree. Used only by the root of the tree.
    /// Shrinking a leaf node generates an empty tree.
    fn shrink(&mut self) -> Option<Box<Node>> {
        debug_assert!(self.keys().is_empty());
        None
    }

    /// Returns the value (if exists) corresponding to the key.
    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        match position {
            Ok(index) => Some(self.vals[index]),
            Err(_) => None,
        }
    }

    /// Insert a (key, value) pair into the tree.
    fn insert(&mut self, key: i32, value: i32, max: usize) -> InsertResult {
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
        match prev {
            Some(value) => InsertResult::Replace(value),
            None => self.split(max),
        }
    }

    /// Remove a (key, value) pair from the tree.
    fn remove(&mut self, key: i32, min: usize) -> RemoveResult {
        let position = self.keys.binary_search(&key);
        let prev = match position {
            Ok(index) => {
                self.keys.remove(index);
                Some(self.vals.remove(index))
            }
            Err(_) => None,
        };
        match prev {
            Some(val) => RemoveResult::generate(self, min, val),
            None => RemoveResult::None,
        }
    }

    /// Split the node if the number of keys is greater than max.
    fn split(&mut self, max: usize) -> InsertResult {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            let newkeys = self.keys.split_off(partition);
            let newvals = self.vals.split_off(partition);
            InsertResult::Split(newkeys[0],
                                Box::new(LeafNode {
                                    keys: newkeys,
                                    vals: newvals,
                                }))
        } else {
            InsertResult::None
        }
    }

    /// Move some elements from a sibling node onto this node.
    /// Return value is the new partition between this node and sibling node.
    /// Return value will replace an existing key in the parent.
    #[allow(unused_variables)]
    fn shuffle(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling, min: usize) -> i32 {
        let sibling = sibling.as_leaf();
        let sibling_len = sibling.keys.len();
        let count = cmp::max(1, (sibling_len - min) / 2);
        Node::vec_shuffle(&mut sibling.keys, &mut self.keys, ord, count);
        Node::vec_shuffle(&mut sibling.vals, &mut self.vals, ord, count);
        LeafNode::post_shuffle_get(&sibling.keys, ord)
    }

    /// Move all elements from this node to a sibling. This node will be deleted.
    #[allow(unused_variables)]
    fn collapse(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling) {
        let sibling = sibling.as_leaf();
        Node::vec_collapse(&mut sibling.keys, &mut self.keys, ord);
        Node::vec_collapse(&mut sibling.vals, &mut self.vals, ord);
    }
}

impl Node for InternalNode {
    /// Accessor function for the keys of a node
    fn keys(&self) -> &[i32] {
        &self.keys
    }

    /// Assert this value is a leaf node or panic on internal node
    fn as_leaf(&mut self) -> &mut LeafNode {
        panic!("attempt to convert internal node into leaf node");
    }

    /// Assert this value is an internal node or panic on leaf node
    fn as_internal(&mut self) -> &mut InternalNode {
        self
    }

    /// Reduce the height of a tree. Used only by the root of the tree.
    /// Shrinking an internal node replaces the node with its only child.
    fn shrink(&mut self) -> Option<Box<Node>> {
        debug_assert!(self.keys().is_empty());
        Some(self.children.remove(0))
    }

    /// Returns the value (if exists) corresponding to the key.
    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        let index = InternalNode::index(position);
        self.children[index].get(key)
    }

    /// Insert a (key, value) pair into the tree.
    fn insert(&mut self, key: i32, value: i32, max: usize) -> InsertResult {
        let position = self.keys.binary_search(&key);
        let index = InternalNode::index(position);
        let recursive = self.children[index].insert(key, value, max);
        match recursive {
            InsertResult::Split(key, newchild) => {
                let index = InternalNode::index(self.keys.binary_search(&key));
                self.keys.insert(index, key);
                self.children.insert(index + 1, newchild);
                self.split(max)
            }
            _ => recursive,
        }
    }

    /// Remove a (key, value) pair from the tree.
    fn remove(&mut self, key: i32, min: usize) -> RemoveResult {
        let position = self.keys.binary_search(&key);
        let index = InternalNode::index(position);
        let recursive = self.children[index].remove(key, min);
        match recursive {
            RemoveResult::Shrink(val) => {
                self.merge_child(InternalNode::index(position), min);
                RemoveResult::generate(self, min, val)
            }
            _ => recursive,
        }
    }

    /// Split the node if the number of keys is greater than max.
    fn split(&mut self, max: usize) -> InsertResult {
        if self.keys.len() > max {
            let partition = self.keys.len() / 2;
            let mut newkeys = self.keys.split_off(partition);
            let newchildren = self.children.split_off(partition + 1);
            let newkey = newkeys.remove(0);
            InsertResult::Split(newkey,
                                Box::new(InternalNode {
                                    keys: newkeys,
                                    children: newchildren,
                                }))
        } else {
            InsertResult::None
        }
    }

    /// Move some elements from a sibling node onto this node.
    /// Return value is the new partition between this node and sibling node.
    /// Return value will replace an existing key in the parent.
    fn shuffle(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling, min: usize) -> i32 {
        let sibling = sibling.as_internal();
        let sibling_len = sibling.keys.len();
        let count = cmp::max(1, (sibling_len - min) / 2);
        InternalNode::pre_shuffle(&mut sibling.keys, pkey, ord);
        Node::vec_shuffle(&mut sibling.keys, &mut self.keys, ord, count);
        Node::vec_shuffle(&mut sibling.children, &mut self.children, ord, count);
        InternalNode::post_shuffle_take(&mut sibling.keys, ord)
    }

    /// Move all elements from this node to a sibling. This node will be deleted.
    fn collapse(&mut self, sibling: &mut Box<Node>, pkey: i32, ord: Sibling) {
        let sibling = sibling.as_internal();
        Node::vec_collapse_with_middle(&mut sibling.keys, &mut self.keys, pkey, ord);
        Node::vec_collapse(&mut sibling.children, &mut self.children, ord);
    }
}

impl LeafNode {
    fn new_leaf(key: i32, value: i32) -> Option<Box<Node>> {
        Some(Box::new(LeafNode {
            keys: vec![key],
            vals: vec![value],
        }))
    }

    /// Copy the new partition key from a child node. The key
    /// will be inserted into the parent of this node. The
    /// insertion is performed by InternalNode::set_parent_key().
    fn post_shuffle_get(sibling: &[i32], ord: Sibling) -> i32 {
        match ord {
            Sibling::Less => {
                let len = sibling.len();
                sibling[len - 1]
            }
            Sibling::Greater => sibling[0],
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

    /// Using a binary search of the keys as input, return the index of
    /// the child node as output. A key `k` divides the key space in half:
    /// values less than `k` and values greater than or equal to `k`.
    fn index(position: Result<usize, usize>) -> usize {
        match position {
            Ok(index) => index + 1,
            Err(index) => index,
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
            Ordering::Less | Ordering::Equal => Sibling::Less,
            Ordering::Greater => Sibling::Greater,
        }
    }

    /// The number of keys in a child node is less than
    /// the minimum. Either shuffle elements from a sibling
    /// node or collapse this node into a sibling.
    fn merge_child(&mut self, index: usize, min: usize) {
        let ord = self.merge_select_sibling(index);
        let sib_index = InternalNode::sibling(index, ord);
        let sib_len = self.children[sib_index].keys().len();
        if sib_len > min {
            self.merge_shuffle(index, ord, min);
        } else {
            self.merge_collapse(index, ord);
        }
    }

    /// Move some elements from a sibling node onto this node.
    fn merge_shuffle(&mut self, index: usize, ord: Sibling, min: usize) {
        let pkey = self.get_parent_key(index, ord);
        let ckey = {
            let (mut child, mut sibling) = self.partition(index, ord);
            child.shuffle(sibling, pkey, ord, min)
        };
        self.set_parent_key(ckey, index, ord);
    }

    /// Move all elements from this node to a sibling. This node will be deleted.
    fn merge_collapse(&mut self, index: usize, ord: Sibling) {
        let pkey = self.get_parent_key(index, ord);
        {
            let (mut child, mut sibling) = self.partition(index, ord);
            child.collapse(sibling, pkey, ord);
        }
        self.drop_parent_key(index, ord);
        self.children.remove(index);
    }

    /// Get the partition key associated with a child node to be merged.
    /// The partition key is used when merging internal nodes and is
    /// unused when merging leaf nodes.
    fn get_parent_key(&self, index: usize, ord: Sibling) -> i32 {
        match ord {
            Sibling::Less => self.keys[index - 1],
            Sibling::Greater => self.keys[index],
        }
    }

    /// Replace a key in the parent node at completion of a shuffle operation.
    /// This is the second half of a swap operation. The first half is
    /// performed by InternalNode::pre_shuffle().
    fn set_parent_key(&mut self, key: i32, index: usize, ord: Sibling) {
        match ord {
            Sibling::Less => {
                self.keys[index - 1] = key;
            }
            Sibling::Greater => {
                self.keys[index] = key;
            }
        }
    }

    /// Eliminate a key associated with a child node that is deleted.
    /// The child node is deleted when it has too few elements and
    /// its left and right siblings do not have extra elements to donate.
    fn drop_parent_key(&mut self, index: usize, ord: Sibling) {
        match ord {
            Sibling::Less => {
                self.keys.remove(index - 1);
            }
            Sibling::Greater => {
                self.keys.remove(index);
            }
        }
    }

    /// Return a pair of references - the child node that is to
    /// be merged and the sibling of the child node.
    fn partition(&mut self, index: usize, ord: Sibling) -> (&mut Box<Node>, &mut Box<Node>) {
        match ord {
            Sibling::Less => {
                let (left, right) = self.children.split_at_mut(index);
                let index = left.len() - 1;
                (&mut right[0], &mut left[index])
            }
            Sibling::Greater => {
                let (left, right) = self.children.split_at_mut(index + 1);
                let index = left.len() - 1;
                (&mut left[index], &mut right[0])
            }
        }
    }

    /// Copy a key from the parent node into a child node prior to shuffle operation.
    /// This is the first half of a swap operation. The second half is
    /// performed by InternalNode::set_parent_key().
    fn pre_shuffle(sibling: &mut Vec<i32>, key: i32, ord: Sibling) {
        match ord {
            Sibling::Less => {
                sibling.push(key);
            }
            Sibling::Greater => {
                sibling.insert(0, key);
            }
        }
    }

    /// Extract the new partition key from a child node. The key
    /// will be inserted into the parent of this node. The
    /// insertion is performed by InternalNode::set_parent_key().
    fn post_shuffle_take(sibling: &mut Vec<i32>, ord: Sibling) -> i32 {
        match ord {
            Sibling::Less => sibling.pop().unwrap(),
            Sibling::Greater => sibling.remove(0),
        }
    }
}

impl Node {
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
}

impl RemoveResult {
    /// Extract the value stored by the RemoveResult
    fn result(&self) -> Option<i32> {
        match *self {
            RemoveResult::Shrink(val) |
            RemoveResult::NoShrink(val) => Some(val),
            RemoveResult::None => None,
        }
    }

    /// Generate a RemoveResult that stores a value
    fn generate(node: &Node, min: usize, val: i32) -> RemoveResult {
        if node.needs_merge(min) {
            RemoveResult::Shrink(val)
        } else {
            RemoveResult::NoShrink(val)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Node;
    use super::InternalNode;
    use super::LeafNode;
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
        LeafNode::new_leaf(0, 0).unwrap()
    }

    #[test]
    fn redistribute_children_left() {
        let left = Box::new(InternalNode {
            keys: vec![1, 2, 3, 4, 5, 6],
            children: vec![testnode(), testnode(), testnode(), testnode(), testnode(), testnode(),
                           testnode()],
        });
        let right = Box::new(InternalNode {
            keys: vec![70],
            children: vec![testnode(), testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right],
        };
        parent.merge_shuffle(1, Sibling::Less, 2);
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
            children: vec![testnode(), testnode(), testnode(), testnode(), testnode(), testnode(),
                           testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![18],
            children: vec![left, right],
        };
        parent.merge_shuffle(0, Sibling::Greater, 2);
        assert_eq!(parent.keys(), [30]);
        assert_eq!(parent.children[0].keys(), [15, 18, 20]);
        assert_eq!(parent.children[1].keys(), [40, 50, 60, 70]);
    }

    #[test]
    fn collapse_children_left() {
        let left = Box::new(InternalNode {
            keys: vec![1, 2, 3],
            children: vec![testnode(), testnode(), testnode(), testnode()],
        });
        let right = Box::new(InternalNode {
            keys: vec![70],
            children: vec![testnode(), testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right],
        };
        parent.merge_collapse(1, Sibling::Less);
        assert_eq!(parent.keys(), []);
        assert_eq!(parent.children[0].keys(), [1, 2, 3, 50, 70]);
    }

    #[test]
    fn collapse_children_right() {
        let left = Box::new(InternalNode {
            keys: vec![1],
            children: vec![testnode(), testnode()],
        });
        let right = Box::new(InternalNode {
            keys: vec![70, 80, 90],
            children: vec![testnode(), testnode(), testnode(), testnode()],
        });
        let mut parent = InternalNode {
            keys: vec![50],
            children: vec![left, right],
        };
        parent.merge_collapse(0, Sibling::Greater);
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
