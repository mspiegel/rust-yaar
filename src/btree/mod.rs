
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
    pub fn new(max: usize) -> BTree {
        BTree{ root: None, max: max }
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(ref node) => node.get(key)
        }
    }

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

    fn value(&self, index: usize) -> i32 {
        *self.ref_values().get(index).unwrap()
    }

    fn child(&self, index: usize) -> &Box<Node> {
        self.ref_children().get(index).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_construction() {
        let mut tree = BTree::new(2);
        assert_eq!(tree.get(0), None);
        assert_eq!(tree.insert(0, 1), None);
        assert_eq!(tree.insert(0, 2), Some(1));
        assert_eq!(tree.get(0), Some(2));
    }

    #[test]
    fn insert_sequence() {
        let mut tree = BTree::new(2);
        for i in 0..256 {
            assert_eq!(tree.insert(i, i), None);
            assert_eq!(tree.get(i), Some(i));
        }
    }
}
