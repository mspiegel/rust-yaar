
struct Node {
    keys: Vec<i32>,
    vals: Option<Vec<i32>>,
    children: Option<Vec<Box<Node>>>,
}

#[derive(Default)]
pub struct BTree {
    root: Option<Box<Node>>,
}

impl BTree {
    pub fn new() -> BTree {
        Default::default()
    }

    pub fn get(&self, key: i32) -> Option<i32> {
        match self.root {
            None => None,
            Some(ref node) => node.get(key),
        }
    }
}

impl Node {
    fn child(&self, index: usize) -> &Box<Node> {
        self.children.as_ref().unwrap().get(index).unwrap()
    }

    fn get(&self, key: i32) -> Option<i32> {
        let position = self.keys.binary_search(&key);
        match self.vals {
            None => {
                match position {
                    Ok(index) | Err(index) => self.child(index).get(key),
                }
            }
            Some(ref values) => {
                match position {
                    Ok(index) => Some(*values.get(index).unwrap()),
                    Err(_) => None,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_construction() {
        let mut tree = BTree::new();
        assert_eq!(tree.get(0), None);
        //        assert_eq!(tree.insert(0, 1), None);
        //        assert_eq!(tree.insert(0, 2), Some(1));
        //        assert_eq!(tree.get(0), Some(2));
    }
}
