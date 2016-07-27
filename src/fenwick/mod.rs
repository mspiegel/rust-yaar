use std::iter;
use std::iter::FromIterator;

pub type BinOp = Fn(i32, i32) -> i32;

pub struct Fenwick<'a> {
    vals: Vec<i32>,
    operator: &'a BinOp,
    identity: i32,
}

impl<'a> Fenwick<'a> {
    pub fn new(size: usize, identity: i32, operator: &'a BinOp) -> Fenwick<'a> {
        Fenwick {
            vals: Vec::from_iter(iter::repeat(identity).take(size + 1)),
            operator: operator,
            identity: identity,
        }
    }

    fn bounds_check(index: usize, size: usize) {
        if index == 0 {
            panic!("index must be > 0 and <= size");
        }
        if index > size {
            panic!("index must be > 0 and <= size");
        }
    }

    pub fn update(&mut self, mut index: usize, value: i32) {
        let size = self.vals.len();
        let op = self.operator;
        Fenwick::bounds_check(index, size);
        while index <= size {
            self.vals[index] = op(self.vals[index], value);
            index += index & (!index + 1);
        }
    }

    pub fn get(&mut self, mut index: usize) -> i32 {
        let mut res = self.identity;
        let op = self.operator;
        Fenwick::bounds_check(index, self.vals.len());
        while index > 0 {
            res = op(res, self.vals[index]);
            index -= index & (!index + 1);
        }
        res
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitflip() {
        let val: usize = 24;
        assert_eq!(8, val & (!val + 1));
    }

    #[test]
    fn insert() {
        let add = &|a, b| a + b;
        let mut tree = Fenwick::new(10, 0, add);
        for i in 1..11 {
            tree.update(i as usize, i);
        }
        let mut sum = 0;
        for i in 1..11 {
            sum += i;
            assert_eq!(sum, tree.get(i as usize));
        }
    }
}
