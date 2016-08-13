//! A Fenwick tree or binary indexed tree is a data structure
//! that can efficiently update elements and calculate prefix scans
//! in a table of numbers. This structure was proposed by Peter
//! Fenwick in 1994 to improve the efficiency of arithmetic coding
//! compression algorithms.
//!
//! There is a trade-off between the efficiency of element update
//! and prefix scan calculation. In a flat array of
//! n numbers, calculating prefix sum requires O(n) time,
//! while in an array of prefix sums, updating elements requires
//! O(n) time. Fenwick trees allow both operations to be performed in
//! O(log n) time. This is achieved by representing the numbers as
//! a tree, where the value of each node is the sum of the numbers
//! in that subtree. The tree structure allows operations to be
//! performed using only O(log n) node accesses.
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
        if index >= size {
            panic!("index must less than size");
        }
    }

    pub fn update(&mut self, mut index: usize, value: i32) {
        let size = self.vals.len();
        let op = self.operator;
        Fenwick::bounds_check(index, size);
        index += 1;
        while index <= size {
            self.vals[index] = op(self.vals[index], value);
            index += index & (!index + 1);
        }
    }

    pub fn get(&mut self, mut index: usize) -> i32 {
        let mut res = self.identity;
        let op = self.operator;
        Fenwick::bounds_check(index, self.vals.len());
        index += 1;
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
        for i in 0..10 {
            tree.update(i as usize, i);
        }
        let mut sum = 0;
        for i in 0..10 {
            sum += i;
            assert_eq!(sum, tree.get(i as usize));
        }
    }
}
