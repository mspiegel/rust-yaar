#[derive(Debug)]
pub struct MinHeap {
    vals: Vec<i32>,
}

impl Default for MinHeap {
    fn default() -> MinHeap {
        MinHeap { vals: vec![0] }
    }
}

impl MinHeap {
    pub fn new() -> MinHeap {
        MinHeap::default()
    }

    /// Returns true if the heap contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::minheap::MinHeap;
    ///
    /// let mut a = MinHeap::new();
    /// assert!(a.is_empty());
    /// a.insert(1);
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        self.vals.len() - 1
    }

    /// Inserts a value into the heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use yaar::minheap::MinHeap;
    ///
    /// let mut heap = MinHeap::new();
    /// heap.insert(37);
    /// assert_eq!(heap.is_empty(), false);
    /// ```
    pub fn insert(&mut self, value: i32) {
        let mut i = self.vals.len();
        self.vals.push(value);
        while i > 1 && self.vals[i / 2].gt(&self.vals[i]) {
            self.vals.swap(i, i / 2);
            i /= 2;
        }
    }

    pub fn pop(&mut self) -> Option<i32> {
        if !self.is_empty() {
            let mut i = 1;
            let len = self.len();
            self.vals.swap(1, len);
            let min = self.vals.pop();
            let len = self.len();
            while i * 2 <= len {
                let ii = i * 2;
                let j = if ii < len && self.vals[ii].gt(&self.vals[ii + 1]) {
                    ii + 1
                } else {
                    ii
                };
                if !self.vals[i].gt(&self.vals[j]) {
                    break;
                }
                self.vals.swap(i, j);
                i = j;
            }
            min
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_sequence() {
        let mut heap = MinHeap::new();
        for i in (0..256).rev() {
            heap.insert(i);
        }
        for i in 0..256 {
            assert_eq!(Some(i), heap.pop());
        }
        assert_eq!(None, heap.pop());
    }
}
