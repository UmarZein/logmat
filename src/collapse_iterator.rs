use std::fmt::Debug;

pub trait IntoCollapseIterator2D {
    type Item;
    fn into_collapse_iterator_2d(&self) -> CollapseIterator2D<Self::Item>;
}

impl<T> IntoCollapseIterator2D for Vec<Vec<T>>
where
    T: Clone,
{
    type Item = T;
    fn into_collapse_iterator_2d(&self) -> CollapseIterator2D<Self::Item> {
        return CollapseIterator2D::<T>::new(self.clone());
    }
}

#[derive(Debug, Clone)]
pub struct CollapseIterator2D<T> {
    v: Vec<Vec<T>>,
    indices: Vec<usize>,
    i: u64,
}

impl<T> CollapseIterator2D<T> {
    pub fn new(v: Vec<Vec<T>>) -> CollapseIterator2D<T> {
        let len = v.len();
        CollapseIterator2D {
            v,
            indices: [0].repeat(len),
            i: 0,
        }
    }
    fn n_possibilities(&self) -> u64 {
        let mut prod = 1u64;
        for i in self.v.iter() {
            prod *= i.len() as u64
        }
        prod
    }
}

impl<T> Iterator for CollapseIterator2D<T>
where
    T: Clone,
{
    type Item = Vec<T>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.i >= self.n_possibilities() {
            return None;
        }
        let mut result: Vec<T> = vec![];
        let sizes: Vec<usize> = self.v.iter().map(|x| x.len()).collect();
        for (i, v) in self.v.iter().enumerate() {
            let mut j = self.i;
            for size in sizes[0..i].iter() {
                j /= *size as u64;
            }
            result.push(v[(j as usize) % sizes[i]].clone());
        }
        self.i += 1;
        Some(result)
    }
}

// 3 4 5  <- A
// 2 4    <- B
// 1 2    <- C
//
// n=3
// sum=7
//
// i = sum - n
// i = 4
//
// 4 bit
//
// C = i%2
// B = i/2%2
// A = i/2/2%3
//
// 2*2*3=12
//
// i  : A B C
// 0    0 0 0
// 1    1 0 0
// 2    0 1 0
// 3    1 1 0
// 4    0 0 1
// 5    1 0 1
// 6    0 1 1
// 7    1 1 1
// 8    0 0 2
// 9    1 0 2
// 10   0 1 2
// 11   1 1 2
