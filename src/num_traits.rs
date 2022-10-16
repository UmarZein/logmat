use num::*;
use std::ops::*;
pub trait BitWiz{
    fn sum_bits(&self) -> u64;
    fn ith_bit(&self, i: usize) -> bool;
}


impl<T> BitWiz for T 
    where T: Shr<Output = T> + BitAnd + Copy,
    T: Into<u64>,
    <T as Shr>::Output: Into<u64>,
    <T as BitAnd>::Output: Into<u64>{
    

    fn sum_bits(&self) -> u64 {
        let mut total = 0u64;
        let cache: u64 = (*self).into();
        for i in 0..64u64{
            total += (cache>>i)&1u64;
        }
        total
    }

    fn ith_bit(&self, i: usize) -> bool{
        let i = i as u64;
        let cache: u64 = (*self).into();
        ((cache>>i)&1u64)>0
    }
}

