use crate::num_traits::*;

#[derive(Clone, Debug)]
pub struct Juggler{
    n: u64,
    size: u64,
    state: Vec<u64>,
}

impl Juggler{
    fn get_state(n: u64, size: u64) -> Vec<u64>{
        let size = size + 1;
        let n_vecs: usize = (n/64) as usize;
        // println!("n_vecs = {n_vecs}");
        let mut res: Vec<u64> = vec![];
        res = [res,vec![u64::MAX;n_vecs]].concat();
        if (n%64)!=0{
            let right_nullifier = u64::MAX>>(n%64);
            // println!("right nullifier = {:b}", right_nullifier);
            let last: u64 = u64::MAX-right_nullifier;
            // println!("last = {last:b}");
            res.push(last);
        }
        let more_n_vecs = (size/64-n/64) as usize;
        // println!("size = {size}, more_n_nvecs = {more_n_vecs}");
        res = [res, vec![0; more_n_vecs]].concat();
        let l = res.len();
        res[l-1] |= 1;
        res
    }

    pub fn new(n: u64, size: u64) -> Self{
        Self{n, size, state: Self::get_state(n, size)}
    }
    pub fn padding(&self) -> i32{
        return 64-(self.n%64u64) as i32
    }
    pub fn len(&self) -> u64{
        self.size
    }
    pub fn get_ith_bit(&self, i: usize) -> bool{
        assert!((i as u64)<self.size);
        let r1 = i/64;
        let r2 = 63-(i%64);
        self.state[r1].ith_bit(r2)
    }
    pub fn move_right_bit(&mut self, i: usize) -> Result<(),()>{
        assert!(((i as u64)+1)<self.size);
        if self.get_ith_bit(i)==false{
            return Ok(())
        }
        let r1 = i/64;
        let r2 = 63-(i%64);
        if r2 == 0{
            if r1+1 == self.state.len(){
                return Err(());
            } 
            self.state[r1] ^= 1;
            self.state[r1+1] |= u64::MAX-(u64::MAX>>1);
            return Ok(())
        }
        if self.get_ith_bit(i+1){
            return Err(());
        }
        self.state[r1] ^= (3u64<<62)>>(i%64);
        Ok(())
    }
    pub fn set_bit(&mut self, i: usize, x: bool){
        assert!((i as u64)<self.size);
        let r1 = i/64;
        let r2 = 63-(i%64);
        if x{
            self.state[r1] |= 1<<r2
        } else {
            self.state[r1] &= u64::MAX-(1<<r2);
        }
    }
    pub fn print_state(&self){
        print!("juggler state = [");
        for (i, n) in self.state.iter().enumerate(){
            print!("{:064b}", n);
            if i+1 < self.state.len(){
                print!(", ");
            }
        }
        println!("]");
    }
    pub fn print_from_vec<T>(v: &Vec<u64>, name: T) where T: ToString {
        print!("{} = [",name.to_string());
        for (i, n) in v.iter().enumerate(){
            print!("{:064b}", n);
            if i+1 < v.len(){
                print!(", ");
            }
        }
        println!("]");
    }
}

impl Iterator for Juggler{
    type Item = JugglerState;
    fn next(&mut self) -> Option<Self::Item>{
        
        let mut done = true;
        for i in 0..((self.size-self.n) as usize){
            if self.get_ith_bit(i){
                done = false;
                break;
            }
        }
        if done{
            return None;
        }
        if self.state.last().unwrap()&1 == 1{
            *self.state.last_mut().unwrap() &= u64::MAX-1;
            return Some(JugglerState::new(&self.state, self.size));
        } 
        let mut passed = 1;
        let mut gaps = false;
        for i in (0..self.size).rev(){
            if self.get_ith_bit(i as usize){
                if !gaps{
                    passed += 1;
                } else {
                    for j in i..self.size{
                        self.set_bit(j as usize, false);
                    }
                    for j in i+1..i+1+passed{
                        self.set_bit(j as usize, true);
                    }
                    return Some(JugglerState::new(&self.state, self.size));
                }
            } else {
                gaps = true;
            }
        }
        None
    }
}

pub struct JugglerState{
    state: Vec<u64>,
    size: u64,
    rindex: u64,
}

impl JugglerState{
    pub fn new(state: &Vec<u64>, size: u64) -> Self{
        JugglerState { state: state.clone(), size, rindex: 0}
    }
}

impl Iterator for JugglerState{
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        self.rindex += 1;
        if self.rindex - 1 >= self.size{
            return None
        }
        let rindex = self.rindex-1;
        Some(self.state[(rindex/64) as usize].ith_bit((63-(rindex%64)) as usize))
    }
}

// juggling is supposed to be like this:
// juggler input: n=3, max=6
//
// auto computed:
//  -length = 8
//  -padding =  length-max = 2
//
//      |
// 11100000
// 11010000
// 11001000
// 11000100
// 10110000
// 10101000
// 10100100
// 10011000
// 10010100
// 10001100
// 01110000
// 01101000
// 01100100
// 01011000
// 01010100
// 01001100
// 00111000
// 00110100
// 00101100
// 00011100
