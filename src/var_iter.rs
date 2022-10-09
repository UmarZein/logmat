use std::collections::HashMap;

pub struct VariableIterator{
    pub v: Vec<String>,
    pub c: Vec<u8>,
    pub started: bool,
}

pub trait Booleanize{
    fn booleanize(&self) -> Vec<bool>;
}

impl Booleanize for Vec<u8> {
    fn booleanize(&self) -> Vec<bool> {
        let mut res: Vec<bool> = vec![];
        for n in self.into_iter().rev(){
            for i in 0..8u8{
                let tmp = (*n&(1u8<<i))>0;
                res.push(tmp);
            }
        }
        res
    }
}

impl Iterator for VariableIterator{
    type Item = HashMap<String,bool>;
    fn next(&mut self) -> Option<Self::Item>{
        fn make_hm(v:Vec<String>,b:Vec<bool>) -> HashMap<String,bool>{
            assert_eq!(v.len(),b.len());
            let mut hm = HashMap::<String,bool>::new();
            for i in 0..v.len(){
                hm.insert(v[i].clone(),b[i]);
            }
            hm
        }
        
        if self.started==false{
            self.started=true;
            return Some(make_hm(self.v.clone(), vec![false;self.v.len()]));   
        }
        let mut complete = true;
        let tmp = self.c.booleanize()[..self.v.len()].to_vec();
        for i in tmp{
            if i == false{
                complete = false;
                break;
            }
        }
        if complete{
            return None;
        }
        let mut carry = true;
        for n in self.c.iter_mut().rev(){
            if carry{
                if *n == u8::MAX{
                    carry = true;
                    *n = 0u8;
                }
                else{
                    carry = false;
                    *n += 1u8;
                }
            }
        }
        let mut reversed = Vec::<bool>::new();
        let booleanized = self.c.booleanize();
        for i in 0..self.v.len(){
            reversed.push(booleanized[i]);
        }
        let res = make_hm(self.v.clone(),reversed);
        return Some(res);
    }
}

