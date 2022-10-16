use std::{fmt, cmp::Ordering, collections::{HashMap, hash_map::DefaultHasher}, hash::{Hash, Hasher}};
use crate::var_iter::*;
// look, these words have cool colors wooo~ -> BUG TODO FIXME NOTE HACK WARNING
// prop.rs
#[derive(PartialEq,Eq,Hash,PartialOrd, Ord)]
pub enum PropUntitled{
    Atom,
    Var,
    Scope,
    Not,
    Conj,
    Disj,
    Biimpl,
    Xor,
    LogEqu,
    Then,
    Cause
}
#[derive(Debug,Clone,PartialEq,Eq,PartialOrd, Ord)]
pub enum Prop{
    Atom(bool),
    Var(String),
    
    Scope(Box<Prop>),
    Not(Box<Prop>),
    
    Conj(Vec<Prop>),
    Disj(Vec<Prop>),
    Biimpl(Vec<Prop>),
    Xor(Vec<Prop>),
    LogEqu(Vec<Prop>),
    
    Then([Box<Prop>;2]),
    Cause([Box<Prop>;2]),
}

impl Prop{
    pub fn is_structurally_eq(&self, p2: Prop) -> bool{
        let hasher = DefaultHasher::default();
        let mut h1 = hasher.clone();
        let mut h2 = hasher.clone();
        self.hash(&mut h1);
        p2.hash(&mut h2);
        return h1.finish()==h2.finish();
    }
    
    pub fn all_iotta(&self) -> Result<Vec<bool>, String>{
        let mut res: Vec<bool> = vec![];
        for i in self.get_var_iter(){
            res.push(self.swap(&i).evaluate()?)
        }
        Ok(res)
    }
    
    pub fn is_logically_eq(&self, other: &Prop) -> Result<bool,String>{
        if self.get_vars() == other.get_vars(){
            for i in self.get_var_iter(){
                if (self.swap(&i).evaluate()?) != (other.swap(&i).evaluate()?){
                    return Ok(false)
                }
            }
            return Ok(true)
        }
        Ok(false)
    }

    pub fn evaluate(&self) -> Result<bool,String>{
        use Prop::*;
        match self{
            Atom(x) => Ok(*x),
            Var(_) => Err(String::from("There shouldn't be any variables")),
            Not(bx) => Ok(!(bx.evaluate()?)),
            
            Conj(x) => {
                for i in x{
                    if !(i.evaluate()?){
                        return Ok(false)
                    }
                }
                Ok(true)
            },
            Disj(x) => {
                for i in x{
                    if i.evaluate()?{
                        return Ok(true)
                    }
                }
                Ok(false)
            },
            Xor(x) => {
                let mut ret = false;
                for i in x{
                    ret = ret^(i.evaluate()?);
                }
                Ok(ret)
            },
            Biimpl(x) => {
                let mut ret = false;
                for i in x{
                    ret = ret^(i.evaluate()?);
                }
                Ok(!ret)
            },
            LogEqu(_) => Err(String::from("can not evaluate logical equivalence operator")),
            
            Then([x, y]) => {
                if x.evaluate()? == true{
                    if y.evaluate()? == false{
                        return Ok(false)
                    }
                }
                Ok(true)
            },
            Cause([x, y]) => {
                if y.evaluate()? == true{
                    if x.evaluate()? == false{
                        return Ok(false)
                    }
                }
                Ok(true)
            },
            
            _ => Ok(false),
        }
    }

    pub fn get_vars(&self) -> Vec<String>{
        let mut res = Vec::<String>::new();
        use Prop::*;
        match self{
            Var(s) => res.push(s.clone()),
            Not(bx) => res = [res, bx.get_vars()].concat(),
            
            Conj(x) => for i in x{res = [res, i.get_vars()].concat()},
            Disj(x) => for i in x{res = [res, i.get_vars()].concat()},
            Xor(x) => for i in x{res = [res, i.get_vars()].concat()},
            Biimpl(x) => for i in x{res = [res, i.get_vars()].concat()},
            LogEqu(x) => for i in x{res = [res, i.get_vars()].concat()},
            
            Then(xy) => for i in xy{res = [res, i.get_vars()].concat()},
            Cause(xy) => for i in xy{res = [res, i.get_vars()].concat()},
            
            _ => (),
        };
        assert!("p".partial_cmp("p") == Some(Ordering::Equal));
        res.sort();
        res.dedup();
        return res
    }
    
    pub fn get_var_iter(&self) -> VariableIterator{
        let v = self.get_vars();
        let len = v.clone().len();
        VariableIterator{v,started:false,c:vec![0;(len as f32/8 as f32).ceil() as usize]}
    }

    pub fn swap(&self, v: &HashMap<String,bool>) -> Prop{
        use Prop::*;
        match self{
            Atom(x) => Atom(*x),
            Var(s) => match v.get(s){
                    Some(x) => Atom(*x),
                    None => Var(s.clone())
                }
            ,
            Not(bx) => Not(Box::<Prop>::new(bx.swap(v))),
            Scope(bx) => Scope(Box::<Prop>::new(bx.swap(v))),

            Conj(x) => Conj({
                let mut x2 = vec![];
                for i in x{
                        x2.push(i.swap(v))
                    }
                x2}),
            Disj(x) => Disj({
                let mut x2 = vec![];
                for i in x{
                        x2.push(i.swap(v))
                    }
                x2}),
            Xor(x) => Xor({
                let mut x2 = vec![];
                for i in x{
                        x2.push(i.swap(v))
                    }
                x2}),
            Biimpl(x) => Biimpl({
                let mut x2 = vec![];
                for i in x{
                        x2.push(i.swap(v))
                    }
                x2}),
            LogEqu(x) => LogEqu({
                let mut x2 = vec![];
                for i in x{
                        x2.push(i.swap(v))
                    }
                x2}),
            
            Then([x, y]) => Then([Box::<Prop>::new(x.swap(v)),Box::<Prop>::new(y.swap(v))]),
            Cause([x, y]) => Cause([Box::<Prop>::new(x.swap(v)),Box::<Prop>::new(y.swap(v))]),
        }
        
    }

    pub fn is_valid(&self) -> Result<bool, String>{
        for i in self.get_var_iter(){
            if self.swap(&i).evaluate()? == false{
                return Ok(false)
            }
        }
        Ok(true)
    }
    pub fn is_satisfiable(&self) -> Result<bool, String>{
        for i in self.get_var_iter(){
            if self.swap(&i).evaluate()? == true{
                return Ok(true)
            }
        }
        Ok(false)
    }
    pub fn is_contradictory(&self) -> Result<bool, String>{
        for i in self.get_var_iter(){
            if self.swap(&i).evaluate()? == true{
                return Ok(false)
            }
        }
        Ok(true)
    }
    pub fn is_contingent(&self) -> Result<bool, String>{
        Ok(!(self.is_contradictory()?||self.is_valid()?))
    }
}
// TODO: find difference between .iter() and .into_iter()
impl Hash for Prop {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Prop::*;
        use PropUntitled as PU;
        match self{
            Atom(b) => {PU::Atom.hash(state);b.hash(state)},
            Var(s) => {PU::Var.hash(state);s.hash(state)},
            
            Scope(bp) => {PU::Scope.hash(state);(*bp).hash(state)},
            Not(bp) => {PU::Not.hash(state);(*bp).hash(state)},
            
            Conj(vp) => {PU::Conj.hash(state);let mut vpc = (*vp).clone();vpc.sort();vpc.hash(state)},
            Disj(vp) => {PU::Disj.hash(state);let mut vpc = (*vp).clone();vpc.sort();vpc.hash(state)},
            Biimpl(vp) => {PU::Biimpl.hash(state);let mut vpc = (*vp).clone();vpc.sort();vpc.hash(state)},
            Xor(vp) => {PU::Xor.hash(state);let mut vpc = (*vp).clone();vpc.sort();vpc.hash(state)},
            LogEqu(vp) => {PU::LogEqu.hash(state);let mut vpc = (*vp).clone();vpc.sort();vpc.hash(state)},
            
            Then(bp2) => {PU::Then.hash(state);(*bp2).hash(state)},
            Cause(bp2) => {PU::Cause.hash(state);(*bp2).hash(state)},
        }
    }
}

impl fmt::Display for Prop{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn impl_box_p(bp: Box<Prop>) -> String{
            impl_p(*bp) 
        }
        /// returns the reversed precedence of an operator by delimiter
        fn d2v(delimiter: &str)->u8{
            match delimiter{
                "¬" => 1,
                "∧" => 2,
                "∨" => 3,
                "⊕" => 4,
                "→" => 5,
                "←" => 6,
                "↔" => 7,
                "≡" => 8,
                _ => u8::MAX
            }
        }
        /// returns the reversed precedence of an operator by prop
        fn p2v(p: Prop)->u8{
            use Prop::*;
            match p{
                Atom  (_) => 0,
                Var   (_) => 0,
                Not   (_) => 1,
                Conj  (_) => 2,
                Disj  (_) => 3,
                Xor   (_) => 4,
                Then  (_) => 5,
                Cause (_) => 6,
                Biimpl(_) => 7,
                LogEqu(_) => 8,
                _ => u8::MAX,
            }
        }
        fn impl_box_pv_d(pv: Vec<Prop>, delimiter: &str) -> String{
            let mut s = String::new();
            for (i,p) in (&pv).into_iter().enumerate(){
                if p2v(p.clone()) >= d2v(delimiter){
                    s.push('(');
                }
                s.push_str(impl_p(p.clone()).as_str());
                if p2v(p.clone()) >= d2v(delimiter){
                    s.push(')');
                }
                if i+1 != pv.len(){
                    s.push_str(delimiter);
                }
            }
            s
        }
        fn impl_p(p: Prop) -> String{
            use Prop::*;
            match p{
                Atom(true) => String::from("T"),
                Atom(false) => String::from("F"),
                Var(s) => s,
                Scope(inner) => String::from(format!("({})", impl_box_p(inner))),
                Not(inner) => {
                    match *inner{
                        Atom(_) => String::from(format!("¬{}", impl_box_p(inner))),
                        Var(_) => String::from(format!("¬{}", impl_box_p(inner))),
                        Scope(_) => String::from(format!("¬{}", impl_box_p(inner))),
                        _ => String::from(format!("¬({})", impl_box_p(inner)))
                    }
                },
                
                Conj  (pv) => impl_box_pv_d(pv, "∧"),
                Disj  (pv) => impl_box_pv_d(pv, "∨"),
                Xor   (pv) => impl_box_pv_d(pv, "⊕"),
                Biimpl(pv) => impl_box_pv_d(pv, "↔"),
                LogEqu(pv) => impl_box_pv_d(pv, "≡"),
                
                Then  ([p1, p2]) => impl_box_pv_d(vec![*p1, *p2], "→"),
                Cause ([p1, p2]) => impl_box_pv_d(vec![*p1, *p2], "←"),
                // _ => String::from("_")
            }
        }
        write!(f,"{}",impl_p(self.clone()))
    }
}

