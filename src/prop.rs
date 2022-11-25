use crate::var_iter::*;
use crate::qol_macros::*;

use std::ops::Deref;
use std::{
    cmp::Ordering,
    collections::{hash_map::DefaultHasher, HashMap},
    fmt,
    hash::{Hash, Hasher},
};
// look, these words have cool colors wooo~ -> BUG TODO FIXME NOTE HACK WARNING
// prop.rs
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PropUntitled {
    Atom,
    Var,
    Scope,
    Not,
    Conj,
    Disj,
    Biimpl,
    Xor,
    LogEqu,
    Impl,
}

/// Proposition types. 
/// Caveats:
///     - XOR has multiple input. if it contains odd number of true, 
///       it evaluates into true. this is different from the other 
///       interpretation of XOR as "one and only one true". this is 
///       because XOR(a,b,c) is interpreted as (a⊕b)⊕c
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prop {
    Atom(bool),
    Var(String),

    Scope(Box<Prop>),
    Not(Box<Prop>),

    Conj(Vec<Prop>),
    Disj(Vec<Prop>),
    Biimpl(Vec<Prop>),
    Xor(Vec<Prop>),
    LogEqu(Vec<Prop>),

    Impl([Box<Prop>; 2]),
}
// biimpl = p|-q&-p|q
// xor    = p&-q|-p&q
//
// -p&-q&n = CONJ(NOT(p),NOT(q),n...) = 2+len(n)+6+n.iter.compl.sum = 8 + len(n) + #n 
// -(p|q|n...) = NOT(DISJ(p,q,n)) = 1 + 2 * (2+len(n) + 2 + n.iter.compl.sum) = 9+2*(len(n) + #n)
//
//
impl Prop {
    pub fn complexity(&self) -> u64{
        use Prop::*;
        match self {
            Atom(_) => 0,
            Var(_) => 1,
            Scope(bp) => bp.complexity(),
            Not(bp) => 1+2*bp.complexity(),
            Conj(vp) => vp.len() as u64 + vp.iter().map(|p|p.complexity()).sum::<u64>(),
            Disj(vp) => vp.len() as u64 + vp.iter().map(|p|p.complexity()).sum::<u64>(),
            
            Biimpl(vp) => vp.len() as u64 + (vp.iter().map(|p|p.complexity()).sum::<u64>())*2,
            Xor(vp) => vp.len() as u64 + vp.iter().map(|p|p.complexity()).sum::<u64>()*2,

            LogEqu(vp) => 1+2*vp.iter().map(|p|p.complexity()).sum::<u64>(),

            Impl(bp2) => {
                let x=bp2[0].clone();
                let y=bp2[1].clone();
                1+disj!(n!(x.deref().clone()),y.deref().clone()).complexity()
            }
        }
    }
    pub fn is_structurally_eq(&self, p2: &Prop) -> bool {
        let hasher = DefaultHasher::default();
        let mut h1 = hasher.clone();
        let mut h2 = hasher.clone();
        self.hash(&mut h1);
        p2.hash(&mut h2);
        return h1.finish() == h2.finish();
    }

    pub fn all_iotta(&self) -> Result<Vec<bool>, String> {
        let mut res: Vec<bool> = vec![];
        for i in self.get_var_iter() {
            res.push(self.swap(&i).evaluate()?)
        }
        Ok(res)
    }

    /// returns `true` whether self and other is logically equal.
    /// errors:
    ///     Prop.swap(_) error
    pub fn is_logically_eq(&self, other: &Prop) -> Result<bool, String> {
        
        let mut v = self.get_vars();
        let v_ = v.clone();
        for i in other.get_vars(){
            if !v_.contains(&i){
                v.push(i);
            }
        }
        let len = v.clone().len();
        let iter = VariableIterator {
            v,
            started: false,
            c: vec![0; (len as f32 / 8 as f32).ceil() as usize],
        };

        for i in iter {
            if (self.swap(&i).evaluate()?) != (other.swap(&i).evaluate()?) {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    
    pub fn is_logically_opp(&self, other: &Prop) -> Result<bool, String> {
        let mut v = self.get_vars();
        let v_ = v.clone();
        for i in other.get_vars(){
            if !v_.contains(&i){
                v.push(i);
            }
        }
        let len = v.clone().len();
        let iter = VariableIterator {
            v,
            started: false,
            c: vec![0; (len as f32 / 8 as f32).ceil() as usize],
        };
        for i in iter {
            if (self.swap(&i).evaluate()?) == (other.swap(&i).evaluate()?) {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    pub fn evaluate(&self) -> Result<bool, String> {
        use Prop::*;
        match self {
            Atom(x) => Ok(*x),
            Var(_) => Err(String::from("There shouldn't be any variables")),
            Not(bx) => Ok(!(bx.evaluate()?)),

            Conj(x) => {
                for i in x {
                    if !(i.evaluate()?) {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Disj(x) => {
                for i in x {
                    if i.evaluate()? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Xor(x) => {
                let mut ret = false;
                for i in x {
                    ret = ret ^ (i.evaluate()?);
                }
                Ok(ret)
            }
            Biimpl(x) => {
                let mut ret = false;
                for i in x {
                    ret = ret ^ (i.evaluate()?);
                }
                Ok(!ret)
            }
            LogEqu(_) => Err(String::from(
                "can not evaluate logical equivalence operator",
            )),

            Impl([x, y]) => {
                if x.evaluate()? == true {
                    if y.evaluate()? == false {
                        return Ok(false);
                    }
                }
                Ok(true)
            }

            _ => Ok(false),
        }
    }

    pub fn get_vars(&self) -> Vec<String> {
        let mut res = Vec::<String>::new();
        use Prop::*;
        match self {
            Var(s) => res.push(s.clone()),
            Not(bx) => res = [res, bx.get_vars()].concat(),

            Conj(x) => {
                for i in x {
                    res = [res, i.get_vars()].concat()
                }
            }
            Disj(x) => {
                for i in x {
                    res = [res, i.get_vars()].concat()
                }
            }
            Xor(x) => {
                for i in x {
                    res = [res, i.get_vars()].concat()
                }
            }
            Biimpl(x) => {
                for i in x {
                    res = [res, i.get_vars()].concat()
                }
            }
            LogEqu(x) => {
                for i in x {
                    res = [res, i.get_vars()].concat()
                }
            }

            Impl(xy) => {
                for i in xy {
                    res = [res, i.get_vars()].concat()
                }
            }

            _ => (),
        };
        assert!("p".partial_cmp("p") == Some(Ordering::Equal));
        res.sort();
        res.dedup();
        return res;
    }

    pub fn get_var_iter(&self) -> VariableIterator {
        let v = self.get_vars();
        let len = v.clone().len();
        VariableIterator {
            v,
            started: false,
            c: vec![0; (len as f32 / 8 as f32).ceil() as usize],
        }
    }

    pub fn swap(&self, v: &HashMap<String, bool>) -> Prop {
        use Prop::*;
        match self {
            Atom(x) => Atom(*x),
            Var(s) => match v.get(s) {
                Some(x) => Atom(*x),
                None => Var(s.clone()),
            },
            Not(bx) => Not(Box::<Prop>::new(bx.swap(v))),
            Scope(bx) => Scope(Box::<Prop>::new(bx.swap(v))),

            Conj(x) => Conj({
                let mut x2 = vec![];
                for i in x {
                    x2.push(i.swap(v))
                }
                x2
            }),
            Disj(x) => Disj({
                let mut x2 = vec![];
                for i in x {
                    x2.push(i.swap(v))
                }
                x2
            }),
            Xor(x) => Xor({
                let mut x2 = vec![];
                for i in x {
                    x2.push(i.swap(v))
                }
                x2
            }),
            Biimpl(x) => Biimpl({
                let mut x2 = vec![];
                for i in x {
                    x2.push(i.swap(v))
                }
                x2
            }),
            LogEqu(x) => LogEqu({
                let mut x2 = vec![];
                for i in x {
                    x2.push(i.swap(v))
                }
                x2
            }),

            Impl([x, y]) => Impl([Box::<Prop>::new(x.swap(v)), Box::<Prop>::new(y.swap(v))]),
        }
    }

    pub fn is_valid(&self) -> Result<bool, String> {
        for i in self.get_var_iter() {
            if self.swap(&i).evaluate()? == false {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub fn is_satisfiable(&self) -> Result<bool, String> {
        for i in self.get_var_iter() {
            if self.swap(&i).evaluate()? == true {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub fn is_contradictory(&self) -> Result<bool, String> {
        for i in self.get_var_iter() {
            if self.swap(&i).evaluate()? == true {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub fn is_contingent(&self) -> Result<bool, String> {
        Ok(!(self.is_contradictory()? || self.is_valid()?))
    }

    pub fn print_truth_table(&self) {
        // +---+---+---+
        // | p | q | * |
        // |---+---+---|
        // | T | T | T |
        // |---+---+---|
        // | T | F | F |
        // |---+---+---|
        // | F | T | T |
        // |---+---+---|
        // | F | F | T |
        // +---+---+---+
        let vars = self.get_vars();
        let cols: Vec<String> = [vars.clone(), vec!["*".to_string()]].concat();
        let v_edge: String = ["+".to_string(), "---+".repeat(cols.len())].concat();
        let mut v_sep: String = ["|".to_string(), "---+".repeat(cols.len())].concat();
        v_sep = v_sep[..v_sep.len() - 1].to_string();
        v_sep.push('|');
        let header: String = [
            "|".to_string(),
            cols.iter()
                .map(|x| [" ".to_string(), x.clone(), " |".to_string()].concat())
                .collect(),
        ]
        .concat();
        println!("{v_edge}");
        println!("{header}");
        for hm in self.get_var_iter() {
            println!("{v_sep}");
            let mut interpretation: Vec<bool> = vec![];
            for i in &vars {
                interpretation.push(*hm.get(&i.clone()).unwrap());
            }
            interpretation.push(self.swap(&hm).evaluate().unwrap());
            let translate_bool = |x| -> String {
                if x {
                    return "T".to_string();
                } "F".to_string()
            };
            let header: String = [
                "|".to_string(),
                interpretation
                    .iter()
                    .map(|x| {
                        [
                            " ".to_string(),
                            translate_bool(*x).clone(),
                            " |".to_string(),
                        ]
                        .concat()
                    })
                    .collect(),
            ]
            .concat();
            println!("{header}");
        }
        println!("{v_edge}");
    }
}
// TODO: find difference between .iter() and .into_iter()
impl Hash for Prop {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Prop::*;
        use PropUntitled as PU;
        match self {
            Atom(b) => {
                PU::Atom.hash(state);
                b.hash(state)
            }
            Var(s) => {
                PU::Var.hash(state);
                s.hash(state)
            }

            Scope(bp) => {
                PU::Scope.hash(state);
                (*bp).hash(state)
            }
            Not(bp) => {
                PU::Not.hash(state);
                (*bp).hash(state)
            }

            Conj(vp) => {
                PU::Conj.hash(state);
                let mut vpc = (*vp).clone();
                vpc.sort();
                vpc.hash(state)
            }
            Disj(vp) => {
                PU::Disj.hash(state);
                let mut vpc = (*vp).clone();
                vpc.sort();
                vpc.hash(state)
            }
            Biimpl(vp) => {
                PU::Biimpl.hash(state);
                let mut vpc = (*vp).clone();
                vpc.sort();
                vpc.hash(state)
            }
            Xor(vp) => {
                PU::Xor.hash(state);
                let mut vpc = (*vp).clone();
                vpc.sort();
                vpc.hash(state)
            }
            LogEqu(vp) => {
                PU::LogEqu.hash(state);
                let mut vpc = (*vp).clone();
                vpc.sort();
                vpc.hash(state)
            }

            Impl(bp2) => {
                PU::Impl.hash(state);
                (*bp2).hash(state)
            }
        }
    }
}

impl fmt::Display for Prop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn impl_box_p(bp: Box<Prop>) -> String {
            impl_p(*bp)
        }
        /// returns the reversed precedence of an operator by delimiter
        fn d2v(delimiter: &str) -> u8 {
            match delimiter {
                "¬" => 1,
                "∧" => 2,
                "∨" => 3,
                "⊕" => 4,
                "→" => 5,
                "↔" => 6,
                "≡" => 7,
                _ => u8::MAX,
            }
        }
        /// returns the reversed precedence of an operator by prop
        fn p2v(p: Prop) -> u8 {
            use Prop::*;
            match p {
                Atom(_) => 0,
                Var(_) => 0,
                Not(_) => 1,
                Conj(_) => 2,
                Disj(_) => 3,
                Xor(_) => 4,
                Impl(_) => 5,
                Biimpl(_) => 6,
                LogEqu(_) => 7,
                _ => u8::MAX,
            }
        }
        fn impl_box_pv_d(pv: Vec<Prop>, delimiter: &str) -> String {
            let mut s = String::new();
            for (i, p) in (&pv).into_iter().enumerate() {
                if p2v(p.clone()) >= d2v(delimiter) {
                    s.push('(');
                }
                s.push_str(impl_p(p.clone()).as_str());
                if p2v(p.clone()) >= d2v(delimiter) {
                    s.push(')');
                }
                if i + 1 != pv.len() {
                    s.push_str(delimiter);
                }
            }
            s
        }
        fn impl_p(p: Prop) -> String {
            use Prop::*;
            match p {
                Atom(true) => String::from("T"),
                Atom(false) => String::from("F"),
                Var(s) => s,
                Scope(inner) => String::from(format!("({})", impl_box_p(inner))),
                Not(inner) => match *inner {
                    Atom(_) => String::from(format!("¬{}", impl_box_p(inner))),
                    Var(_) => String::from(format!("¬{}", impl_box_p(inner))),
                    Scope(_) => String::from(format!("¬{}", impl_box_p(inner))),
                    _ => String::from(format!("¬({})", impl_box_p(inner))),
                },

                Conj(pv) => impl_box_pv_d(pv, "∧"),
                Disj(pv) => impl_box_pv_d(pv, "∨"),
                Xor(pv) => impl_box_pv_d(pv, "⊕"),
                Biimpl(pv) => impl_box_pv_d(pv, "↔"),
                LogEqu(pv) => impl_box_pv_d(pv, "≡"),

                Impl([p1, p2]) => impl_box_pv_d(vec![*p1, *p2], "→"),
                // _ => String::from("_")
            }
        }
        write!(f, "{}", impl_p(self.clone()))
    }
}
