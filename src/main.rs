mod prop;
mod var_iter;
mod rules;
use std::{collections::hash_map::*, hash::*};
use prop::*;

use crate::rules::apply_rules;
 
// prop_tools.rs
// TODO: these should be macros
pub fn b(p: Prop) -> Box<Prop>{
    Box::<Prop>::new(p)
}

pub fn atom(b:bool)->Prop{
    Prop::Atom(b)
}
pub fn var(s:&str)->Prop{
    Prop::Var(s.to_owned())
}
pub fn scope(bp: Prop)->Prop{
    Prop::Scope(b(bp))
}
pub fn not(bp: Prop)->Prop{
    Prop::Not(b(bp))
}

pub fn conj(bp1: Prop, bp2: Prop)->Prop{
    Prop::Conj(vec![bp1,bp2])
}
pub fn disj(bp1: Prop, bp2: Prop)->Prop{
    Prop::Disj(vec![bp1,bp2])
}
pub fn xor(bp1: Prop, bp2: Prop)->Prop{
    Prop::Xor(vec![bp1,bp2])
}
pub fn biimpl(bp1: Prop, bp2: Prop)->Prop{
    Prop::Biimpl(vec![bp1,bp2])
}

pub fn then(bp1: Prop, bp2: Prop)->Prop{
    Prop::Then([b(bp1),b(bp2)])
}
pub fn cause(bp1: Prop, bp2: Prop)->Prop{
    Prop::Cause([b(bp1),b(bp2)])
}


#[allow(dead_code)]
const T: bool = true;
#[allow(dead_code)]
const F: bool = false;

fn main() {
    let bp = |x: Prop|Box::<Prop>::new(x);
    let a = Prop::Disj(vec![
        var("a"),
        atom(T),
        var("c"),
    ]);
    let b = Prop::Disj(vec![
        atom(T),
        var("a"),
        var("c"),
    ]);
    use Prop::*;
    let c = Not(
        Box::<Prop>::new(
            Conj(vec![
                var("p"),
                var("q"),
                var("r"),
                var("s"),
            ])
        )
    );
    let c2 = Disj(vec![
        Not(bp(var("p"))),
        Not(bp(var("q"))),
        Not(bp(var("r"))),
        Not(bp(var("s"))),
    ]);
    let c3 = Disj(vec![
        Not(bp(var("p"))),
        Not(bp(var("q"))),
        Not(bp(Conj(vec![
            var("r"),
            var("s")
        ])))
    ]);
    let c4 = Disj(vec![
        Not(bp(var("p"))),
        Not(bp(Conj(vec![
            var("q"),
            var("r"),
            var("s")
        ])))
    ]);
    let c5 = Disj(vec![
        Not(bp(var("p"))),
        Not(bp(var("r"))),
        Not(bp(Conj(vec![
            var("q"),
            var("s")
        ])))
    ]);
    

    println!("before = {c}");
    let res =apply_rules(&c, &vec![], DefaultHasher::default()); 
    for (x, _, _) in res{
        println!("applied rules = {x}");
    }
    println!("c≡c2 = {:?}",c.is_logically_eq(&c2).unwrap());
    println!("c≡c3 = {:?}",c.is_logically_eq(&c3).unwrap());
    println!("c2≡c3 = {:?}",c2.is_logically_eq(&c3).unwrap());
    println!("c2≡c4 = {:?}",c2.is_logically_eq(&c4).unwrap());
    println!("c≡c5 = {:?}",c.is_logically_eq(&c5).unwrap());
    println!("c={c}");
    println!("c2={c2}");
    println!("c3={c3}");
    println!("c4={c4}");
    println!("c5={c5}");
}

