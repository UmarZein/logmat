use crate::prop::*;
use std::{hash::{Hash,Hasher}, ops::Deref};
fn b(p: Prop) -> Box<Prop>{
    Box::<Prop>::new(p)
}

/// apply logical rules. Each rule which is applied is put in a (result, rule_name) in a vec. The 
pub fn apply_rules<H>(target: &Prop, hashes: &Vec<u64>, hasher: H)
    -> Vec<(Prop, String, u64)>
    where H: Hasher + Clone{
    
    
    let hash = |input: &Prop| -> u64{
        let mut copied_hasher = hasher.clone();
        input.hash(&mut copied_hasher);
        return copied_hasher.finish();
    };
    
    let mut applied_results: Vec<(Prop, String, u64)> = vec![];
    
    let mut push_if_new = |p: Prop,s:&str|{
        let h = hash(&p);
        if !hashes.contains(&h){
            applied_results.push((p.clone(),s.to_owned(),h));
        }
    };
    
    use Prop::*; 
    match target{
        Not(bx) => {
            match bx.deref(){
                Not(b2) => {
                    let h = hash(b2.deref());
                    if !hashes.contains(&h){
                        applied_results.push((b2.deref().clone(),String::from("double negation law"),hash(b2.deref())))
                    }


                },
                // ¬(p∧q∧r∧s)
                Conj(l) => {
                    // assumption: l.len() > 1
                    let mut new: Vec<Prop> = vec![];
                    // all => ¬p∨¬q∨¬r∨¬s
                    for p in l{
                        new.push(Not(b(p.clone())))
                    }
                    // 2..all-1 => ¬p∨¬q∨¬(r∧s) ... ¬p∨¬(q∧r∧s)
                    let mut buffer: Vec<usize> = vec![0];
                    for i in 2..l.len(){
                        while buffer.len() > i{
                            for j in (buffer[buffer.len()-1]+1)..l.len()-buffer.len(){
                                todo!();
                            }
                        }
                    }
                    push_if_new(Disj(new),"de morgan's law"); 
                }
                _ => ()
            };
        },
        
        Conj(x) => (),
        Disj(x) => (),
        Xor(x) => (),
        Biimpl(x) => (),
        LogEqu(x) => (),
        
        Then(xy) => (),
        Cause(xy) => (),
        
        _ => (),
    }



    return applied_results;
}
