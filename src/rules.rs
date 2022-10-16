use crate::prop::*;
use crate::juggler::*;
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
                    let mut all: Vec<(Prop, &str)> = vec![];
                    
                    let mut new: Vec<Prop> = vec![];
                    // all => ¬p∨¬q∨¬r∨¬s
                    for p in l{
                        new.push(Not(b(p.clone())))
                    }
                    
                    all.push((Disj(new), "de morgan's law"));

                    // 2..all-1 => ¬p∨¬q∨¬(r∧s) ... ¬p∨¬(q∧r∧s)
                    for i in 2..l.len(){
                        let j = Juggler::new(i as u64, l.len() as u64);
                        let mut buffer_disj: Vec<Prop> = vec![];
                        let mut buffer_conj: Vec<Prop> = vec![];
                        for state in j{
                            buffer_disj.clear();
                            buffer_conj.clear();
                            let mut k = 0;
                            for x in state{
                                if x{
                                    buffer_conj.push(l[k].clone());
                                } else {
                                    buffer_disj.push(Not(b(l[k].clone())));
                                }
                                k += 1;
                            }
                            all.push(
                                (Disj
                                    ([vec![
                                        Not(
                                            b(
                                                Conj(
                                                    buffer_conj.clone()
                                                )
                                            )
                                        )],
                                    buffer_disj.clone()
                                    ].concat()), 
                                "de morgan's law")
                            );
                        }
                    }
                    for (p, s) in all{
                        push_if_new(p, s);
                    }
                    //push_if_new(Disj(new),"de morgan's law"); 
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
