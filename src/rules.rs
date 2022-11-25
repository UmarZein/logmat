//! simplification rules
use crate::prop::*;
use crate::juggler::*;
use std::collections::HashMap;
use std::ops::Deref;
// TODO: add rule: p|p&q = p
use crate::qol_macros::*;

fn b(p: Prop) -> Box<Prop>{
    Box::<Prop>::new(p)
}

/// apply logical rules. 
/// Each rule which is applied is put in a (result, rule_name) in a vec. The 
/// may return multiple equivalent values

pub fn all_simplifications(target: &Prop) -> Vec<Prop> {
    let mut res = HashMap::<Prop,bool>::new();
    res.insert(target.clone(), false);
    let mut done = false;
    while !done{
        // println!("{}","-".repeat(1000));
        done = true;
        let mut res_keys: Vec<Prop> = res.keys().map(|x|x.clone()).collect();
        res_keys.sort_by(|a,b|a.complexity().cmp(&b.complexity())/*.reverse()*/);
        //println!("res_keys = {:?}",res_keys.iter().map(|x|x.complexity()).collect::<Vec<u64>>());
        for p_done in res_keys{
            if res.get(&p_done).unwrap()==&false{
                // println!("{p_done} -> {}",p_done.complexity());
                for (p, s) in apply_rules_raw(&p_done.clone()){
                    if !res.contains_key(&p){
                        res.insert(p.clone(), false);
                        if p.complexity() <= 2{break}
                        let len = res.len();
                        // println!("before: {p_done}");
                        // println!("{p}");
                        // println!("reason = {s}");
                        done = false;
                        // println!("res[{}] = {{",len);
                        // for i in res.keys(){
                        //     println!("\t{i},")
                        // }
                        // println!("}}")
                    }
                }
                *res.get_mut(&p_done).unwrap()=true;
            }
        }
    }
    res.keys().map(|x|x.clone()).collect()
}


pub fn apply_rules_raw(target: &Prop) -> Vec<(Prop, String)> {
    
    let mut applied_results: Vec<(Prop, String)> = vec![];

    let mut submit = |p: Prop,s:&str|{
        applied_results.push((p.clone(),s.to_owned()));
    };
    use Prop::*; 
    match target{
        Not(bx) => {
            match bx.deref(){
                Atom(b) => {
                    submit(Atom(!b),"negation evaluation");
                }, 
                Not(b2) => {
                    submit(b2.deref().clone(), "double negation law");

                },
                // ¬(p∧q∧r∧s)
                Conj(l) => {
                    // assumption: l.len() > 1
                    let mut new: Vec<Prop> = vec![];
                    // all => ¬p∨¬q∨¬r∨¬s
                    for p in l{
                        new.push(Not(b(p.clone())))
                    }
                    
                    submit(Disj(new), "de morgan's law");

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
                            submit(
                                Disj(
                                    [vec![
                                        Not(
                                            b(
                                                Conj(
                                                    buffer_conj.clone()
                                                )
                                            )
                                        )],
                                    buffer_disj.clone()
                                    ].concat()), 
                                "de morgan's law"
                            );
                        }
                    }
                },
                Disj(l) => {
                    // assumption: l.len() > 1
                    let mut new: Vec<Prop> = vec![];
                    // all => ¬p∧¬q∧¬r∧¬s
                    for p in l{
                        new.push(Not(b(p.clone())))
                    }
                    
                    submit(Conj(new), "de morgan's law");

                    // 2..all-1 => ¬p∧¬q∧¬(r∨s) ... ¬p∧¬(q∨r∨s)
                    for i in 2..l.len(){
                        let j = Juggler::new(i as u64, l.len() as u64);
                        let mut buffer_conj: Vec<Prop> = vec![];
                        let mut buffer_disj: Vec<Prop> = vec![];
                        for state in j{
                            buffer_conj.clear();
                            buffer_disj.clear();
                            let mut k = 0;
                            for x in state{
                                if x{
                                    buffer_disj.push(l[k].clone());
                                } else {
                                    buffer_conj.push(Not(b(l[k].clone())));
                                }
                                k += 1;
                            }
                            submit(
                                Conj
                                    ([vec![
                                        Not(
                                            b(
                                                Disj(
                                                    buffer_disj.clone()
                                                )
                                            )
                                        )],
                                    buffer_conj.clone()
                                    ].concat()), 
                                "de morgan's law"
                            );
                        }
                    }
                    //push(Disj(new),"de morgan's law"); 
                },
                _ => ()
            };
            let vps = apply_rules_raw(&bx.deref().clone());
            for (p, s) in vps{
                //println!("p = {p:?}");
                submit(Not(b(p)), s.as_str());
            }
        },

        ////////////////////////// end of Not(_) /////////////////////////////// 
        
        Conj(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "conjunction single unwrap")
            };

            // Conj([..., Conj(A...), ...]) -> Conj([..., A..., ...])
            let mut unwrapped: Vec<Prop> = vec![];
            let mut has_unwrapped = false;
            let mut atomic_propositions: Vec<Prop> = vec![];
            let mut non_atomic_propositions: Vec<Prop> = vec![];
            for i in x{
                match i{
                    Conj(y) => {
                        let cloned = unwrapped.clone();
                        unwrapped = [cloned, y.clone()].concat();
                        has_unwrapped = true;
                        non_atomic_propositions.push(Conj(y.clone()));
                    }
                    _ => {
                        unwrapped.push(i.clone());
                        
                        match i{
                            Atom(bool_val) => {
                                if !bool_val{
                                    submit(F,"conjunction domination law")
                                }
                                atomic_propositions.push(i.clone())
                            },
                            _ => {
                                non_atomic_propositions.push(i.clone())
                            }
                        }
                    }
                }
            }
            // p&T = p 
            // p&F = F 
            if atomic_propositions.len()>0 {
                let evaluated = Atom(Conj(atomic_propositions).evaluate().unwrap());
                if evaluated == Atom(false){
                    submit(F,"conjunction evaluation");
                } else {
                    if non_atomic_propositions.len()>0{
                        submit(Conj([non_atomic_propositions].concat()),"conjunction evaluation");
                    } else {
                        submit(T,"conjunction evaluation");
                    }
                }
            }
            if has_unwrapped{
                submit(Conj(unwrapped), "conjunction associative law (unwrap)");
            }

            let mut all_different: Vec<Prop> = vec![];

            for (i,p) in x.clone().iter().enumerate(){
                let mut other_children: Vec<Prop> = x.clone();
                other_children.remove(i);
                for (p, s) in apply_rules_raw(p){
                    let mut complete_with_processed_children = other_children.clone();
                    complete_with_processed_children.push(p);
                    submit(Conj(complete_with_processed_children), s.as_str());
                }
                // p&~p&:: = f 
                for q in x.clone(){
                    if p.is_logically_opp(&q).unwrap(){
                        submit(F, "conjunction negation law")
                    } 
                }
                // remove equivalents, leave only uniques
                let mut already_contains = false;
                for q in all_different.clone(){
                    if p.is_structurally_eq(&q){
                        already_contains = true;
                        break
                    }
                }
                if !already_contains{
                    all_different.push(p.clone());  
                }
            }
            all_different.sort();
            let sorted_x = {let mut tmp = x.clone(); tmp.sort(); tmp};
            if (all_different.len()>0) && (all_different!=sorted_x){
                submit(Conj(all_different), "conjunction negation law? (p&p <=> p)");       
            }

            // Conj(x,y,z) = Not(Disj([Not(x),Not(y),Not(z)]))
            // WARNING: do not uncomment. it will recurse indefinitely
            // submit(n!(Disj(x.iter().map(|c|n!(c.clone())).collect::<Vec<Prop>>())),"de morgan");

            // p∧(q∨r)≡(p∧q)∨(p∧r)
            
            // p∧(p∨q)≡p

            // p∧p∧:::≡p∧:::
        },
        Disj(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "single unwrap")
            };
            // 1. Conj([..., Conj(A...), ...]) -> Conj([..., A..., ...])
            let mut unwrapped: Vec<Prop> = vec![];
            let mut has_unwrapped = false;
            let mut atomic_propositions: Vec<Prop> = vec![];
            let mut non_atomic_propositions: Vec<Prop> = vec![];
            for i in x{
                match i{
                    Disj(y) => {
                        let cloned = unwrapped.clone();
                        unwrapped = [cloned, y.clone()].concat();
                        has_unwrapped = true;
                        non_atomic_propositions.push(Disj(y.clone()));
                    }
                    _ => {
                        unwrapped.push(i.clone());
                        
                        match i{
                            Atom(bool_val) => {
                                if *bool_val{
                                    submit(T,"disjunction domination law")
                                }
                                atomic_propositions.push(i.clone())
                            },
                            _ => {
                                non_atomic_propositions.push(i.clone())
                            }
                        }
                    }
                }
            }
            // p|T = T 
            // p|F = p 
            if atomic_propositions.len()>0 {
                let evaluated = Atom(Disj(atomic_propositions).evaluate().unwrap());
                if evaluated == Atom(true){
                    submit(T, "disjunction evaluation");
                } else {
                    if non_atomic_propositions.len()>0{
                        submit(Disj([non_atomic_propositions].concat()),"disjunction evaluation");
                    } else {
                        submit(F, "disjunction evaluation");
                    }
                }
            }


            if has_unwrapped{
                submit(Disj(unwrapped), "disjunction associative law (unwrap)");
            }
            // END 1.
            
            let mut all_different: Vec<Prop> = vec![];

            // Conj([:::])=Conj(simplifiy[:::])
            for (i,p) in x.clone().iter().enumerate(){
                let mut other_children: Vec<Prop> = x.clone();
                other_children.remove(i);
                for (p, s) in apply_rules_raw(p){
                    let mut complete_with_processed_children = other_children.clone();
                    complete_with_processed_children.push(p);
                    submit(Disj(complete_with_processed_children), s.as_str());
                }
                // p|~p&:: = t 
                for q in x.clone(){
                    if p.is_logically_opp(&q).unwrap(){
                        submit(T, "disjunction negation law")
                    }
                }
                
                let mut already_contains = false;
                for q in all_different.clone(){
                    if p.is_structurally_eq(&q){
                        already_contains = true;
                        break
                    }
                }
                if !already_contains{
                    all_different.push(p.clone());  
                }
            }
            all_different.sort();
            let sorted_x = {let mut tmp = x.clone(); tmp.sort(); tmp};
            if (all_different.len()>0) && all_different!=sorted_x{
                submit(Disj(all_different), "disjunction removed duplicates (p|p <=> p)");       
            }

            // WARNING: do not uncomment. it will recurse indefinitely 
            // submit(n!(Conj(x.iter().map(|c|n!(c.clone())).collect::<Vec<Prop>>())),"de morgan");

        },
        Xor(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "single unwrap")
            };
            let mut new_x: Vec<Prop> = vec![];
            let mut has_done_elimination = false;
            for i in x{
                let new_x_clone = new_x.clone();
                let mut has_opposite = false;
                let mut j: usize = 0;
                while j<new_x_clone.len(){
                    if new_x[j].is_logically_eq(i).unwrap(){
                        new_x.remove(j);
                        has_opposite = true;
                        has_done_elimination = true;
                        j += 1;
                    } else if new_x[j].is_logically_opp(i).unwrap(){
                        new_x.remove(j);
                        new_x.push(T);
                    }
                    j+= 1;
                }
                if !has_opposite{
                    new_x.push(i.clone());
                }
            }
            let mut x = x;
            if new_x.len()>0 && has_done_elimination{
                println!("XOR elimination => {}",Xor(new_x.clone()));
                let tmp = Xor(new_x.clone());
                x = &new_x;
                submit(tmp,"XOR elimination");
            }
            // F 
            // T 
            // T 
            // F 
            // (p|q)&(~p|~q)
            // if x.len() == 2{
            //     let p = x[0].clone();
            //     let q = x[1].clone();
            //     submit(conj!(disj!(p.clone(),q.clone()),disj!(n!(p),n!(q))),"xor simplification");
            // }
            
            if x.len()>=2 {
                let mut res: Prop;
                let mut new_x = x.clone();
                for i in 0..(new_x.len()-1){
                    for j in (i+1)..new_x.len(){
                        let p = new_x.remove(j);
                        let q = new_x.remove(i);
                        
                        res = conj!(disj!(p.clone(),q.clone()),disj!(n!(p),n!(q)));
                        new_x.push(res.clone());
                        submit(Xor(new_x.clone()), "xor simplification");

                        new_x = x.clone()
                    }
                    // {
                    //     let p = new_x.remove(i);
                    //     let q = new_x.remove(i);
                    //     res = conj!(disj!(p.clone(),q.clone()),disj!(n!(p),n!(q)));
                    // };
                    // for _ in 0..x.len()-2{
                    //     let p = new_x.pop().unwrap();
                    //     res = conj!(disj!(p.clone(),res.clone()),disj!(n!(p),n!(res)));
                    // }
                    // // println!("res = {res}");
                    // submit(res, "xor simplification")
                }
            }
            // let mut unwrapped: Vec<Prop> = vec![];
            // let mut has_unwrapped = false;
            // for i in x{
            //     match i{
            //         Xor(y) => {
            //             let cloned = unwrapped.clone();
            //             unwrapped = [cloned, y.clone()].concat();
            //             has_unwrapped = true;
            //         }
            //         _ => unwrapped.push(i.clone())
            //     }
            // }
            // if has_unwrapped{
            //     submit(Biimpl(unwrapped), "associative law (unwrap)");
            // }
            // // END 1.
            // // Xor([:::])=Xor(simplifiy[:::])
            // for (i,p) in x.clone().iter().enumerate(){
            //     let mut other_children: Vec<Prop> = x.clone();
            //     other_children.remove(i);
            //     for (p, s) in apply_rules_raw(p){
            //         let mut complete_with_processed_children = other_children.clone();
            //         complete_with_processed_children.push(p);
            //         submit(Xor(complete_with_processed_children), s.as_str());
            //     }
            // }
        },
        Biimpl(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "single unwrap")
            };
            // T 
            // F 
            // F 
            // T 
            // (p&q)|(~p&~q)
            //
            if x.len()>=2 {
                let mut res: Prop;
                let mut new_x = x.clone();
                {
                    let p = new_x.pop().unwrap();
                    let q = new_x.pop().unwrap();
                    res = disj!(conj!(p.clone(),q.clone()),conj!(n!(p),n!(q)));
                };
                for _ in 0..x.len()-2{
                    let p = new_x.pop().unwrap();
                    res = disj!(conj!(p.clone(),res.clone()),conj!(n!(p),n!(res)));
                }
                // println!("res = {res}");
                submit(res, "xor simplification")
            }
            // let mut unwrapped: Vec<Prop> = vec![];
            // let mut has_unwrapped = false;
            // for i in x{
            //     match i{
            //         Biimpl(y) => {
            //             let cloned = unwrapped.clone();
            //             unwrapped = [cloned, y.clone()].concat();
            //             has_unwrapped = true;
            //         }
            //         _ => unwrapped.push(i.clone())
            //     }
            // }
            // if has_unwrapped{
            //     submit(Biimpl(unwrapped), "associative law (unwrap)");
            // }
            // // END 1.
            // // Xor([:::])=Xor(simplifiy[:::])
            // for (i,p) in x.clone().iter().enumerate(){
            //     let mut other_children: Vec<Prop> = x.clone();
            //     other_children.remove(i);
            //     for (p, s) in apply_rules_raw(p){
            //         let mut complete_with_processed_children = other_children.clone();
            //         complete_with_processed_children.push(p);
            //         submit(Biimpl(complete_with_processed_children), s.as_str());
            //     }
            // }
        },
        LogEqu(x) => (),
        
        Impl([x,y]) => {
            // p→q = ¬p∨q
            let x_clone = (*x).deref().clone();
            let y_clone = (*y).deref().clone();
            submit(disj!(n!(x_clone.clone()), y_clone.clone()), "p→q into ¬p∨q...\"implication explansion\"?");
            
            for (p, s) in apply_rules_raw(&x_clone){
                submit(imply!(p,y_clone.clone()),s.as_str());
            }
            
            for (p, s) in apply_rules_raw(&y_clone){
                submit(imply!(x_clone.clone(),p),s.as_str());
            }
        },
        
        _ => (),
    }



    return applied_results;
}
