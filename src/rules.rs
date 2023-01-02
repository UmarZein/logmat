//! simplification rules
use crate::prop::*;
use crate::juggler::*;
use std::collections::HashMap;
use std::ops::Deref;
use std::sync::Arc;
use std::sync::Mutex;
// TODO: add rule: p|p&q = p
use crate::qol_macros::*;

fn b(p: Prop) -> Box<Prop>{
    Box::<Prop>::new(p)
}

/// thread-safe hashmap cache
pub type TCache<K,V> = Arc<Mutex<HashMap<K,V>>>;

/// simplifier cache
pub type SCache = TCache<Prop, Vec<(Prop, String)>>;

/// apply logical rules. 
/// Each rule which is applied is put in a (result, rule_name) in a vec. The 
/// may return multiple equivalent values

pub fn all_simplifications(target: &Prop, recurse_absorption: bool, cache: SCache) -> Vec<Prop> {
    let mut res = HashMap::<Prop,bool>::new();
    //let cache = Arc::new(Mutex::new(HashMap::<Prop,Vec<(Prop, String)>>::new()));
    res.insert(target.clone(), false);
    let mut done = false;
    while !done{
        done = true;
        let mut res_keys: Vec<Prop> = res.keys().map(|x|x.clone()).collect();
        res_keys.sort_by(|a,b|a.complexity().cmp(&b.complexity())/*.reverse()*/);
        for p_done in res_keys{
            if res.get(&p_done).unwrap()==&false{
                for (p, _) in apply_rules_raw(&p_done.clone(), cache.clone(), recurse_absorption){
                    if !res.contains_key(&p){
                        res.insert(p.clone(), false);
                        if p.complexity() <= 1{break}
                        done = false;
                    }
                }
                *res.get_mut(&p_done).unwrap()=true;
            }
        }
    }
    if false{
        println!("-----------------------------------");
        let cache = cache.lock().unwrap();
        for (k,v) in cache.iter(){
            print!("{k} => [");
            for (i,x) in v.iter().enumerate(){
                if i>0{
                    print!(", ")
                }
                print!("{}",x.0)
            }
            println!("]")
        }
        println!("-----------------------------------");
    }
    res.keys().map(|x|x.clone()).collect()
}

const USE_CACHE: bool = true;
const MIN_COMPLEXITY: u64 = 10;

pub fn apply_rules_raw(target: &Prop, cache: SCache, recurse_absorption: bool) -> Vec<(Prop, String)> {
    if target.complexity()>=MIN_COMPLEXITY&&USE_CACHE{
        let read = cache.lock().unwrap();
        if let Some(ret)= read.get(target){
            if ret.len()==0{
                return vec![]
            }
            let first = ret[0].clone();
            let mut simplest: ((Prop, String),u64) = (first.clone(),first.0.complexity());
            ret.iter().for_each(|x|{
                let new_compl = x.0.complexity();
                if new_compl < simplest.1{
                    simplest = (x.clone(),new_compl)
                }
            });
            if false{
                println!("used cache on {target}");
            }
            return vec![simplest.0];
        }
    }
    
    //println!("---applying rules to {target}---");
    let mut applied_results: Vec<(Prop, String)> = vec![];

    let mut submit = |p: Prop,s:&str|{
        //println!("{s}");
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
                            for (i, x) in state.enumerate(){
                                if x{
                                    buffer_conj.push(l[i].clone());
                                } else {
                                    buffer_disj.push(n!(l[i].clone()));
                                }
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
                            for (i, x) in state.enumerate(){
                                if x{
                                    buffer_disj.push(l[i].clone());
                                } else {
                                    buffer_conj.push(n!(l[i].clone()));
                                }
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
            let vps = apply_rules_raw(&bx.deref().clone(), cache.clone(), true);
            for (p, s) in vps{
                //println!("p = {p:?}");
                submit(Not(b(p)), s.as_str());
            }
        },

        ////////////////////////// end of Not(_) /////////////////////////////// 
        
        Conj(children) => {
            if children.len() == 1{
                submit(children[0].clone(), &format!("conjunction single unwrap: before = {}",target.clone()));
                
            };

            // Conj([..., Conj(A...), ...]) -> Conj([..., A..., ...])
            let mut unwrapped: Vec<Prop> = vec![];
            let mut has_unwrapped = false;
            let mut atomic_propositions: Vec<Prop> = vec![];
            let mut non_atomic_propositions: Vec<Prop> = vec![];
            for i in children{
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

            for (i,p) in children.clone().iter().enumerate(){
                let mut other_children: Vec<Prop> = children.clone();
                other_children.remove(i);
                for (p, s) in apply_rules_raw(p, cache.clone(), true){
                    let mut complete_with_processed_children = other_children.clone();
                    complete_with_processed_children.push(p);
                    submit(Conj(complete_with_processed_children), s.as_str());
                }
                // p&~p&:: = f 
                for q in children.clone(){
                    if p.is_structurally_opp(&q){
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
            let sorted_children = {let mut tmp = children.clone(); tmp.sort(); tmp};
            let mut idlaw = false;
            if (all_different.len()>0) && (all_different!=sorted_children){
                submit(Conj(all_different), "conjunction idempotent law");       
                idlaw = true;
            }

            // Conj(x,y,z) = Not(Disj([Not(x),Not(y),Not(z)]))
            // WARNING: do not uncomment. it will recurse indefinitely
            // submit(n!(Disj(x.iter().map(|c|n!(c.clone())).collect::<Vec<Prop>>())),"de morgan");

            // p∧(q∨r)≡(p∧q)∨(p∧r)
            
            // p∧(p∨q)≡p
            // (p->q)=>(p&q=p)
            // (conj!(chosen)->conj!(leftover))=>(self=conj!(chosen))
            if !idlaw&&recurse_absorption{
                for i in 1..children.len(){
                    let j = Juggler::new(i as u64, children.len() as u64);
                    let mut chosen: Vec<Prop> = vec![];
                    let mut leftover: Vec<Prop> = vec![];
                    for state in j{
                        chosen.clear();
                        leftover.clear();
                        for (i, x) in state.enumerate(){
                            if x{
                                chosen.push(children[i].clone().simplify_nore_cached(cache.clone()));
                            } else {
                                leftover.push(children[i].clone().simplify_nore_cached(cache.clone()));
                            }
                        }
                        if let Prop::Atom(true) = disj!(
                            n!(
                                Prop::Conj(chosen.clone()).simplify_cached(cache.clone())
                            ).simplify_cached(cache.clone()),
                            Prop::Conj(leftover.clone()).simplify_cached(cache.clone())
                        ).simplify_nore_cached(cache.clone()){
                            submit(Prop::Conj(chosen.clone()), "absorption law on conjunction")
                        }
                    }
                }
            }
            // p∧p∧:::≡p∧:::
        },
        Disj(children) => {
            if children.len() == 1{
                submit(children[0].clone(), &format!("Disj single unwrap. target = {}",target.clone()))
            };
            // 1. Conj([..., Conj(A...), ...]) -> Conj([..., A..., ...])
            let mut unwrapped: Vec<Prop> = vec![];
            let mut has_unwrapped = false;
            let mut atomic_propositions: Vec<Prop> = vec![];
            let mut non_atomic_propositions: Vec<Prop> = vec![];
            for i in children{
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
            for (i,p) in children.clone().iter().enumerate(){
                let mut other_children: Vec<Prop> = children.clone();
                other_children.remove(i);
                for (p, s) in apply_rules_raw(p, cache.clone(), true){
                    let mut complete_with_processed_children = other_children.clone();
                    complete_with_processed_children.push(p);
                    submit(Disj(complete_with_processed_children), s.as_str());
                }
                // p|~p&:: = t 
                for q in children.clone(){
                    if p.is_structurally_opp(&q){
                        submit(T, &format!("disjunction negation law on {}",target.clone()))
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
            let sorted_children = {let mut tmp = children.clone(); tmp.sort(); tmp};
            let mut idlaw = false;
            if (all_different.len()>0) && all_different!=sorted_children{
                submit(Disj(all_different), "disjunction identity laws");       
                idlaw = true;
            }
            
            // WARNING: do not uncomment. it will recurse indefinitely 
            // submit(n!(Conj(x.iter().map(|c|n!(c.clone())).collect::<Vec<Prop>>())),"de morgan");

            // (p->q)=>(p|q=q)
            // (disj!(chosen)->disj!(leftover))=>(self=disj!(leftover))
            if !idlaw&&recurse_absorption{
                for i in 1..children.len(){
                    let j = Juggler::new(i as u64, children.len() as u64);
                    let mut chosen: Vec<Prop> = vec![];
                    let mut leftover: Vec<Prop> = vec![];
                    for state in j{
                        chosen.clear();
                        leftover.clear();
                        for (i, x) in state.enumerate(){
                            if x{
                                chosen.push(children[i].clone().simplify_nore_cached(cache.clone()));
                            } else {
                                leftover.push(children[i].clone().simplify_nore_cached(cache.clone()));
                            }
                        }
                        if let Prop::Atom(true) = disj!(
                            n!(
                                Prop::Disj(chosen.clone()).simplify_cached(cache.clone())
                            ).simplify_cached(cache.clone()), 
                            Prop::Disj(leftover.clone()).simplify_cached(cache.clone())
                        ).simplify_nore_cached(cache.clone()){
                            submit(Prop::Disj(leftover.clone()), "absorption law on disjunction")
                        }
                    }
                }
            }
        },
        Xor(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "xor single unwrap")
            };
            let mut new_x: Vec<Prop> = vec![];
            let mut has_done_elimination = false;
            for i in x{
                let new_x_clone = new_x.clone();
                let mut has_opposite = false;
                let mut j: usize = 0;
                while j<new_x_clone.len(){
                    if new_x[j].is_structurally_eq(i){
                        new_x.remove(j);
                        has_opposite = true;
                        has_done_elimination = true;
                        j += 1;
                    } else if new_x[j].is_structurally_opp(i){
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
                }
            }
        },
        Biimpl(x) => {
            if x.len() == 1{
                submit(x[0].clone(), "Biimpl single unwrap")
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
                submit(res, "biimplication simplification")
            }
        },
        
        Impl([x,y]) => {
            // p→q = ¬p∨q
            let x = (*x).deref().clone();
            let y = (*y).deref().clone();

            if x.is_eq(&y){
                submit(T, "implication T->T");
            } else {
                submit(disj!(n!(x.clone()), y.clone()), "material implication");
            }
            

            // for (p, s) in apply_rules_raw(&x, true){
            //     submit(imply!(p,y.clone()),s.as_str());
            // }
            // 
            // for (p, s) in apply_rules_raw(&y, true){
            //     submit(imply!(x.clone(),p),s.as_str());
            // }
        },
        
        _ => (),
    };


    if target.complexity()>=MIN_COMPLEXITY&&USE_CACHE{
        let mut write = cache.lock().unwrap();
        write.insert(target.clone(), applied_results.clone());
    }
    return applied_results;
}
