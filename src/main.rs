// #![allow(warnings)]
mod parser;
mod collapse_iterator;
mod juggler;
mod num_traits;
mod prop;
mod qol_macros;
mod rules;
mod var_iter;

use std::{str::FromStr, fmt::Debug};

#[allow(dead_code)]
//use qol_macros::*;
// use crate::rules::*;
use prop::Prop::{self, *};

use crate::rules::all_simplifications;


pub fn input<T>() -> T where T:FromStr, <T as FromStr>::Err: Debug{
    let mut s: String = "".into();
    std::io::stdin().read_line(&mut s).unwrap();
    s.trim().parse::<T>().unwrap()
}


fn main() {
    // a|b|c|(x&y&z)
    //let x = disj!(v!("a"), v!("b"), v!("c"), conj!(v!("x"), v!("y"), v!("z")));
    let j = juggler::Juggler::new(2 , 4 );
    for i in j{
        juggler::Juggler::print_from_vec(&i.state(), "state") 
    }
    let x = imply!(v!("a"),v!("b"));
    println!("y={x}");

    // // (a|b|c|x)&(a|b|c|y)&(a|b|c|z)
    // let y = conj!(
    //     disj!(v!("a"), v!("b"), v!("c"), v!("x")),
    //     disj!(v!("a"), v!("b"), v!("c"), v!("y")),
    //     disj!(v!("a"), v!("b"), v!("c"), v!("z"))
    // );
    // println!("y={y}");
    // println!("x==y = {}", x.is_logically_eq(&y).unwrap());
    // println!("{}", " == ".to_string().repeat(30));
    let x =parser::parse(&input::<String>()).unwrap();
    println!("{x}");
    println!("{}",x.truth_table());
    //                    let x = xor!(v!("p"), v!("q"), n!(v!("p")));
    //                    let mut z = n!(n!(n!(n!(n!(n!(n!(v!("a"))))))));
    //                    let x = xor!(n!(xor!(v!("a"), v!("b"))), disj!(v!("b"), n!(v!("c"))));
    //                    let y = xor!(v!("a"), v!("b"), conj!(v!("b"), n!(v!("c"))));
    //                    let x = imply!(v!("p"), imply!(v!("q"), v!("r")));
    //                    let y = disj!(conj!(v!("p"), n!(v!("q"))), disj!(n!(v!("p")), v!("r")));

    //                    //let x=conj!(disj!(v!("p"),v!("q")),v!("p"));
    //                    //let x= xor!(n!(xor!(v!("a"),v!("b"))),disj!(v!("b"),n!(v!("c"))));
    //                    println!("x={x}");
    //                    println!("y={y}");
    //                    println!("{}", x.is_logically_eq(&y).unwrap());
    //                    // for i in all_simplifications(&x) {
    //                    //     //println!("{i}");

    //                    //     if !(i.is_logically_eq(&x.clone()).unwrap()){
    //                    //         println!("i = {i}");
    //                    //         println!("x = {x}");
    //                    //         panic!();
    //                    //     }
    //                    //     println!("i={i}");
    //                    //     if i.complexity()<z.complexity(){
    //                    //         z = i
    //                    //     }
    //                    // }
    //                    // let y = conj!(
    //                    //     disj!(v!("p"), v!("q"), v!("r")),
    //                    //     disj!(n!(v!("p")),n!(v!("q")),n!(v!("r")))
    //                    // );
    //                    //println!("{}",x.is_logically_eq(&y).unwrap());
    //                    let x = disj!(n!(v!("p")), conj!(v!("p"), n!(v!("q"))));
    //                    x.print_truth_table();
    //                    // println!("z = {z}");
    //                    // z.print_truth_table();
    //                    // xor!(v!("p"), v!("q"), v!("r"),v!("s")).print_truth_table();
}
