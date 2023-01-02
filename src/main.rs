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

fn foo(){
    1==2;
}

pub fn input<T>() -> T where T:FromStr, <T as FromStr>::Err: Debug{
    let mut s: String = "".into();
    std::io::stdin().read_line(&mut s).unwrap();
    s.trim().parse::<T>().unwrap()
}


fn main() {
    let x =parser::parse(&input::<String>()).unwrap();
    println!("{x}");
    println!("{}",x.truth_table());
    println!("z={}",x.simplify());
}
