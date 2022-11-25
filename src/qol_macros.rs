use crate::Prop::{self, *};

#[allow(dead_code)]
pub(crate) const T: Prop = Atom(true);
#[allow(dead_code)]
pub(crate) const F: Prop = Atom(false);

#[macro_export]
macro_rules! v {
    ($name: expr) => {
        Var($name.to_string())
    };
}

#[macro_export]
macro_rules! n {
    ($child: expr) => {
        Prop::Not(Box::<Prop>::new($child))
    };
}

#[macro_export]
macro_rules! conj {
    ($( $child: expr ),*) => {{
        let mut children: Vec<Prop> = vec![];
        $( children.push($child); )*
        Conj(children)
    }};
}

#[macro_export]
macro_rules! disj {
    ($( $child: expr ),*) => {{
        let mut children: Vec<Prop> = vec![];
        $( children.push($child); )*
        Disj(children)
    }};
}

#[macro_export]
macro_rules! biimpl {
    ($( $child: expr ),*) => {{
        let mut children: Vec<Prop> = vec![];
        $( children.push($child); )*
        Biimpl(children)
    }};
}

#[macro_export]
macro_rules! xor {
    ($( $child: expr ),*) => {{
        let mut children: Vec<Prop> = vec![];
        $( children.push($child); )*
        Xor(children)
    }};
}

#[macro_export]
macro_rules! logequ {
    ($( $child: expr ),*) => {{
        let mut children: Vec<Prop> = vec![];
        $( children.push($child); )*
        LogEqu(children)
    }};
}

#[macro_export]
macro_rules! imply {
    ($cause: expr, $effect: expr) => {
        Impl([Box::<Prop>::new($cause), Box::<Prop>::new($effect)])
    };
}
#[allow(unused_imports)]
pub(crate) use {v,n,conj,disj,xor,biimpl,logequ,imply};
