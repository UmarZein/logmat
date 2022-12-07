use crate::prop::*;
use crate::qol_macros::*;
// u&(p|q)^-p
#[derive(Debug, Clone)]
pub enum ParseErr {
    Unknown,
    EmptyString,
    TokenNotFound,
    UnpairedBraces,
    TypeError,
    Unimplimented(String),
}

pub fn translate_operator(s: char) -> Result<PropUntitled, ParseErr> {
    use PropUntitled::*;
    match s {
        // pqrs¬∧∨⊕→≡↔
        '¬' => Ok(Not),
        '∨' => Ok(Disj),
        '∧' => Ok(Conj),
        '⊕' => Ok(Xor),
        '→' => Ok(Impl),
        '↔' => Ok(Biimpl),
        c => Err(ParseErr::Unimplimented(
            c.to_string() + " is not implemented for parsing",
        )),
    }
}

pub fn rank(pu: &PropUntitled) -> u32 {
    use PropUntitled::*;
    match pu {
        Atom => 0,
        Not => 1,
        Conj => 2,
        Disj => 3,
        Xor => 4,
        Impl => 5,
        Biimpl => 6,
        _ => 99,
    }
}

pub fn highest_order(vc: &Vec<char>) -> Result<PropUntitled, ParseErr> {
    use PropUntitled::*;
    if vc.len() == 0 {
        return Err(ParseErr::EmptyString);
    }
    let mut scope_depth = 0i32;
    // pqrs¬∧∨⊕→≡↔
    let mut highest_rank = Atom;
    for &c in vc.iter() {
        if c == '(' {
            scope_depth += 1;
            continue;
        } else if c == ')' {
            scope_depth -= 1;
            continue;
        }
        if scope_depth < 0 {
            return Err(ParseErr::UnpairedBraces);
        }
        if scope_depth != 0 {
            continue;
        }
        if c.is_alphabetic() {
            continue;
        }
        let op = translate_operator(c)?;
        let opr = rank(&op);
        if rank(&highest_rank) < opr {
            highest_rank = op
        }
        highest_rank = highest_rank.max(op)
    }
    Ok(highest_rank)
}
// p&(p|q)
// p->q->r

pub fn _first_layer(text: &str) -> Result<String, ParseErr> {
    let mut layer = 0i32;
    let text: Vec<char> = text.chars().collect();
    let mut ret: Vec<char> = vec![];
    for i in 0..ret.len() {
        if text[i] == '(' {
            layer += 1
        }
        if text[i] == ')' {
            layer -= 1
        }
        if layer < 0 {
            return Err(ParseErr::UnpairedBraces);
        }
        if layer > 0 {
            continue;
        }
        ret.push(text[i])
    }
    Ok(ret.iter().collect::<String>())
}

/// finds position of the char in the first layer
pub fn first_layer_find(text: &str, discriminator: char) -> Result<Vec<usize>, ParseErr> {
    let mut ret: Vec<usize> = vec![];
    let mut layer = 0i32;
    let text: Vec<char> = text.chars().collect();
    for i in 0..text.len() {
        if text[i] == '(' {
            layer += 1
        }
        if text[i] == ')' {
            layer -= 1
        }
        if layer < 0 {
            return Err(ParseErr::UnpairedBraces);
        }
        if layer > 0 {
            continue;
        }
        if text[i] == discriminator {
            ret.push(i)
        }
    }
    Ok(ret)
}

/// returns (position, length)
pub fn pinpoint_associative_operators(
    text: &str,
    prop: &PropUntitled,
) -> Result<Vec<usize>, ParseErr> {
    let mut ret: Vec<usize> = vec![];
    let mut layer = 0i32;
    let text: Vec<char> = text.chars().collect();
    if !prop.is_associative_operator() {
        return Ok(ret);
    }
    for i in 0..text.len() {
        if text[i] == '(' {
            layer += 1
        }
        if text[i] == ')' {
            layer -= 1
        }
        if layer < 0 {
            return Err(ParseErr::UnpairedBraces);
        }
        if layer > 0 {
            continue;
        }
        if text[i] == prop.symbol().unwrap() {
            ret.push(i)
        }
    }
    Ok(ret)
}

pub fn replace(text: &str) -> String {
    // pqrs¬∧∨⊕→≡↔
    let text = text.replace("<->", "↔");
    let text = text.replace("->", "→");
    let text = text.replace("^", "⊕");
    let text = text.replace("|", "∨");
    let text = text.replace("&", "∧");
    let text = text.replace("-", "¬");
    text
}
/// removes 1 layer of unnecessary parens.
/// if success, returns the Ok of trimmed text
/// if fails, returns the Err of untrimmed text
pub fn unwrap_parens(text: &str) -> Result<String, String> {
    if !text.starts_with("(") {
        return Err(text.to_string());
    }
    if !text.ends_with(")") {
        return Err(text.to_string());
    }
    let mut depth = 0i32;
    let text: Vec<char> = text.chars().collect();
    for i in 1..text.len() - 1 {
        if text[i] == '(' {
            depth += 1;
        } else if text[i] == ')' {
            depth -= 1
        }
        if depth < 0 {
            return Err(text.iter().collect());
        }
    }
    return Ok(text[1..text.len() - 1].iter().collect());
}

pub fn parse(text: &str) -> Result<Prop, ParseErr> {
    if text.is_empty(){
        return Err(ParseErr::EmptyString)
    }
    if text.chars().all(|x: char| x.is_alphabetic()) {
        return Ok(Prop::Var(text.to_string()));
    }

    let mut text = replace(text);

    loop {
        match unwrap_parens(&text) {
            Ok(x) => text = x,
            Err(_) => break,
        };
    }

    let chars: Vec<char> = text.chars().collect();
    let highest_rank = highest_order(&chars)?;
    dbg!(text.clone());
    dbg!("ey");
    // println!("{text}");
    println!("highest_rank = {highest_rank:?}");
    match &highest_rank {
        PropUntitled::Not => {
            let tmp = first_layer_find(&text, '¬')?[0];
            let bytes = text.chars()
                            .take(tmp)
                            .map(|x: char|x.len_utf8())
                            .sum();
            let (_, right) = text.split_at(bytes);
            let right = right.split('¬').last().ok_or(ParseErr::Unknown)?;
            return Ok(n!(parse(dbg!(right))?));
        }
        PropUntitled::Impl => {
            let tmp = first_layer_find(&text, '→')?[0];
            let bytes = text.chars()
                            .take(tmp)
                            .map(|x: char|x.len_utf8())
                            .sum();
            let (left, right) = text.split_at(bytes);
            dbg!(&(left, right));
            let right = right.split('→').last().ok_or(ParseErr::Unknown)?;
            return Ok(imply!(parse(dbg!(left))?, parse(dbg!(right))?));
        }
        _ => {
            let mut children: Vec<Prop> = vec![];
            let splitted: Vec<usize> = pinpoint_associative_operators(&text, &highest_rank)?;
            if splitted.len()==0{
                return Err(ParseErr::TokenNotFound)
            }
            let chars: Vec<char> = text.chars().collect();
            //p^qa^r 
            //1,4
            //0..1
            //2..4
            //5..6
            for i in 0..splitted.len(){
                let part: Vec<char>;
                if i == 0{
                    part = dbg!(chars[0..splitted[i]].to_vec())
                } else {
                    part = dbg!(chars[splitted[i-1]+1..splitted[i]].to_vec())
                }
                children.push(parse(&part.iter().collect::<String>())?);
            } 
            let part = dbg!(chars[splitted.last().unwrap()+1..].to_vec());
            children.push(parse(&part.iter().collect::<String>())?);
            //dbg!(buffer.0.clone());
            
            Ok(highest_rank.associative_wrapper(children).ok_or(ParseErr::Unknown)? )
        }
    }
}
