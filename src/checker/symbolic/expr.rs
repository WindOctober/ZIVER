use std::fmt::{Display, Formatter};
use std::ops::{Add, Div, Mul, Sub};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymType {
    /// Finite field element (generic field `F`).
    F,
    /// Unsigned integer with a fixed bit width.
    Uint(usize),
    /// Signed integer with a fixed bit width.
    Int(usize),
    /// Boolean value.
    Bool,
}

/// Integer-valued symbolic expressions for SMT-LIB NIA.
/// The design preserves structure (no evaluation), enabling constraint emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymExpr {
    Int(i128),
    Var(String, SymType),
    Neg(Box<SymExpr>),
    Add(Vec<SymExpr>), // n-ary addition
    Mul(Vec<SymExpr>), // n-ary multiplication
    Sub(Box<SymExpr>, Box<SymExpr>),
    Div(Box<SymExpr>, Box<SymExpr>), // Euclidean integer division (maps to `div`)
    Ite(Box<BoolExpr>, Box<SymExpr>, Box<SymExpr>),
}

/// Boolean expressions used in guards and `ite`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolExpr {
    Bool(bool),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Eq(SymExpr, SymExpr),
    Ne(SymExpr, SymExpr),
    Le(SymExpr, SymExpr),
    Lt(SymExpr, SymExpr),
    Ge(SymExpr, SymExpr),
    Gt(SymExpr, SymExpr),
}

impl SymExpr {
    /// Builds an `ite` expression with a Boolean guard.
    pub fn ite(cond: BoolExpr, then_e: SymExpr, else_e: SymExpr) -> Self {
        SymExpr::Ite(Box::new(cond), Box::new(then_e), Box::new(else_e))
    }

    /// Comparison constructors yield Boolean expressions (SMT-LIB relations).
    pub fn eq_to(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Eq(self, rhs)
    }
    pub fn ne(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Ne(self, rhs)
    }
    pub fn le(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Le(self, rhs)
    }
    pub fn lt(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Lt(self, rhs)
    }
    pub fn ge(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Ge(self, rhs)
    }
    pub fn gt(self, rhs: SymExpr) -> BoolExpr {
        BoolExpr::Gt(self, rhs)
    }
}

/* ---------- Smart constructors (lightweight flattening & constants) ---------- */

fn simplify_add(mut xs: Vec<SymExpr>) -> SymExpr {
    // Constant-folding and variadic flattening for aesthetics.
    let mut sum: i128 = 0;
    let mut flat: Vec<SymExpr> = Vec::new();
    for x in xs.drain(..) {
        match x {
            SymExpr::Int(k) => sum += k,
            SymExpr::Add(vs) => {
                for v in vs {
                    match v {
                        SymExpr::Int(k) => sum += k,
                        other => flat.push(other),
                    }
                }
            }
            other => flat.push(other),
        }
    }
    if sum != 0 {
        flat.push(SymExpr::Int(sum));
    }
    match flat.len() {
        0 => SymExpr::Int(0),
        1 => flat.pop().unwrap(),
        _ => SymExpr::Add(flat),
    }
}

fn simplify_mul(mut xs: Vec<SymExpr>) -> SymExpr {
    // Multiplicative folding with 0/1 handling and n-ary flattening.
    let mut prod: i128 = 1;
    let mut flat: Vec<SymExpr> = Vec::new();
    for x in xs.drain(..) {
        match x {
            SymExpr::Int(k) => {
                if k == 0 {
                    return SymExpr::Int(0);
                }
                prod = prod.saturating_mul(k);
            }
            SymExpr::Mul(vs) => {
                for v in vs {
                    match v {
                        SymExpr::Int(k) => {
                            if k == 0 {
                                return SymExpr::Int(0);
                            }
                            prod = prod.saturating_mul(k);
                        }
                        other => flat.push(other),
                    }
                }
            }
            other => flat.push(other),
        }
    }
    if prod == 0 {
        return SymExpr::Int(0);
    }
    if prod != 1 {
        flat.insert(0, SymExpr::Int(prod));
    }
    match flat.len() {
        0 => SymExpr::Int(1),
        1 => flat.pop().unwrap(),
        _ => SymExpr::Mul(flat),
    }
}

fn simplify_sub(a: SymExpr, b: SymExpr) -> SymExpr {
    match (a, b) {
        (SymExpr::Int(x), SymExpr::Int(y)) => SymExpr::Int(x - y),
        (lhs, SymExpr::Int(0)) => lhs,
        (lhs, rhs) => SymExpr::Sub(Box::new(lhs), Box::new(rhs)),
    }
}

fn simplify_div(a: SymExpr, b: SymExpr) -> SymExpr {
    // Symbolic integer division; map to SMT-LIB `div`. No evaluation (keeps structure).
    match (a, b) {
        (SymExpr::Int(x), SymExpr::Int(y)) => {
            // Avoid division by zero here; keep symbolic if y==0.
            if y != 0 {
                SymExpr::Int(x.div_euclid(y))
            } else {
                SymExpr::Div(Box::new(SymExpr::Int(x)), Box::new(SymExpr::Int(y)))
            }
        }
        (lhs, rhs) => SymExpr::Div(Box::new(lhs), Box::new(rhs)),
    }
}

/* ---------- Conversions ---------- */

impl From<i64> for SymExpr {
    fn from(v: i64) -> Self {
        SymExpr::Int(v as i128)
    }
}
impl From<i128> for SymExpr {
    fn from(v: i128) -> Self {
        SymExpr::Int(v)
    }
}

/* ---------- Operator overloads (builder-style; no evaluation) ---------- */

impl Add for SymExpr {
    type Output = SymExpr;
    fn add(self, rhs: SymExpr) -> SymExpr {
        simplify_add(vec![self, rhs])
    }
}
impl<'a> Add<&'a SymExpr> for SymExpr {
    type Output = SymExpr;
    fn add(self, rhs: &'a SymExpr) -> SymExpr {
        simplify_add(vec![self, rhs.clone()])
    }
}
impl Sub for SymExpr {
    type Output = SymExpr;
    fn sub(self, rhs: SymExpr) -> SymExpr {
        simplify_sub(self, rhs)
    }
}
impl<'a> Sub<&'a SymExpr> for SymExpr {
    type Output = SymExpr;
    fn sub(self, rhs: &'a SymExpr) -> SymExpr {
        simplify_sub(self, rhs.clone())
    }
}
impl Mul for SymExpr {
    type Output = SymExpr;
    fn mul(self, rhs: SymExpr) -> SymExpr {
        simplify_mul(vec![self, rhs])
    }
}
impl<'a> Mul<&'a SymExpr> for SymExpr {
    type Output = SymExpr;
    fn mul(self, rhs: &'a SymExpr) -> SymExpr {
        simplify_mul(vec![self, rhs.clone()])
    }
}
impl Div for SymExpr {
    type Output = SymExpr;
    fn div(self, rhs: SymExpr) -> SymExpr {
        simplify_div(self, rhs)
    }
}
impl<'a> Div<&'a SymExpr> for SymExpr {
    type Output = SymExpr;
    fn div(self, rhs: &'a SymExpr) -> SymExpr {
        simplify_div(self, rhs.clone())
    }
}

/* ---------- Boolean combinators ---------- */

impl BoolExpr {
    /// Builds a negation.
    pub fn not(self) -> Self {
        BoolExpr::Not(Box::new(self))
    }
    /// Builds a conjunction (variadic).
    pub fn and(mut xs: Vec<BoolExpr>) -> Self {
        // Lightweight flattening.
        let mut flat = Vec::new();
        for x in xs.drain(..) {
            match x {
                BoolExpr::And(vs) => flat.extend(vs),
                other => flat.push(other),
            }
        }
        match flat.len() {
            0 => BoolExpr::Bool(true),
            1 => flat.pop().unwrap(),
            _ => BoolExpr::And(flat),
        }
    }
    /// Builds a disjunction (variadic).
    pub fn or(mut xs: Vec<BoolExpr>) -> Self {
        let mut flat = Vec::new();
        for x in xs.drain(..) {
            match x {
                BoolExpr::Or(vs) => flat.extend(vs),
                other => flat.push(other),
            }
        }
        match flat.len() {
            0 => BoolExpr::Bool(false),
            1 => flat.pop().unwrap(),
            _ => BoolExpr::Or(flat),
        }
    }
}

/* ---------- SMT-LIB format transform (minimal) ---------- */

impl Display for SymType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SymType::F => write!(f, "F"),                 // field element
            SymType::Uint(w) => write!(f, "uint({})", w), // unsigned int with width
            SymType::Int(w) => write!(f, "int({})", w),   // signed int with width
            SymType::Bool => write!(f, "bool"),           // boolean
        }
    }
}

impl Display for SymExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SymExpr::Int(k) => write!(f, "{k}"),
            SymExpr::Var(s, ty) => write!(f, "{s} : {ty}"),
            SymExpr::Neg(x) => write!(f, "(- {})", x),
            SymExpr::Add(xs) => {
                if xs.is_empty() {
                    return write!(f, "0");
                }
                write!(f, "(+")?;
                for x in xs {
                    write!(f, " {}", x)?;
                }
                write!(f, ")")
            }
            SymExpr::Mul(xs) => {
                if xs.is_empty() {
                    return write!(f, "1");
                }
                write!(f, "(*")?;
                for x in xs {
                    write!(f, " {}", x)?;
                }
                write!(f, ")")
            }
            SymExpr::Sub(a, b) => write!(f, "(- {} {})", a, b),
            SymExpr::Div(a, b) => write!(f, "(div {} {})", a, b),
            SymExpr::Ite(c, t, e) => write!(f, "(ite {} {} {})", c, t, e),
        }
    }
}

impl Display for BoolExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BoolExpr::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            BoolExpr::Not(x) => write!(f, "(not {})", x),
            BoolExpr::And(xs) => {
                if xs.is_empty() {
                    return write!(f, "true");
                }
                write!(f, "(and")?;
                for x in xs {
                    write!(f, " {}", x)?;
                }
                write!(f, ")")
            }
            BoolExpr::Or(xs) => {
                if xs.is_empty() {
                    return write!(f, "false");
                }
                write!(f, "(or")?;
                for x in xs {
                    write!(f, " {}", x)?;
                }
                write!(f, ")")
            }
            BoolExpr::Eq(a, b) => write!(f, "(= {} {})", a, b),
            BoolExpr::Ne(a, b) => write!(f, "(not (= {} {}))", a, b),
            BoolExpr::Le(a, b) => write!(f, "(<= {} {})", a, b),
            BoolExpr::Lt(a, b) => write!(f, "(< {} {})", a, b),
            BoolExpr::Ge(a, b) => write!(f, "(>= {} {})", a, b),
            BoolExpr::Gt(a, b) => write!(f, "(> {} {})", a, b),
        }
    }
}
