use std::collections::HashMap;

use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

use crate::checker::symbolic::expr::{BoolExpr, FIELD_MODULUS, SymExpr, SymType};

/// Z3 backend using integer arithmetic with range constraints.
pub struct Z3NiaBackend {
    solver: Solver,
    int_vars: HashMap<String, Int>,
    var_sorts: HashMap<String, SymType>,
}

impl Z3NiaBackend {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            int_vars: HashMap::new(),
            var_sorts: HashMap::new(),
        }
    }

    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }

    fn int_var(&mut self, name: &str, sort: Option<&SymType>) -> Int {
        if let Some(v) = self.int_vars.get(name) {
            if let Some(s) = sort {
                if let Some(prev) = self.var_sorts.get(name) {
                    if prev != s {
                        panic!(
                            "Z3: inconsistent sort for `{}`: prev = {:?}, new = {:?}",
                            name, prev, s
                        );
                    }
                }
            }
            return v.clone();
        }

        let v = Int::new_const(name);
        self.int_vars.insert(name.to_owned(), v.clone());

        if let Some(s) = sort {
            self.var_sorts.insert(name.to_owned(), s.clone());
            self.assert_sort_range(&v, s);
        }

        v
    }

    fn assert_sort_range(&mut self, v: &Int, sort: &SymType) {
        fn i64_const(k: i128) -> i64 {
            i64::try_from(k).expect("Z3 range bound out of i64 range")
        }

        match sort {
            SymType::Bool => {
                let zero = Int::from_i64(0);
                let one = Int::from_i64(1);
                self.solver.assert(&v.ge(&zero));
                self.solver.assert(&v.le(&one));
            }

            SymType::Uint(w) => {
                let zero = Int::from_i64(0);
                if *w >= 63 {
                    self.solver.assert(&v.ge(&zero));
                } else {
                    let max = (1_i128 << *w as u32) - 1;
                    let hi = Int::from_i64(i64_const(max));
                    self.solver.assert(&v.ge(&zero));
                    self.solver.assert(&v.le(&hi));
                }
            }

            SymType::Int(w) => {
                if *w == 0 || *w >= 62 {
                    return;
                }
                let min = -(1_i128 << (*w as u32 - 1));
                let max = (1_i128 << (*w as u32 - 1)) - 1;
                let lo = Int::from_i64(i64_const(min));
                let hi = Int::from_i64(i64_const(max));
                self.solver.assert(&v.ge(&lo));
                self.solver.assert(&v.le(&hi));
            }

            SymType::F => {
                let zero = Int::from_i64(0);
                let p = Int::from_i64(i64_const(FIELD_MODULUS));
                self.solver.assert(&v.ge(&zero));
                self.solver.assert(&v.lt(&p));
            }
        }
    }

    fn encode_int(&mut self, e: &SymExpr) -> Int {
        match e {
            SymExpr::Int(k) => {
                let v = i64::try_from(*k).expect("SymExpr::Int out of i64 range");
                Int::from_i64(v)
            }

            SymExpr::Var(name, sort) => self.int_var(name, Some(sort)),

            SymExpr::Neg(inner) => self.encode_int(inner).unary_minus(),

            SymExpr::Add(xs) => {
                if xs.is_empty() {
                    return Int::from_i64(0);
                }
                let mut it = xs.iter();
                let first = self.encode_int(it.next().unwrap());
                it.fold(first, |acc, e| acc + self.encode_int(e))
            }

            SymExpr::Mul(xs) => {
                if xs.is_empty() {
                    return Int::from_i64(1);
                }
                let mut it = xs.iter();
                let first = self.encode_int(it.next().unwrap());
                it.fold(first, |acc, e| acc * self.encode_int(e))
            }

            SymExpr::Sub(a, b) => self.encode_int(a) - self.encode_int(b),

            SymExpr::Div(a, b) => self.encode_int(a).div(self.encode_int(b)),

            SymExpr::Ite(cond, t, e) => {
                let c = self.encode_bool(cond);
                let t_z3 = self.encode_int(t);
                let e_z3 = self.encode_int(e);
                c.ite(&t_z3, &e_z3)
            }

            SymExpr::Mod(a, b) => {
                let az = self.encode_int(a);
                let bz = self.encode_int(b);
                az.modulo(&bz)
            }
        }
    }

    fn encode_bool(&mut self, b: &BoolExpr) -> Bool {
        match b {
            BoolExpr::Bool(v) => Bool::from_bool(*v),

            BoolExpr::Not(inner) => self.encode_bool(inner).not(),

            BoolExpr::And(xs) => {
                if xs.is_empty() {
                    return Bool::from_bool(true);
                }
                let parts: Vec<Bool> = xs.iter().map(|e| self.encode_bool(e)).collect();
                Bool::and(&parts)
            }

            BoolExpr::Or(xs) => {
                if xs.is_empty() {
                    return Bool::from_bool(false);
                }
                let parts: Vec<Bool> = xs.iter().map(|e| self.encode_bool(e)).collect();
                Bool::or(&parts)
            }

            BoolExpr::Eq(a, b) => self.encode_int(a).eq(&self.encode_int(b)),
            BoolExpr::Ne(a, b) => self.encode_int(a).ne(&self.encode_int(b)),
            BoolExpr::Le(a, b) => self.encode_int(a).le(&self.encode_int(b)),
            BoolExpr::Lt(a, b) => self.encode_int(a).lt(&self.encode_int(b)),
            BoolExpr::Ge(a, b) => self.encode_int(a).ge(&self.encode_int(b)),
            BoolExpr::Gt(a, b) => self.encode_int(a).gt(&self.encode_int(b)),
            BoolExpr::Range {
                value, min, max, ..
            } => {
                let v = self.encode_int(value);
                let lo = Int::from_i64(i64::try_from(*min).expect("range lower bound out of i64"));
                let hi = Int::from_i64(i64::try_from(*max).expect("range upper bound out of i64"));
                Bool::and(&[v.ge(&lo), v.le(&hi)])
            }
        }
    }

    pub fn assert_bool(&mut self, b: &BoolExpr) {
        let z3_b = self.encode_bool(b);
        self.solver.assert(&z3_b);
    }

    pub fn check(mut self, phi: &BoolExpr) -> Result<bool, String> {
        self.assert_bool(phi);
        let solver = self.solver_mut();
        println!("Z3 (NIA) solving formula:\n{solver}");
        match solver.check() {
            SatResult::Sat => {
                if let Some(model) = solver.get_model() {
                    println!("Z3: SAT model:\n{model}");
                }
                Ok(true)
            }
            SatResult::Unsat => Ok(false),
            SatResult::Unknown => Err("Z3 returned `unknown` for the given formula".to_string()),
        }
    }
}
