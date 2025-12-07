use std::collections::HashMap;

use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

use crate::checker::symbolic::expr::{BoolExpr, SymExpr, SymType};
use crate::checker::symbolic::range::{symexpr_range, symtype_range};

/// Z3 backend using integer arithmetic with range constraints.
pub struct Z3NiaBackend {
    solver: Solver,
    int_vars: HashMap<String, Int>,
    var_sorts: HashMap<String, SymType>,
    /// Optional range hints supplied by `assert_range` / Range predicates.
    range_hints: HashMap<String, (i128, i128)>,
}

impl Z3NiaBackend {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            int_vars: HashMap::new(),
            var_sorts: HashMap::new(),
            range_hints: HashMap::new(),
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
            self.assert_sort_range(Some(name), &v, s);
        }

        v
    }

    fn record_range_hint(&mut self, name: &str, min: i128, max: i128) {
        if min > max {
            return;
        }
        self.range_hints
            .entry(name.to_owned())
            .and_modify(|(lo, hi)| {
                let new_lo = std::cmp::max(*lo, min);
                let new_hi = std::cmp::min(*hi, max);
                if new_lo <= new_hi {
                    *lo = new_lo;
                    *hi = new_hi;
                }
            })
            .or_insert((min, max));
    }

    fn hint_for(&self, name: &str) -> Option<(i128, i128)> {
        self.range_hints.get(name).copied()
    }

    /// Conservative interval for an expression using recorded hints + symbolic sorts.
    fn expr_range(&self, e: &SymExpr) -> Option<(i128, i128)> {
        symexpr_range(e, |name, _| self.hint_for(name))
    }

    fn assert_sort_range(&mut self, name: Option<&str>, v: &Int, sort: &SymType) {
        // Build the default type range.
        let type_range: Option<(i128, Option<i128>)> =
            symtype_range(sort).map(|(lo, hi)| (lo, Some(hi)));

        // Merge with any hint provided for this name.
        let merged: Option<(i128, Option<i128>)> = if let (Some((h_lo, h_hi)), Some((t_lo, t_hi))) =
            (name.and_then(|nm| self.hint_for(nm)), type_range)
        {
            let lo = std::cmp::max(t_lo, h_lo);
            let hi = match (t_hi, Some(h_hi)) {
                (Some(a), Some(b)) => Some(std::cmp::min(a, b)),
                (None, hb) => hb,
                (ta, None) => ta,
            };
            Some((lo, hi))
        } else if let Some(h) = name.and_then(|nm| self.hint_for(nm)) {
            Some((h.0, Some(h.1)))
        } else {
            type_range
        };

        let Some((lo, hi_opt)) = merged else { return };

        if let Ok(lo_i64) = i64::try_from(lo) {
            self.solver.assert(&v.ge(&Int::from_i64(lo_i64)));
        }
        if let Some(hi) = hi_opt {
            if let Ok(hi_i64) = i64::try_from(hi) {
                self.solver.assert(&v.le(&Int::from_i64(hi_i64)));
            }
        }
    }

    fn maybe_record_range_hint(&mut self, e: &SymExpr, min: i128, max: i128) {
        if let SymExpr::Var(name, _) = e {
            self.record_range_hint(name, min, max);
        }
    }

    fn mod_can_drop(&self, expr: &SymExpr, modulus: &SymExpr) -> bool {
        if let SymExpr::Int(k) = modulus {
            if *k <= 0 {
                return false;
            }
            if let Some((lo, hi)) = self.expr_range(expr) {
                return lo >= 0 && hi < *k;
            }
        }
        false
    }

    fn encode_mod(&mut self, a: &SymExpr, b: &SymExpr) -> Int {
        if self.mod_can_drop(a, b) {
            return self.encode_int(a);
        }

        let az = self.encode_int(a);
        let bz = self.encode_int(b);
        az.modulo(&bz)
    }

    fn encode_range(&mut self, value: &SymExpr, min: i128, max: i128) -> Bool {
        self.maybe_record_range_hint(value, min, max);
        let v = self.encode_int(value);
        let lo = Int::from_i64(i64::try_from(min).expect("range lower bound out of i64"));
        let hi = Int::from_i64(i64::try_from(max).expect("range upper bound out of i64"));
        Bool::and(&[v.ge(&lo), v.le(&hi)])
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

            SymExpr::Mod(a, b) => self.encode_mod(a, b),
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
            } => self.encode_range(value, *min, *max),
        }
    }

    pub fn assert_bool(&mut self, b: &BoolExpr) {
        let z3_b = self.encode_bool(b);
        self.solver.assert(&z3_b);
    }

    pub fn check(mut self, phi: &BoolExpr) -> Result<bool, String> {
        // Preload range hints so mod-dropping can use them even if the
        // corresponding `Range` constraints appear later in the formula.
        self.preload_ranges(phi);
        self.assert_bool(phi);

        // Optional SMT dump before solving.
        if std::env::var("Z3_DUMP").is_ok() {
            let smt = self.solver.to_smt2();
            let _ = std::fs::write("z3_debug.smt2", smt);
        }
        if std::env::var("Z3_DUMP_ONLY").is_ok() {
            return Err("Z3_DUMP_ONLY set; solver run skipped after dump".to_string());
        }

        let solver = self.solver_mut();
        println!("Z3 (NIA) solving formula...");
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

    fn preload_ranges(&mut self, b: &BoolExpr) {
        match b {
            BoolExpr::Range {
                value, min, max, ..
            } => {
                self.maybe_record_range_hint(value, *min, *max);
            }
            BoolExpr::Eq(a, b) => {
                if let SymExpr::Int(k) = b {
                    if let SymExpr::Var(name, _) = a {
                        self.record_range_hint(name, *k, *k);
                    }
                }
                if let SymExpr::Int(k) = a {
                    if let SymExpr::Var(name, _) = b {
                        self.record_range_hint(name, *k, *k);
                    }
                }
            }
            BoolExpr::Not(inner) => self.preload_ranges(inner),
            BoolExpr::And(xs) => {
                for c in xs {
                    self.preload_ranges(c);
                }
            }
            // Disjunctions are skipped: hints drawn from different branches can conflict.
            BoolExpr::Or(_) => {}
            _ => {}
        }
    }
}
