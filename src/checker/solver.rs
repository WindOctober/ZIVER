//! Z3 backend for symbolic formulas.
//!
//! This module translates the internal `SymExpr` / `BoolExpr` syntax into
//! Z3 ASTs and runs a single satisfiability check.  It is intentionally
//! lightweight and does not expose any Z3-specific details to the rest
//! of the checker.

use std::collections::HashMap;

use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

use crate::checker::symbolic::expr::{BoolExpr, SymExpr};

/// Lightweight Z3 front-end for encoding symbolic expressions.
///
/// A single instance holds one `Solver` together with a cache of integer
/// variables, keyed by their symbolic names.  All expressions are encoded
/// as unbounded integer arithmetic, ignoring bit-width information in
/// `SymType` for now.
pub struct Z3Encoder {
    solver: Solver,
    int_vars: HashMap<String, Int>,
}

impl Z3Encoder {
    /// Create a new encoder with a fresh Z3 solver instance.
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            int_vars: HashMap::new(),
        }
    }

    /// Mutable access to the underlying solver.
    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }

    /// Ensure that an integer variable with the given name is materialized.
    ///
    /// Reuses the same Z3 symbol whenever the name is requested again.
    fn int_var(&mut self, name: &str) -> Int {
        if let Some(v) = self.int_vars.get(name) {
            return v.clone();
        }
        let v = Int::new_const(name);
        self.int_vars.insert(name.to_owned(), v.clone());
        v
    }

    /// Encode an arithmetic `SymExpr` into a Z3 integer AST.
    ///
    /// All expressions are mapped to the Z3 integer sort.  If a literal
    /// does not fit into a signed 64-bit integer, the encoder reports an
    /// error via panic, as such values are not expected in the current
    /// setting.
    fn encode_int(&mut self, e: &SymExpr) -> Int {
        match e {
            SymExpr::Int(k) => {
                // This encoder assumes that all constants fit into i64.
                let v = i64::try_from(*k).expect("SymExpr::Int out of i64 range");
                Int::from_i64(v)
            }

            SymExpr::Var(name, _ty) => {
                // All scalar symbolic variables are mapped to integer symbols.
                self.int_var(name)
            }

            SymExpr::Neg(inner) => self.encode_int(inner).unary_minus(),

            SymExpr::Add(xs) => {
                if xs.is_empty() {
                    return Int::from_i64(0);
                }
                let mut it = xs.iter();
                let first = self.encode_int(
                    it.next()
                        .expect("non-empty Add must have at least one operand"),
                );
                it.fold(first, |acc, e| acc + self.encode_int(e))
            }

            SymExpr::Mul(xs) => {
                if xs.is_empty() {
                    return Int::from_i64(1);
                }
                let mut it = xs.iter();
                let first = self.encode_int(
                    it.next()
                        .expect("non-empty Mul must have at least one operand"),
                );
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
        }
    }

    /// Encode a Boolean guard into a Z3 Boolean AST.
    ///
    /// This function is structurally recursive and assumes that all
    /// embedded arithmetic expressions are well-typed scalars.
    fn encode_bool(&mut self, b: &BoolExpr) -> Bool {
        match b {
            BoolExpr::Bool(v) => Bool::from_bool(*v),

            BoolExpr::Not(inner) => self.encode_bool(inner).not(),

            BoolExpr::And(xs) => {
                if xs.is_empty() {
                    return Bool::from_bool(true);
                }
                // Use the associated function `Bool::and` rather than a
                // non-existent instance method.
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

            BoolExpr::Eq(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.eq(&b_z)
            }

            BoolExpr::Ne(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.ne(b_z)
            }

            BoolExpr::Le(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.le(b_z)
            }

            BoolExpr::Lt(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.lt(b_z)
            }

            BoolExpr::Ge(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.ge(b_z)
            }

            BoolExpr::Gt(a, b) => {
                let a_z = self.encode_int(a);
                let b_z = self.encode_int(b);
                a_z.gt(b_z)
            }
        }
    }

    /// Push a single Boolean constraint into the underlying solver.
    pub fn assert_bool(&mut self, b: &BoolExpr) {
        let z3_b = self.encode_bool(b);
        self.solver.assert(&z3_b);
    }
}

/// Check satisfiability of a single Boolean formula using Z3.
///
/// The function returns `Ok(true)` if the formula is satisfiable, and
/// `Ok(false)` if it is unsatisfiable.  If Z3 reports `Unknown`, the
/// function returns an error, as this outcome is not expected for the
/// current fragment.
pub fn check_with_z3(phi: &BoolExpr) -> Result<bool, String> {
    let mut enc = Z3Encoder::new();
    enc.assert_bool(phi);

    match enc.solver_mut().check() {
        SatResult::Sat => Ok(true),
        SatResult::Unsat => Ok(false),
        SatResult::Unknown => Err("Z3 returned `unknown` for the given formula".to_string()),
    }
}
