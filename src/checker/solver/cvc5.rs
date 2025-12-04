use std::collections::HashMap;
use std::io::Write;
use std::process::{Command, Stdio};

use crate::checker::symbolic::expr::{BoolExpr, SymExpr, SymType};

/// cvc5 backend using QF_FF for field constraints.
pub struct Cvc5ffBackend {
    field_modulus: i128,
    vars: HashMap<String, SymType>,
    asserts: Vec<String>,
    range_fresh: usize,
}

impl Cvc5ffBackend {
    pub fn new(field_modulus: i128) -> Self {
        Self {
            field_modulus,
            vars: HashMap::new(),
            asserts: Vec::new(),
            range_fresh: 0,
        }
    }

    fn flatten_and<'a>(b: &'a BoolExpr, out: &mut Vec<&'a BoolExpr>) {
        match b {
            BoolExpr::And(xs) => {
                for c in xs {
                    Self::flatten_and(c, out);
                }
            }
            other => out.push(other),
        }
    }

    /// Register a symbolic variable and enforce basic sort-specific constraints.
    fn ensure_var(&mut self, name: &str, sort: &SymType) -> Result<(), String> {
        if let Some(prev) = self.vars.get(name) {
            if prev != sort {
                return Err(format!(
                    "cvc5-ff: inconsistent sort for `{}`: prev={:?}, new={:?}",
                    name, prev, sort
                ));
            }
            return Ok(());
        }

        match sort {
            // Field elements are interpreted directly in the finite field F.
            SymType::F => {
                self.vars.insert(name.to_owned(), sort.clone());
                Ok(())
            }

            // Bool variables are encoded as 0/1 elements of F.
            SymType::Bool => {
                self.vars.insert(name.to_owned(), sort.clone());
                self.asserts
                    .push(format!("(or (= {0} (as ff0 F)) (= {0} (as ff1 F)))", name));
                Ok(())
            }

            // Other scalar sorts are not handled in the FF backend yet.
            other => Err(format!(
                "cvc5-ff: sort {:?} is not supported in the finite-field backend for `{}`",
                other, name
            )),
        }
    }

    fn encode_term(&mut self, e: &SymExpr) -> Result<String, String> {
        match e {
            SymExpr::Int(k) => Ok(format!("(as ff{} F)", k)),

            SymExpr::Var(name, sort) => {
                // Both field and bool vars live in F; bools get 0/1 constraints in ensure_var.
                self.ensure_var(name, sort)?;
                Ok(name.clone())
            }

            SymExpr::Neg(inner) => {
                let t = self.encode_term(inner)?;
                Ok(format!("(ff.neg {})", t))
            }

            SymExpr::Add(xs) => {
                if xs.is_empty() {
                    return Ok("(as ff0 F)".to_string());
                }
                if xs.len() == 1 {
                    return self.encode_term(&xs[0]);
                }
                let parts: Result<Vec<_>, _> = xs.iter().map(|e| self.encode_term(e)).collect();
                let parts = parts?;
                Ok(format!("(ff.add {})", parts.join(" ")))
            }

            SymExpr::Mul(xs) => {
                if xs.is_empty() {
                    return Ok("(as ff1 F)".to_string());
                }
                if xs.len() == 1 {
                    return self.encode_term(&xs[0]);
                }
                let parts: Result<Vec<_>, _> = xs.iter().map(|e| self.encode_term(e)).collect();
                let parts = parts?;
                Ok(format!("(ff.mul {})", parts.join(" ")))
            }

            SymExpr::Sub(a, b) => {
                let a_s = self.encode_term(a)?;
                let b_s = self.encode_term(b)?;
                // a - b = a + (-b)
                Ok(format!("(ff.add {} (ff.neg {}))", a_s, b_s))
            }

            SymExpr::Div(a, b) => {
                let a_s = self.encode_term(a)?;
                let b_s = self.encode_term(b)?;
                // a / b = a * b^{-1}
                Ok(format!("(ff.mul {} (ff.inv {}))", a_s, b_s))
            }

            SymExpr::Mod(a, m) => {
                if let SymExpr::Int(k) = &**m {
                    if *k == self.field_modulus {
                        return self.encode_term(a);
                    }
                }
                Err("cvc5-ff: SymExpr::Mod only supports `mod FIELD_MODULUS`".to_string())
            }

            SymExpr::Ite(cond, t, e) => {
                let c_s = self.encode_bool(cond)?;
                let t_s = self.encode_term(t)?;
                let e_s = self.encode_term(e)?;
                // Conditional field expression
                Ok(format!("(ite {} {} {})", c_s, t_s, e_s))
            }
        }
    }

    /// Encode a byte-wise range decomposition in the finite field backend.
    /// This enforces `value` to lie in `[0, 2^{bits}-1]` by expressing it
    /// as the sum of little-endian bytes composed from Boolean bits.
    fn encode_range_byte_decomposition(
        &mut self,
        value: &SymExpr,
        bits: usize,
    ) -> Result<String, String> {
        if bits == 0 || bits > 16 {
            return Err("cvc5-ff: byte decomposition only supports 1..16 bits".to_string());
        }

        let target = self.encode_term(value)?;
        let mut remaining = bits;
        let byte_count = (bits + 7) / 8;
        let range_id = self.range_fresh;
        self.range_fresh += 1;

        let mut accum_terms = Vec::new();
        for i in 0..byte_count {
            let chunk_bits = remaining.min(8);
            remaining -= chunk_bits;

            let mut bit_terms = Vec::new();
            for j in 0..chunk_bits {
                let name = format!("__range_b{}_{}_{}", range_id, i, j);
                self.ensure_var(&name, &SymType::Bool)?;
                let coeff = 1_i128 << j;
                bit_terms.push(format!("(ff.mul (as ff{} F) {})", coeff, name));
            }

            let byte_sum = if bit_terms.len() == 1 {
                bit_terms[0].clone()
            } else {
                format!("(ff.add {})", bit_terms.join(" "))
            };

            let scale = 256_i128.pow(i as u32);
            let scaled = if scale == 1 {
                byte_sum.clone()
            } else {
                format!("(ff.mul (as ff{} F) {})", scale, byte_sum)
            };
            accum_terms.push(scaled);
        }

        let combined = if accum_terms.len() == 1 {
            accum_terms.remove(0)
        } else {
            format!("(ff.add {})", accum_terms.join(" "))
        };

        Ok(format!("(= {} {})", target, combined))
    }

    fn encode_bool(&mut self, b: &BoolExpr) -> Result<String, String> {
        match b {
            BoolExpr::Bool(v) => Ok(if *v {
                "true".to_string()
            } else {
                "false".to_string()
            }),

            BoolExpr::Not(inner) => {
                let s = self.encode_bool(inner)?;
                Ok(format!("(not {})", s))
            }

            BoolExpr::And(xs) => {
                if xs.is_empty() {
                    return Ok("true".to_string());
                }
                let parts: Result<Vec<_>, _> = xs.iter().map(|e| self.encode_bool(e)).collect();
                let parts = parts?;
                if parts.len() == 1 {
                    Ok(parts.into_iter().next().unwrap())
                } else {
                    Ok(format!("(and {})", parts.join(" ")))
                }
            }

            BoolExpr::Or(xs) => {
                if xs.is_empty() {
                    return Ok("false".to_string());
                }
                let parts: Result<Vec<_>, _> = xs.iter().map(|e| self.encode_bool(e)).collect();
                let parts = parts?;
                if parts.len() == 1 {
                    Ok(parts.into_iter().next().unwrap())
                } else {
                    Ok(format!("(or {})", parts.join(" ")))
                }
            }

            BoolExpr::Eq(a, b) => {
                let a_s = self.encode_term(a)?;
                let b_s = self.encode_term(b)?;
                Ok(format!("(= {} {})", a_s, b_s))
            }

            BoolExpr::Ne(a, b) => {
                let a_s = self.encode_term(a)?;
                let b_s = self.encode_term(b)?;
                Ok(format!("(not (= {} {}))", a_s, b_s))
            }

            BoolExpr::Le(_, _) | BoolExpr::Lt(_, _) | BoolExpr::Ge(_, _) | BoolExpr::Gt(_, _) => {
                Err("cvc5-ff: order comparisons (<,<=,>,>=) are not supported in QF_FF".to_string())
            }
            BoolExpr::Range {
                value,
                min,
                max,
                bits,
            } => {
                if *min != 0 {
                    return Err("cvc5-ff: only non-negative ranges are supported".to_string());
                }

                let bw = bits.ok_or_else(|| {
                    "cvc5-ff: bit-width hint is required for range predicates".to_string()
                })?;

                let expected_max = (1_i128 << bw) - 1;
                if *max != expected_max {
                    return Err(format!(
                        "cvc5-ff: range upper bound must be 2^bits-1 (got {}, bits={})",
                        max, bw
                    ));
                }

                self.encode_range_byte_decomposition(value, bw)
            }
        }
    }

    pub fn assert_bool(&mut self, b: &BoolExpr) -> Result<(), String> {
        // Split top-level conjunction into multiple asserts for readability.
        let mut clauses = Vec::new();
        Self::flatten_and(b, &mut clauses);

        if clauses.is_empty() {
            return Ok(());
        }

        for c in clauses {
            let s = self.encode_bool(c)?;
            self.asserts.push(s);
        }

        Ok(())
    }

    pub fn build_script(&self) -> String {
        let mut out = String::new();
        out.push_str("(set-logic QF_FF)\n");
        out.push_str(&format!(
            "(define-sort F () (_ FiniteField {}))\n\n",
            self.field_modulus
        ));

        for (name, sort) in &self.vars {
            match sort {
                // Both field and 0/1-encoded bool variables use the field sort F.
                SymType::F | SymType::Bool => {
                    out.push_str(&format!("(declare-fun {} () F)\n", name));
                }
                _ => {
                    // Unsupported sorts are rejected earlier.
                }
            }
        }

        if !self.vars.is_empty() {
            out.push('\n');
        }

        for a in &self.asserts {
            out.push_str(&format!("(assert {})\n", a));
        }

        out.push_str("(check-sat)\n");
        out
    }

    pub fn check(mut self, phi: &BoolExpr, cmd: &str) -> Result<bool, String> {
        self.assert_bool(phi)?;
        let script = self.build_script();
        println!("cvc5-ff script:\n{}", script);

        let mut child = Command::new(cmd)
            .arg("--lang")
            .arg("smt2")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn `{}`: {}", cmd, e))?;

        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| "failed to open stdin for cvc5".to_string())?;
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| format!("failed to write SMT-LIB to cvc5: {}", e))?;
        }

        let output = child
            .wait_with_output()
            .map_err(|e| format!("failed to wait for cvc5: {}", e))?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            return Err(format!(
                "cvc5 exited with status {}.\nSTDOUT:\n{}\nSTDERR:\n{}",
                output.status, stdout, stderr
            ));
        }

        for line in stdout.lines().map(|l| l.trim()) {
            match line {
                "sat" => return Ok(true),
                "unsat" => return Ok(false),
                "unknown" => {
                    return Err(format!(
                        "cvc5 returned `unknown` for the formula.\nSTDERR:\n{}",
                        stderr
                    ));
                }
                _ => {}
            }
        }

        Err(format!(
            "no `sat`/`unsat`/`unknown` in cvc5 output.\nSTDOUT:\n{}\nSTDERR:\n{}",
            stdout, stderr
        ))
    }
}
