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
    /// Track range hints (in bits) for encoded terms, to reuse on order constraints.
    range_hints: HashMap<String, usize>,
}

impl Cvc5ffBackend {
    pub fn new(field_modulus: i128) -> Self {
        Self {
            field_modulus,
            vars: HashMap::new(),
            asserts: Vec::new(),
            range_fresh: 0,
            range_hints: HashMap::new(),
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
            // Permit numeric sorts to cohabit the field sort; Bool stays strict.
            let compatible = match (prev, sort) {
                (SymType::Bool, SymType::Bool) => true,
                (SymType::F, SymType::F)
                | (SymType::F, SymType::Uint(_))
                | (SymType::F, SymType::Int(_)) => true,
                (SymType::Uint(_), SymType::F) | (SymType::Int(_), SymType::F) => true,
                (SymType::Uint(_), SymType::Uint(_))
                | (SymType::Int(_), SymType::Int(_)) => true,
                _ => false,
            };

            if !compatible {
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
                self.vars.insert(name.to_owned(), SymType::F);
                Ok(())
            }

            // Bool variables are encoded as 0/1 elements of F.
            SymType::Bool => {
                self.vars.insert(name.to_owned(), SymType::Bool);
                self.asserts
                    .push(format!("(or (= {0} (as ff0 F)) (= {0} (as ff1 F)))", name));
                Ok(())
            }

            // Treat machine integers as field elements; range predicates will bound them.
            SymType::Uint(_) | SymType::Int(_) => {
                self.vars.insert(name.to_owned(), SymType::F);
                Ok(())
            }
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
        if bits == 0 || bits > 24 {
            return Err("cvc5-ff: byte decomposition only supports 1..24 bits".to_string());
        }

        let target = self.encode_term(value)?;
        self.range_hints.insert(target.clone(), bits);
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

    /// Return `Some(bits)` if `k` is of the form 2^bits - 1 with a small bit-width.
    fn pow2_minus1_bits(k: i128) -> Option<usize> {
        if k < 0 {
            return None;
        }
        let kp1 = (k + 1) as u128;
        if kp1.is_power_of_two() {
            let bits = kp1.trailing_zeros() as usize;
            if bits > 0 && bits <= 24 {
                return Some(bits);
            }
        }
        None
    }

    fn ceil_log2_u128(x: u128) -> usize {
        if x <= 1 {
            1
        } else {
            (128 - x.leading_zeros()) as usize
        }
    }

    /// Try to derive a bit width hint for a previously-encoded term.
    fn hint_bits_for_term(&self, term: &str) -> Option<usize> {
        self.range_hints.get(term).copied()
    }

    /// Best-effort encoding for order comparisons when the bound is a `2^n-1` constant.
    /// This covers common byte-sized overflow checks such as `x > 255`.
    fn encode_order_with_pow2_const(
        &mut self,
        op: &str,
        lhs: &SymExpr,
        rhs: &SymExpr,
    ) -> Option<Result<String, String>> {
        fn as_const(e: &SymExpr) -> Option<i128> {
            if let SymExpr::Int(k) = e {
                if *k >= 0 {
                    return Some(*k);
                }
            }
            None
        }

        // Normalize to (value ? const) where const is on the RHS.
        let (val, k, norm_op) = match (as_const(lhs), as_const(rhs)) {
            (_, Some(c)) => (lhs, c, op),
            (Some(c), _) => {
                let swapped = match op {
                    "lt" => "gt",
                    "le" => "ge",
                    "gt" => "lt",
                    "ge" => "le",
                    _ => return None,
                };
                (rhs, c, swapped)
            }
            _ => return None,
        };

        let bits = Self::pow2_minus1_bits(k)?;

        match norm_op {
            // x > (2^n-1)  ==>  x - 2^n in [0, 2^n-1]
            "gt" => {
                let shifted = SymExpr::Sub(Box::new(val.clone()), Box::new(SymExpr::Int(k + 1)));
                Some(self.encode_range_byte_decomposition(&shifted, bits))
            }

            // x >= (2^n-1)  ==>  x - (2^n-1) in [0, 2^n-1]
            "ge" => {
                let shifted = SymExpr::Sub(Box::new(val.clone()), Box::new(SymExpr::Int(k)));
                Some(self.encode_range_byte_decomposition(&shifted, bits))
            }

            // x <= (2^n-1) is equivalent to x in [0, 2^n-1].
            "le" => Some(self.encode_range_byte_decomposition(val, bits)),

            // Skip strict `<` for now to avoid over-approximating.
            _ => None,
        }
    }

    /// General order encoding: require one side to be a non-negative constant.
    /// Encodes `val ? k` as a bounded offset `val = k + c` with a small bit-width for `c`.
    /// Falls back to an error if we cannot find a safe bound within 24 bits.
    fn encode_order_with_const(
        &mut self,
        op: &str,
        lhs: &SymExpr,
        rhs: &SymExpr,
    ) -> Option<Result<String, String>> {
        fn as_const(e: &SymExpr) -> Option<i128> {
            if let SymExpr::Int(k) = e {
                if *k >= 0 {
                    return Some(*k);
                }
            }
            None
        }

        // Normalize so that the constant is on the RHS.
        let (val, k, norm_op, swapped) = match (as_const(lhs), as_const(rhs)) {
            (_, Some(c)) => (lhs, c, op, false),
            (Some(c), _) => {
                let swapped = match op {
                    "lt" => "gt",
                    "le" => "ge",
                    "gt" => "lt",
                    "ge" => "le",
                    _ => return None,
                };
                (rhs, c, swapped, true)
            }
            _ => return None,
        };

        // Guard against wrap-around: refuse if k is too close to the modulus.
        if k >= self.field_modulus / 2 {
            return Some(Err(format!(
                "cvc5-ff: order comparison constant {} is too large for safe offset encoding",
                k
            )));
        }

        // Encode the value term once for hint lookup.
        let val_term = match self.encode_term(val) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };

        let hint_bits = self.hint_bits_for_term(&val_term);

        // Helper: build offset encoding val = k + c, with 1 <= c <= 2^bits-1 (or 0.. when op is le).
        let encode_offset = |backend: &mut Cvc5ffBackend, start: i128, bits: usize| {
            // start is k (for ge/gt) or 0 (for le), bits bounds the offset.
            let c_bits = bits.min(24).max(1);
            let offset = SymExpr::Sub(Box::new(val.clone()), Box::new(SymExpr::Int(start)));
            backend.encode_range_byte_decomposition(&offset, c_bits)
        };

        match norm_op {
            // x > k  => x - (k+1) in [0, 2^bits-1], ensure bits large enough for hint gap.
            "gt" | "ge" => {
                let min_gap = if norm_op == "gt" { 1 } else { 0 };
                let bits_needed = if let Some(h) = hint_bits {
                    let max_val = (1_u128 << h).saturating_sub(1);
                    let gap = max_val.saturating_sub((k as u128) + min_gap as u128);
                    let safe_gap = gap.min((1_u128 << 24) - 1);
                    Self::ceil_log2_u128(safe_gap + 1)
                } else {
                    24 // fallback: still safe under p/2; may be bigger than necessary.
                };

                let start = k + min_gap as i128;
                Some(encode_offset(self, start, bits_needed))
            }

            // x <= k  => if hint says max<=k, it's trivially true; otherwise encode x in [0,k].
            "le" => {
                if let Some(h) = hint_bits {
                    let max_val = (1_u128 << h) - 1;
                    if (k as u128) >= max_val {
                        return Some(Ok("true".to_string()));
                    }
                }
                let bits_needed = Self::ceil_log2_u128((k as u128) + 1);
                let offset = SymExpr::Sub(Box::new(val.clone()), Box::new(SymExpr::Int(0)));
                Some(self.encode_range_byte_decomposition(&offset, bits_needed))
            }

            // x < k  => encode x <= k-1 if k>0.
            "lt" => {
                if k == 0 {
                    return Some(Ok("false".to_string()));
                }
                let adj = k - 1;
                let bits_needed = Self::ceil_log2_u128((adj as u128) + 1);
                let offset = SymExpr::Sub(Box::new(val.clone()), Box::new(SymExpr::Int(0)));
                Some(self.encode_range_byte_decomposition(&offset, bits_needed))
            }

            _ => None,
        }
        .map(|res| {
            res.map_err(|e| {
                format!(
                    "cvc5-ff: failed to encode order comparison (swapped={}): {}",
                    swapped, e
                )
            })
        })
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

            BoolExpr::Le(a, b) => {
                if let Some(res) = self.encode_order_with_const("le", a, b) {
                    return res;
                }
                if let Some(res) = self.encode_order_with_pow2_const("le", a, b) {
                    return res;
                }
                Err("cvc5-ff: order comparisons (<,<=,>,>=) are not supported in QF_FF"
                    .to_string())
            }
            BoolExpr::Lt(_, _) => {
                Err("cvc5-ff: order comparisons (<,<=,>,>=) are not supported in QF_FF"
                    .to_string())
            }
            BoolExpr::Ge(a, b) => {
                if let Some(res) = self.encode_order_with_const("ge", a, b) {
                    return res;
                }
                if let Some(res) = self.encode_order_with_pow2_const("ge", a, b) {
                    return res;
                }
                Err("cvc5-ff: order comparisons (<,<=,>,>=) are not supported in QF_FF"
                    .to_string())
            }
            BoolExpr::Gt(a, b) => {
                if let Some(res) = self.encode_order_with_const("gt", a, b) {
                    return res;
                }
                if let Some(res) = self.encode_order_with_pow2_const("gt", a, b) {
                    return res;
                }
                Err("cvc5-ff: order comparisons (<,<=,>,>=) are not supported in QF_FF"
                    .to_string())
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

        out.push_str("(check-sat)\n(exit)\n");
        out
    }

    pub fn check(mut self, phi: &BoolExpr, cmd: &str) -> Result<bool, String> {
        self.assert_bool(phi)?;
        let script = self.build_script();

        if std::env::var("CVC5_DUMP").is_ok() {
            let _ = std::fs::write("cvc5_debug.smt2", &script);
        }

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
