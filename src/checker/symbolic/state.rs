use im::HashMap as IMap;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::ast::*;
use crate::checker::symbolic::context::{Context, PathKind};
use crate::checker::symbolic::eval_index_const_or_err;
use crate::checker::symbolic::expr::{
    BoolExpr, FIELD_MODULUS, SymExpr, SymType, SymValue, SymWord, WORD_BYTES,
};
use crate::checker::symbolic::range;

/// Persistent store node for symbolic memory.
#[derive(Clone, Debug)]
pub enum StoreNode {
    /// Scalar expression.
    Scalar(SymValue),

    /// Constant-size (or unknown-size) array.
    /// Indices must be concrete `usize`; symbolic indices are disallowed.
    Array {
        len: Option<usize>,
        elems: IMap<usize, StoreNode>,
    },

    /// Struct keyed by field id.
    Struct { fields: IMap<i64, StoreNode> },
}

impl StoreNode {
    fn scalar(e: SymValue) -> Self {
        StoreNode::Scalar(e)
    }
    fn array(len: Option<usize>) -> Self {
        StoreNode::Array {
            len,
            elems: IMap::new(),
        }
    }
    fn structure() -> Self {
        StoreNode::Struct {
            fields: IMap::new(),
        }
    }

    /// Recursively collect pairs of scalar symbolic expressions from `self`
    /// and `other`. This procedure enforces that the two nodes exhibit an
    /// identical structural "shape" (same set of fields for structs, same
    /// index set for arrays) and records all corresponding leaf-level scalar
    /// expressions as candidate output pairs.
    pub fn collect_scalar_pairs_with(
        &self,
        other: &StoreNode,
        out: &mut Vec<(SymExpr, SymExpr)>,
    ) -> Result<(), String> {
        match (self, other) {
            // Base case: both nodes are scalar expressions.
            (StoreNode::Scalar(a), StoreNode::Scalar(b)) => {
                out.push((a.surface.clone(), b.surface.clone()));
                if let (Some(wa), Some(wb)) = (a.word_bytes(), b.word_bytes()) {
                    for (ba, bb) in wa.iter().zip(wb.iter()) {
                        out.push((ba.clone(), bb.clone()));
                    }
                }
                Ok(())
            }

            // Recursive case: structs keyed by identical field identifiers.
            (StoreNode::Struct { fields: lf }, StoreNode::Struct { fields: rf }) => {
                if lf.len() != rf.len() {
                    return Err(format!(
                        "struct shape mismatch: lhs has {} fields, rhs has {} fields",
                        lf.len(),
                        rf.len()
                    ));
                }

                // Traverse fields in a deterministic order (sorted by field id)
                // to obtain a canonical pairing of subnodes.
                let mut keys: Vec<i64> = lf.keys().cloned().collect();
                keys.sort_unstable();

                for fid in keys {
                    let lc = lf.get(&fid).ok_or_else(|| {
                        format!("lhs is missing field id {} during struct comparison", fid)
                    })?;
                    let rc = rf.get(&fid).ok_or_else(|| {
                        format!("rhs is missing field id {} during struct comparison", fid)
                    })?;
                    lc.collect_scalar_pairs_with(rc, out)?;
                }
                Ok(())
            }

            // Recursive case: arrays with compatible lengths and index sets.
            (StoreNode::Array { len: ll, elems: le }, StoreNode::Array { len: rl, elems: re }) => {
                if ll != rl {
                    return Err(format!("array length mismatch: lhs {:?}, rhs {:?}", ll, rl));
                }

                let lhs_idxs: BTreeSet<_> = le.keys().cloned().collect();
                let rhs_idxs: BTreeSet<_> = re.keys().cloned().collect();
                if lhs_idxs != rhs_idxs {
                    return Err(format!(
                        "array index set mismatch: lhs {:?}, rhs {:?}",
                        lhs_idxs, rhs_idxs
                    ));
                }
                for i in lhs_idxs {
                    let lc = le.get(&i).unwrap();
                    let rc = re.get(&i).unwrap();
                    lc.collect_scalar_pairs_with(rc, out)?;
                }
                Ok(())
            }

            // Any remaining combination indicates a structural incompatibility.
            (l, r) => Err(format!(
                "store shape mismatch: lhs node `{:?}`, rhs node `{:?}`",
                l, r
            )),
        }
    }
}

/// Persistent store mapping variable ids to nodes.
#[derive(Clone, Debug, Default)]
pub struct Store {
    /// var/param/loop-var binding id -> node
    pub vars: IMap<i64, StoreNode>,
}

impl Store {
    pub fn get(&self, id: i64) -> Option<&StoreNode> {
        self.vars.get(&id)
    }
    pub fn set(self, id: i64, node: StoreNode) -> Self {
        Store {
            vars: self.vars.update(id, node),
        }
    }

    /// Resolve an expression to a store node (supports only Path).
    pub fn query_scalar_node(&self, e: &Expr) -> Option<&StoreNode> {
        match e {
            Expr::Path { ref_id, .. } => {
                let vid = (*ref_id)?;
                self.get(vid)
            }
            _ => {
                unreachable!()
            }
        }
    }

    /// Load a scalar symbolic value from the store; reject arrays/structs.
    pub fn query_scalar(&self, e: &Expr) -> Option<SymValue> {
        let node = self.query_scalar_node(e)?;
        match node {
            StoreNode::Scalar(se) => Some(se.clone()),
            StoreNode::Array { .. } => panic!("array used as scalar without indexing"),
            StoreNode::Struct { .. } => panic!("struct used as scalar without field selection"),
        }
    }
}

/// Execution status of the current state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecStatus {
    Step,
    Continue,
    Break,
    Return,
}

/// Memory interaction kind (Send/Receive) captured during execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryEventKind {
    Send,
    Receive,
}

/// Cached map read entry to keep clk_prev/value consistent across projections.
#[derive(Clone, Debug)]
pub struct MapReadRecord {
    pub base_id: Option<i64>,
    pub base_repr: String,
    pub clk: SymExpr,
    pub addr: SymExpr,
    pub clk_prev: SymExpr,
    pub value: SymExpr,
    clk_key: String,
    addr_key: String,
}

/// A single memory access record collected from lookups or map reads.
#[derive(Clone, Debug)]
pub struct MemoryEvent {
    pub kind: MemoryEventKind,
    pub clk: SymExpr,
    pub addr: SymExpr,
    pub value: SymExpr,
}

/// Symbolic state with path condition and persistent store.
#[derive(Clone, Debug)]
pub struct SymState {
    pub ctx: Rc<Context>,
    pub path_cond: Vec<BoolExpr>,
    pub store: Store,
    pub status: ExecStatus,
    pub memory_events: Vec<MemoryEvent>,
    pub map_reads: Vec<MapReadRecord>,
    bit_decomp_cache: HashMap<String, Vec<SymExpr>>,
    byte_op_cache: HashSet<String>,
    range_hints: HashMap<String, (i128, i128)>,
    fresh: usize,
    /// True if the accumulated path condition is already contradictory.
    unsat: bool,
}

/// Result of a lightweight Boolean simplification used during path pruning.
struct BoolSimplifyResult {
    expr: BoolExpr,
    always_true: bool,
    always_false: bool,
}

impl BoolSimplifyResult {
    fn from_constant(v: bool) -> Self {
        Self {
            expr: BoolExpr::Bool(v),
            always_true: v,
            always_false: !v,
        }
    }

    fn from_expr(expr: BoolExpr) -> Self {
        Self {
            expr,
            always_true: false,
            always_false: false,
        }
    }
}

fn tighten_range(
    hints: &mut HashMap<String, (i128, i128)>,
    name: &str,
    min: i128,
    max: i128,
) -> (bool, bool) {
    if min > max {
        return (true, false);
    }
    if let Some((lo, hi)) = hints.get_mut(name) {
        let implied = *lo >= min && *hi <= max;
        let new_lo = std::cmp::max(*lo, min);
        let new_hi = std::cmp::min(*hi, max);
        if new_lo > new_hi {
            return (true, implied);
        }
        *lo = new_lo;
        *hi = new_hi;
        (false, implied)
    } else {
        hints.insert(name.to_string(), (min, max));
        (false, false)
    }
}

impl SymState {
    pub fn new(ctx: Rc<Context>) -> Self {
        Self {
            ctx,
            path_cond: Vec::new(),
            store: Store::default(),
            status: ExecStatus::Step,
            memory_events: Vec::new(),
            map_reads: Vec::new(),
            bit_decomp_cache: HashMap::new(),
            byte_op_cache: HashSet::new(),
            range_hints: HashMap::new(),
            fresh: 0,
            unsat: false,
        }
    }
    /// Returns the next fresh index for symbol allocation.
    pub fn fresh_index(&self) -> usize {
        self.fresh
    }

    /// Overrides the starting fresh index.
    /// This is intended for orchestrating multiple symbolic runs that
    /// should not reuse symbol names.
    pub fn with_fresh_start(mut self, start: usize) -> Self {
        self.fresh = start;
        self
    }

    /// Return a new state with an additional path constraint appended.
    pub fn with_pc(mut self, cond: BoolExpr) -> Self {
        let normalized = self.normalize_bool(cond);

        if normalized.always_false {
            self.unsat = true;
            self.path_cond.push(BoolExpr::Bool(false));
            return self;
        }

        // Flatten conjunctions early after normalization.
        if let BoolExpr::And(vs) = normalized.expr {
            let mut cur = self;
            for c in vs {
                cur = cur.with_pc(c);
                if cur.unsat {
                    break;
                }
            }
            return cur;
        }

        // Drop trivial truths to keep path_cond short.
        if normalized.always_true {
            return self;
        }

        if self.unsat {
            return self;
        }
        if self.is_contradiction(&normalized.expr) {
            self.unsat = true;
            self.path_cond.push(BoolExpr::Bool(false));
            return self;
        }

        // Harvest simple range hints attached to individual variables.
        match &normalized.expr {
            BoolExpr::Range {
                value, min, max, ..
            } => {
                self.record_range_hint(value, *min, *max);
            }
            BoolExpr::Eq(a, b) => {
                self.record_eq_hint(a, b);
                self.record_eq_hint(b, a);
            }
            _ => {}
        };
        self.path_cond.push(normalized.expr);
        self.maybe_compact_path_cond();
        self
    }

    /// Normalizes a Boolean condition for early contradiction detection.
    /// Performs light simplification (flattening, constant folding, range/equality propagation)
    /// without invoking the solver.
    fn normalize_bool(&self, cond: BoolExpr) -> BoolSimplifyResult {
        let mut hints = self.range_hints.clone();
        self.simplify_bool_expr(cond, &mut hints)
    }

    fn simplify_bool_expr(
        &self,
        cond: BoolExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        match cond {
            BoolExpr::Bool(b) => BoolSimplifyResult::from_constant(b),
            BoolExpr::Not(inner) => {
                let res = self.simplify_bool_expr(*inner, hints);
                if res.always_true {
                    BoolSimplifyResult::from_constant(false)
                } else if res.always_false {
                    BoolSimplifyResult::from_constant(true)
                } else {
                    BoolSimplifyResult::from_expr(BoolExpr::Not(Box::new(res.expr)))
                }
            }
            BoolExpr::And(vs) => {
                let mut flat = Vec::new();
                for v in vs {
                    let res = self.simplify_bool_expr(v, hints);
                    if res.always_false {
                        return BoolSimplifyResult::from_constant(false);
                    }
                    if res.always_true {
                        continue;
                    }
                    flat.push(res.expr);
                }
                if flat.is_empty() {
                    BoolSimplifyResult::from_constant(true)
                } else if flat.len() == 1 {
                    BoolSimplifyResult::from_expr(flat.into_iter().next().unwrap())
                } else {
                    BoolSimplifyResult::from_expr(BoolExpr::And(flat))
                }
            }
            BoolExpr::Or(vs) => {
                let mut flat = Vec::new();
                let base_hints = hints.clone();
                for v in vs {
                    let mut branch_hints = base_hints.clone();
                    let res = self.simplify_bool_expr(v, &mut branch_hints);
                    if res.always_true {
                        return BoolSimplifyResult::from_constant(true);
                    }
                    if res.always_false {
                        continue;
                    }
                    flat.push(res.expr);
                }
                if flat.is_empty() {
                    BoolSimplifyResult::from_constant(false)
                } else if flat.len() == 1 {
                    BoolSimplifyResult::from_expr(flat.into_iter().next().unwrap())
                } else {
                    BoolSimplifyResult::from_expr(BoolExpr::Or(flat))
                }
            }
            BoolExpr::Range {
                value,
                min,
                max,
                bits,
            } => self.simplify_range(value, min, max, bits, hints),
            BoolExpr::Eq(a, b) => self.simplify_eq(a, b, hints),
            BoolExpr::Ne(a, b) => self.simplify_ne(a, b, hints),
            BoolExpr::Le(a, b) => self.simplify_le(a, b, hints),
            BoolExpr::Lt(a, b) => self.simplify_lt(a, b, hints),
            BoolExpr::Ge(a, b) => self.simplify_ge(a, b, hints),
            BoolExpr::Gt(a, b) => self.simplify_gt(a, b, hints),
        }
    }

    fn simplify_range(
        &self,
        value: SymExpr,
        min: i128,
        max: i128,
        bits: Option<usize>,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if min > max {
            return BoolSimplifyResult::from_constant(false);
        }

        if let SymExpr::Int(k) = value {
            return BoolSimplifyResult::from_constant(k >= min && k <= max);
        }

        if let SymExpr::Var(name, _) = &value {
            let (contradiction, implied) = tighten_range(hints, name, min, max);
            if contradiction {
                return BoolSimplifyResult::from_constant(false);
            }
            if implied {
                return BoolSimplifyResult::from_constant(true);
            }
        }

        BoolSimplifyResult::from_expr(BoolExpr::Range {
            value,
            min,
            max,
            bits,
        })
    }

    fn simplify_eq(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if a == b {
            return BoolSimplifyResult::from_constant(true);
        }

        match (&a, &b) {
            (SymExpr::Int(x), SymExpr::Int(y)) => return BoolSimplifyResult::from_constant(x == y),
            (SymExpr::Var(name, _), SymExpr::Int(k)) => {
                let (contradiction, implied) = tighten_range(hints, name, *k, *k);
                if contradiction {
                    return BoolSimplifyResult::from_constant(false);
                }
                if implied {
                    return BoolSimplifyResult::from_constant(true);
                }
            }
            (SymExpr::Int(k), SymExpr::Var(name, _)) => {
                let (contradiction, implied) = tighten_range(hints, name, *k, *k);
                if contradiction {
                    return BoolSimplifyResult::from_constant(false);
                }
                if implied {
                    return BoolSimplifyResult::from_constant(true);
                }
            }
            _ => {}
        }

        BoolSimplifyResult::from_expr(BoolExpr::Eq(a, b))
    }

    fn simplify_ne(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if a == b {
            return BoolSimplifyResult::from_constant(false);
        }

        match (&a, &b) {
            (SymExpr::Int(x), SymExpr::Int(y)) => return BoolSimplifyResult::from_constant(x != y),
            (SymExpr::Var(name, _), SymExpr::Int(k)) => {
                if let Some((lo, hi)) = hints.get(name) {
                    if *lo == *hi {
                        return BoolSimplifyResult::from_constant(*lo != *k);
                    }
                    if *k < *lo || *k > *hi {
                        return BoolSimplifyResult::from_constant(true);
                    }
                }
            }
            (SymExpr::Int(k), SymExpr::Var(name, _)) => {
                if let Some((lo, hi)) = hints.get(name) {
                    if *lo == *hi {
                        return BoolSimplifyResult::from_constant(*lo != *k);
                    }
                    if *k < *lo || *k > *hi {
                        return BoolSimplifyResult::from_constant(true);
                    }
                }
            }
            _ => {}
        }

        BoolSimplifyResult::from_expr(BoolExpr::Ne(a, b))
    }

    fn simplify_le(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if let (SymExpr::Int(x), SymExpr::Int(y)) = (&a, &b) {
            return BoolSimplifyResult::from_constant(x <= y);
        }

        if let (SymExpr::Var(name, _), SymExpr::Int(k)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *lo > *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *hi <= *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        if let (SymExpr::Int(k), SymExpr::Var(name, _)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *hi < *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *lo >= *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        BoolSimplifyResult::from_expr(BoolExpr::Le(a, b))
    }

    fn simplify_lt(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if let (SymExpr::Int(x), SymExpr::Int(y)) = (&a, &b) {
            return BoolSimplifyResult::from_constant(x < y);
        }

        if let (SymExpr::Var(name, _), SymExpr::Int(k)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *lo >= *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *hi < *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        if let (SymExpr::Int(k), SymExpr::Var(name, _)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *hi <= *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *lo > *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        BoolSimplifyResult::from_expr(BoolExpr::Lt(a, b))
    }

    fn simplify_ge(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if let (SymExpr::Int(x), SymExpr::Int(y)) = (&a, &b) {
            return BoolSimplifyResult::from_constant(x >= y);
        }

        if let (SymExpr::Var(name, _), SymExpr::Int(k)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *hi < *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *lo >= *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        if let (SymExpr::Int(k), SymExpr::Var(name, _)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *lo > *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *hi <= *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        BoolSimplifyResult::from_expr(BoolExpr::Ge(a, b))
    }

    fn simplify_gt(
        &self,
        a: SymExpr,
        b: SymExpr,
        hints: &mut HashMap<String, (i128, i128)>,
    ) -> BoolSimplifyResult {
        if let (SymExpr::Int(x), SymExpr::Int(y)) = (&a, &b) {
            return BoolSimplifyResult::from_constant(x > y);
        }

        if let (SymExpr::Var(name, _), SymExpr::Int(k)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *hi <= *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *lo > *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        if let (SymExpr::Int(k), SymExpr::Var(name, _)) = (&a, &b)
            && let Some((lo, hi)) = hints.get(name) {
                if *lo >= *k {
                    return BoolSimplifyResult::from_constant(false);
                }
                if *hi < *k {
                    return BoolSimplifyResult::from_constant(true);
                }
            }

        BoolSimplifyResult::from_expr(BoolExpr::Gt(a, b))
    }

    fn cache_key_for_expr(value: &SymExpr) -> String {
        match value {
            SymExpr::Var(name, _) => format!("var:{name}"),
            other => format!("expr:{other:?}"),
        }
    }

    pub(crate) fn cache_key_for_expr_normalized(value: &SymExpr) -> String {
        let norm = Self::canonicalize_symexpr(value);
        format!("{norm:?}")
    }

    fn canonicalize_symexpr(e: &SymExpr) -> SymExpr {
        match e {
            SymExpr::Neg(x) => SymExpr::Neg(Box::new(Self::canonicalize_symexpr(x))),
            SymExpr::Add(vs) => {
                let mut items: Vec<_> = vs.iter().map(Self::canonicalize_symexpr).collect();
                items.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
                match items.len() {
                    0 => SymExpr::Int(0),
                    1 => items.pop().unwrap(),
                    _ => SymExpr::Add(items),
                }
            }
            SymExpr::Mul(vs) => {
                let mut items: Vec<_> = vs.iter().map(Self::canonicalize_symexpr).collect();
                items.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
                match items.len() {
                    0 => SymExpr::Int(1),
                    1 => items.pop().unwrap(),
                    _ => SymExpr::Mul(items),
                }
            }
            SymExpr::Sub(a, b) => SymExpr::Sub(
                Box::new(Self::canonicalize_symexpr(a)),
                Box::new(Self::canonicalize_symexpr(b)),
            ),
            SymExpr::Div(a, b) => SymExpr::Div(
                Box::new(Self::canonicalize_symexpr(a)),
                Box::new(Self::canonicalize_symexpr(b)),
            ),
            SymExpr::Ite(c, t, f) => SymExpr::Ite(
                Box::new(Self::canonicalize_bool_expr(c)),
                Box::new(Self::canonicalize_symexpr(t)),
                Box::new(Self::canonicalize_symexpr(f)),
            ),
            SymExpr::Mod(a, b) => SymExpr::Mod(
                Box::new(Self::canonicalize_symexpr(a)),
                Box::new(Self::canonicalize_symexpr(b)),
            ),
            other => other.clone(),
        }
    }

    fn canonicalize_bool_expr(b: &BoolExpr) -> BoolExpr {
        match b {
            BoolExpr::Not(inner) => BoolExpr::Not(Box::new(Self::canonicalize_bool_expr(inner))),
            BoolExpr::And(vs) => {
                let mut items: Vec<_> = vs.iter().map(Self::canonicalize_bool_expr).collect();
                items.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
                match items.len() {
                    0 => BoolExpr::Bool(true),
                    1 => items.pop().unwrap(),
                    _ => BoolExpr::And(items),
                }
            }
            BoolExpr::Or(vs) => {
                let mut items: Vec<_> = vs.iter().map(Self::canonicalize_bool_expr).collect();
                items.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
                match items.len() {
                    0 => BoolExpr::Bool(false),
                    1 => items.pop().unwrap(),
                    _ => BoolExpr::Or(items),
                }
            }
            BoolExpr::Eq(a, b) => {
                BoolExpr::Eq(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Ne(a, b) => {
                BoolExpr::Ne(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Le(a, b) => {
                BoolExpr::Le(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Lt(a, b) => {
                BoolExpr::Lt(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Ge(a, b) => {
                BoolExpr::Ge(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Gt(a, b) => {
                BoolExpr::Gt(Self::canonicalize_symexpr(a), Self::canonicalize_symexpr(b))
            }
            BoolExpr::Range {
                value,
                min,
                max,
                bits,
            } => BoolExpr::Range {
                value: Self::canonicalize_symexpr(value),
                min: *min,
                max: *max,
                bits: *bits,
            },
            other => other.clone(),
        }
    }

    fn record_range_hint(&mut self, value: &SymExpr, min: i128, max: i128) {
        if min > max {
            return;
        }
        if let Some(name) = Self::project_var_name(value) {
            self.range_hints
                .entry(name)
                .and_modify(|(lo, hi)| {
                    let new_lo = std::cmp::max(*lo, min);
                    let new_hi = std::cmp::min(*hi, max);
                    if new_lo <= new_hi {
                        *lo = new_lo;
                        *hi = new_hi;
                    } else {
                        self.unsat = true;
                    }
                })
                .or_insert((min, max));
        }
    }

    fn record_eq_hint(&mut self, a: &SymExpr, b: &SymExpr) {
        if let (Some(name), SymExpr::Int(k)) = (Self::project_var_name(a), b) {
            self.record_range_hint(&SymExpr::Var(name, SymType::Bool), *k, *k);
        }
    }

    pub(crate) fn byte_op_cache_key(
        op: &str,
        out: &SymExpr,
        lhs: &SymExpr,
        rhs: &SymExpr,
    ) -> String {
        format!(
            "{}|{}|{}|{}",
            op,
            Self::cache_key_for_expr_normalized(out),
            Self::cache_key_for_expr_normalized(lhs),
            Self::cache_key_for_expr_normalized(rhs)
        )
    }

    pub(crate) fn is_byte_op_cached(&self, key: &str) -> bool {
        self.byte_op_cache.contains(key)
    }

    pub(crate) fn mark_byte_op_cached(mut self, key: String) -> Self {
        self.byte_op_cache.insert(key);
        self
    }

    /// Periodically compact the accumulated path condition by dropping tautologies,
    /// merging duplicates, and short-circuiting on false.
    fn maybe_compact_path_cond(&mut self) {
        const PATH_COND_COMPACT_THRESHOLD: usize = 64;
        if self.path_cond.len() < PATH_COND_COMPACT_THRESHOLD {
            return;
        }
        let mut seen: HashSet<String> = HashSet::new();
        let mut compacted = Vec::new();
        for cond in self.path_cond.drain(..) {
            match cond {
                BoolExpr::Bool(true) => continue,
                BoolExpr::Bool(false) => {
                    self.unsat = true;
                    compacted.clear();
                    compacted.push(BoolExpr::Bool(false));
                    break;
                }
                other => {
                    let key = format!("{:?}", Self::canonicalize_bool_expr(&other));
                    if seen.insert(key) {
                        compacted.push(other);
                    }
                }
            }
        }
        self.path_cond = compacted;
    }

    /// Try to extract a canonical variable name from simple projections (bare var,
    /// single-element Add/Mul, or degenerate ite). This lets range hints attach
    /// to field/array projections that are materialized as scalars.
    fn project_var_name(value: &SymExpr) -> Option<String> {
        match value {
            SymExpr::Var(name, _) => Some(name.clone()),
            SymExpr::Add(vs) | SymExpr::Mul(vs) if vs.len() == 1 => Self::project_var_name(&vs[0]),
            SymExpr::Ite(_, t, f) if t == f => Self::project_var_name(t),
            _ => None,
        }
    }

    /// Lookup a recorded range for a variable, if any.
    fn hint_for_var(&self, name: &str) -> Option<(i128, i128)> {
        self.range_hints.get(name).copied()
    }

    /// Conservative range inference for a symbolic expression using recorded hints.
    /// Returns (min, max) if a finite interval can be derived.
    pub fn symexpr_range(&self, e: &SymExpr) -> Option<(i128, i128)> {
        range::symexpr_range(e, |name, _| self.hint_for_var(name))
    }

    /// Ensure a non-field expression is constrained to the canonical field range [0, p-1]
    /// before assigning it into a field-typed destination.
    pub fn ensure_field_range(mut self, value: &SymExpr) -> SymState {
        let already_field = matches!(Self::symexpr_sort(value), Some(SymType::F));
        if already_field {
            return self;
        }

        let needs_guard = match self.symexpr_range(value) {
            Some((lo, hi)) => lo < 0 || hi >= FIELD_MODULUS,
            None => true,
        };

        if needs_guard {
            self = self.with_pc(BoolExpr::Range {
                value: value.clone(),
                min: 0,
                max: FIELD_MODULUS - 1,
                bits: Some(32),
            });
        }

        self
    }

    /// Decompose a u32 value into Boolean bits, reusing prior decompositions of the same value.
    pub fn decompose_u32_bits_cached(
        mut self,
        value: SymExpr,
        prefix: &str,
    ) -> (Vec<SymExpr>, SymState) {
        let key = Self::cache_key_for_expr(&value);
        if let Some(bits) = self.bit_decomp_cache.get(&key) {
            return (bits.clone(), self);
        }

        let mut bits = Vec::with_capacity(32);
        let mut acc = SymExpr::Int(0);
        for i in 0..32 {
            let bit = self.fresh_sym(&format!("{}_{}", prefix, i), SymType::Bool);
            self = self.with_pc(BoolExpr::Range {
                value: bit.clone(),
                min: 0,
                max: 1,
                bits: Some(1),
            });
            acc = acc + bit.clone() * SymExpr::Int(1_i128 << i);
            bits.push(bit);
        }

        self = self.with_pc(BoolExpr::Range {
            value: value.clone(),
            min: 0,
            max: (1_i128 << 32) - 1,
            bits: Some(32),
        });
        self = self.with_pc(value.eq_to(acc));
        self.bit_decomp_cache.insert(key, bits.clone());

        (bits, self)
    }

    /// Materialize a little-endian word decomposition for a u32 value with range constraints.
    fn attach_word_bytes(self, value: SymExpr, hint: &str) -> (SymWord, SymState) {
        let mut state = self;
        let mut bytes = Vec::with_capacity(WORD_BYTES);

        for i in 0..WORD_BYTES {
            let b = state.fresh_sym(&format!("{}_b{}", hint, i), SymType::Uint(8));
            let zero = SymExpr::Int(0);
            let max = SymExpr::Int(255);
            state = state.with_pc(BoolExpr::Range {
                value: b.clone(),
                min: 0,
                max: 255,
                bits: Some(8),
            });
            state = state.with_pc(b.clone().ge(zero));
            state = state.with_pc(b.clone().le(max));
            bytes.push(b);
        }

        // Link bytes back to the surface u32 value using little-endian encoding.
        let factor = SymExpr::Int(256);
        let mut acc = bytes
            .last()
            .cloned()
            .expect("word representation must contain at least one byte");
        for i in (0..bytes.len() - 1).rev() {
            acc = bytes[i].clone() + factor.clone() * acc;
        }
        state = state.with_pc(acc.eq_to(value.clone()));

        (SymWord::new(bytes), state)
    }

    /// Build a scalar value with an optional word-level view according to the symbolic sort.
    pub fn pack_scalar_with_symtype(
        mut self,
        value: SymExpr,
        sty: &SymType,
        hint: &str,
    ) -> (SymValue, SymState) {
        if matches!(sty, SymType::F) {
            self = self.ensure_field_range(&value);
        }

        match sty {
            SymType::Uint(32) => {
                let (word, state) = self.attach_word_bytes(value.clone(), hint);
                let SymWord { bytes } = word;
                (SymValue::with_word(value, bytes), state)
            }
            _ => (SymValue::plain(value), self),
        }
    }

    /// Build a scalar value with an optional word view from a concrete AST type.
    pub fn pack_scalar_for_type(
        self,
        value: SymExpr,
        ty: &Type,
        hint: &str,
    ) -> (SymValue, SymState) {
        let sty = self.type_map(ty).unwrap_or(SymType::F);
        self.pack_scalar_with_symtype(value, &sty, hint)
    }

    /// In-place convenience wrapper to attach a word representation.
    pub fn pack_scalar_with_symtype_mut(
        &mut self,
        value: SymExpr,
        sty: &SymType,
        hint: &str,
    ) -> SymValue {
        let state_clone = self.clone();
        let (val, new_state) = state_clone.pack_scalar_with_symtype(value, sty, hint);
        *self = new_state;
        val
    }

    /// In-place convenience wrapper using a concrete AST type.
    pub fn pack_scalar_for_type_mut(&mut self, value: SymExpr, ty: &Type, hint: &str) -> SymValue {
        let state_clone = self.clone();
        let (val, new_state) = state_clone.pack_scalar_for_type(value, ty, hint);
        *self = new_state;
        val
    }

    /// Append a memory event to the trace and return the updated state.
    pub fn add_memory_event(
        mut self,
        kind: MemoryEventKind,
        clk: SymExpr,
        addr: SymExpr,
        value: SymExpr,
    ) -> Self {
        self.memory_events.push(MemoryEvent {
            kind,
            clk,
            addr,
            value,
        });
        self
    }

    /// View the accumulated memory trace.
    pub fn memory_trace(&self) -> &[MemoryEvent] {
        &self.memory_events
    }

    /// Look up a cached map read by base and keys.
    pub fn find_map_read(
        &self,
        base_id: Option<i64>,
        base_repr: &str,
        clk: &SymExpr,
        addr: &SymExpr,
    ) -> Option<(SymExpr, SymExpr)> {
        let clk_key = Self::cache_key_for_expr_normalized(clk);
        let addr_key = Self::cache_key_for_expr_normalized(addr);
        self.map_reads
            .iter()
            .find(|r| {
                r.base_id == base_id
                    && r.base_repr == base_repr
                    && r.clk_key == clk_key
                    && r.addr_key == addr_key
            })
            .map(|r| (r.clk_prev.clone(), r.value.clone()))
    }

    /// Cache a new map read result.
    pub fn record_map_read(
        mut self,
        base_id: Option<i64>,
        base_repr: String,
        clk: SymExpr,
        addr: SymExpr,
        clk_prev: SymExpr,
        value: SymExpr,
    ) -> Self {
        let clk_key = Self::cache_key_for_expr_normalized(&clk);
        let addr_key = Self::cache_key_for_expr_normalized(&addr);
        self.map_reads.push(MapReadRecord {
            base_id,
            base_repr,
            clk,
            addr,
            clk_prev,
            value,
            clk_key,
            addr_key,
        });
        self
    }

    /// Conjoin all accumulated path conditions; returns `true` if empty.
    pub fn pc(&self) -> BoolExpr {
        BoolExpr::and(self.path_cond.clone())
    }

    /// Set execution status and return the updated state.
    pub fn with_status(mut self, status: ExecStatus) -> Self {
        self.status = status;
        self
    }

    /// State is active.
    pub fn is_active(&self) -> bool {
        matches!(self.status, ExecStatus::Step) && !self.unsat
    }

    /// State is terminal for the current control region (Break/Return).
    pub fn is_terminal(&self) -> bool {
        !matches!(self.status, ExecStatus::Step)
    }

    /// State has already been proven inconsistent.
    pub fn is_inconsistent(&self) -> bool {
        self.unsat
    }

    /// Returns `true` if the given AST expression has field sort.
    pub fn is_field_expr(&self, e: &Expr) -> bool {
        if let Some(ty) = self.infer_expr_type(e) {
            matches!(self.type_map(&ty), Ok(SymType::F))
        } else {
            false
        }
    }

    /// Lightweight contradiction check using recorded hints and constant folding.
    fn is_contradiction(&self, cond: &BoolExpr) -> bool {
        match cond {
            BoolExpr::Bool(false) => true,
            BoolExpr::Range {
                value, min, max, ..
            } => {
                if min > max {
                    return true;
                }
                if let SymExpr::Var(name, _) = value
                    && let Some((lo, hi)) = self.range_hints.get(name) {
                        return *max < *lo || *min > *hi;
                    }
                false
            }
            BoolExpr::Eq(a, b) => match (a, b) {
                (SymExpr::Int(x), SymExpr::Int(y)) => x != y,
                (SymExpr::Var(name, _), SymExpr::Int(k)) => {
                    if let Some((lo, hi)) = self.range_hints.get(name) {
                        *k < *lo || *k > *hi
                    } else {
                        false
                    }
                }
                (SymExpr::Int(k), SymExpr::Var(name, _)) => {
                    if let Some((lo, hi)) = self.range_hints.get(name) {
                        *k < *lo || *k > *hi
                    } else {
                        false
                    }
                }
                _ => false,
            },
            BoolExpr::Ne(a, b) => match (a, b) {
                (SymExpr::Int(x), SymExpr::Int(y)) => x == y,
                _ => false,
            },
            _ => false,
        }
    }

    /// Tries to infer expression type using dynamic store information first,
    /// then falls back to static context-based inference.
    pub fn infer_expr_type(&self, e: &Expr) -> Option<Type> {
        // Prefer dynamic sort from a materialized scalar node.
        if let Some(node) = self.query_expr_node(e)
            && let StoreNode::Scalar(se) = node
                && let Some(sty) = Self::symexpr_sort(&se.surface) {
                    return Some(self.ctx.sym_type_to_builtin_type(&sty));
                }

        // Fallback to static inference on ids and builtin types.
        self.ctx.infer_expr_type_static(e)
    }

    /// Returns the symbolic sort for simple scalar expressions.
    fn symexpr_sort(se: &SymExpr) -> Option<SymType> {
        match se {
            SymExpr::Var(_, sty) => Some(sty.clone()),
            SymExpr::Int(k) => {
                if *k < 0 {
                    // Signed literals: pick a small signed width if possible.
                    if *k >= i32::MIN as i128 {
                        Some(SymType::Int(32))
                    } else {
                        Some(SymType::Int(64))
                    }
                } else {
                    let v = *k as u128;
                    // 0/1 as Bool.
                    if v <= 1 {
                        Some(SymType::Bool)
                    } else if v <= 3 {
                        // 2..=3
                        Some(SymType::Uint(2))
                    } else if v <= 15 {
                        Some(SymType::Uint(4))
                    } else if v <= 255 {
                        Some(SymType::Uint(8))
                    } else if v <= 65_535 {
                        Some(SymType::Uint(16))
                    } else if v <= u32::MAX as u128 {
                        // Up to u32 range use uint(32).
                        Some(SymType::Uint(32))
                    } else {
                        // Larger constants fall back to uint(64).
                        Some(SymType::Uint(64))
                    }
                }
            }
            SymExpr::Ite(_, t, f) => {
                // Simple join: require both branches to have the same sort.
                let st = Self::symexpr_sort(t)?;
                let sf = Self::symexpr_sort(f)?;
                if st == sf { Some(st) } else { None }
            }
            SymExpr::Mul(vs) => {
                // Very conservative: if all factors share the same sort, keep it; else None.
                let mut it = vs.iter();
                let first = it.next()?;
                let s0 = Self::symexpr_sort(first)?;
                for x in it {
                    if Self::symexpr_sort(x)? != s0 {
                        return None;
                    }
                }
                Some(s0)
            }
            // Extend as needed for other constructors.
            _ => None,
        }
    }

    pub fn query_expr_node(&self, e: &Expr) -> Option<&StoreNode> {
        match e {
            Expr::Path { ref_id, .. } => {
                let vid = (*ref_id)?;
                self.store.get(vid)
            }
            Expr::Field { base, name, .. } => {
                let sid = match self.infer_expr_type(base.as_ref()) {
                    Some(Type::Path {
                        ref_id: Some(sid), ..
                    }) => sid,
                    _ => return None,
                };
                let fid = self.ctx.field_id_of(sid, name)?;
                let parent = self.query_expr_node(base.as_ref())?;
                match parent {
                    StoreNode::Struct { fields } => fields.get(&fid),
                    _ => None,
                }
            }
            Expr::Index(base, idx) => {
                let idx_val = eval_index_const_or_err(&self.ctx, Some(&self.store), idx)
                    .unwrap_or_else(|| {
                        panic!(
                            "array index must be a concrete integer literal or constant identifier"
                        )
                    });
                let parent = self.query_expr_node(base.as_ref())?;
                match parent {
                    StoreNode::Array { elems, .. } => elems.get(&idx_val),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Map an AST type to a symbolic scalar sort using Context's builtin mapping.
    /// Only builtin scalars are mappable; structs/arrays/functions are rejected.
    pub fn type_map(&self, ty: &Type) -> Result<SymType, String> {
        match self.ctx.builtin_type_to_sym_type(ty) {
            Some(sty) => Ok(sty),
            None => Err(format!("cannot map type `{:?}` to SymType", ty)),
        }
    }

    pub fn fresh_sym(&mut self, hint: &str, ty: SymType) -> SymExpr {
        let id = self.fresh;
        self.fresh += 1;
        // Solver backends are responsible for range constraints based on SymType.
        SymExpr::Var(format!("{}_{}", hint, id), ty)
    }

    /// Initializes parameters with fresh symbols.
    /// For `self`, when a struct id is given, materializes its fields as fresh scalars.
    pub fn init_params_for_func(&mut self, func: &Func, self_struct_id: Option<i64>) {
        for p in &func.params {
            match p {
                Param::SelfParam { id } => {
                    if let Some(vid) = *id {
                        let node = if let Some(sid) = self_struct_id {
                            // Recursively materialize fields with correct static types.
                            self.materialize_struct_node(sid, "self")
                        } else {
                            // Unknown `self` shape; keep an empty struct placeholder.
                            StoreNode::structure()
                        };
                        self.store = self.store.clone().set(vid, node);
                    }
                }
                Param::Typed { id, name, ty, .. } => {
                    if let Some(vid) = *id {
                        let node = self.alloc_node_for_type(name, ty);
                        self.store = self.store.clone().set(vid, node);
                    }
                }
            }
        }
    }

    /// Bind parameters to existing store nodes when provided, allocating any missing ones.
    /// This is useful for reusing symbols across multiple executions (e.g., executor -> chips).
    pub fn bind_params_for_func(
        mut self,
        func: &Func,
        bindings: &HashMap<String, StoreNode>,
        self_struct_id: Option<i64>,
    ) -> Self {
        for p in &func.params {
            match p {
                Param::SelfParam { id } => {
                    if let Some(vid) = *id {
                        if let Some(node) = bindings.get("self") {
                            self.store = self.store.set(vid, node.clone());
                        } else if !self.store.vars.contains_key(&vid) {
                            let node = if let Some(sid) = self_struct_id {
                                self.materialize_struct_node(sid, "self")
                            } else {
                                StoreNode::structure()
                            };
                            self.store = self.store.set(vid, node);
                        }
                    }
                }
                Param::Typed { id, name, ty, .. } => {
                    if let Some(vid) = *id {
                        if let Some(node) = bindings.get(name) {
                            self.store = self.store.set(vid, node.clone());
                        } else if !self.store.vars.contains_key(&vid) {
                            let node = self.alloc_node_for_type(name, ty);
                            self.store = self.store.set(vid, node);
                        }
                    }
                }
            }
        }
        self
    }

    /// Fetch the store node bound to a parameter (by name) after execution.
    pub fn param_node(&self, func: &Func, name: &str) -> Option<&StoreNode> {
        for p in &func.params {
            match p {
                Param::SelfParam { id } if name == "self" => {
                    if let Some(vid) = *id
                        && let Some(node) = self.store.get(vid) {
                            return Some(node);
                        }
                }
                Param::Typed {
                    id, name: pname, ..
                } if pname == name => {
                    if let Some(vid) = *id
                        && let Some(node) = self.store.get(vid) {
                            return Some(node);
                        }
                }
                _ => {}
            }
        }
        None
    }

    /// Materialize a struct into a persistent node with recursively-typed fields.
    /// Each field node is allocated according to its declared static type.
    fn materialize_struct_node(&mut self, struct_id: i64, prefix: &str) -> StoreNode {
        // Snapshot (field_id, name, type) to avoid conflicting borrows during recursive allocation.
        let pairs: Vec<(i64, String, Type)> = {
            let mut out = Vec::new();
            if let Some(members) = self.ctx.struct_members(struct_id) {
                for (name, mi) in members {
                    if let Some(fid) = mi.as_field_id() {
                        let fty = self
                            .ctx
                            .query_type(fid)
                            .unwrap_or_else(|| panic!("missing static type for field_id {}", fid))
                            .clone();
                        out.push((fid, name.clone(), fty));
                    }
                }
            }
            out
        };

        // Allocate children recursively using the snapshot.
        let mut node = StoreNode::structure();
        if let StoreNode::Struct { fields } = &mut node {
            let mut acc = fields.clone(); // persistent map semantics
            for (fid, name, fty) in pairs {
                let child = self.alloc_node_for_type(&format!("{prefix}_{name}"), &fty);
                acc.insert(fid, child);
            }
            *fields = acc;
        }
        node
    }

    /// Allocates a default node according to the declared type (recursive over struct fields).
    fn alloc_node_for_type(&mut self, hint: &str, ty: &Type) -> StoreNode {
        match ty {
            // Strict name-based classification (struct_index only).
            Type::Path { .. } => {
                match self.ctx.classify_type(ty) {
                    Ok(PathKind::Builtin) => {
                        // Builtins are modeled as scalars with precise sorts.
                        let sty = self
                            .type_map(ty)
                            .unwrap_or_else(|e| panic!("builtin type mapping failed: {e}"));
                        let surface = self.fresh_sym(hint, sty.clone());
                        let val = self.pack_scalar_with_symtype_mut(surface, &sty, hint);
                        StoreNode::scalar(val)
                    }
                    Ok(PathKind::Enum(enum_id)) => {
                        // Enums are backed by integers with a configurable width.
                        let sty = self.ctx.enum_sym_type(enum_id);
                        let surface = self.fresh_sym(hint, sty.clone());
                        let val = self.pack_scalar_with_symtype_mut(surface, &sty, hint);
                        StoreNode::scalar(val)
                    }
                    Ok(PathKind::Struct(struct_id)) => {
                        // Structs are materialized recursively by field static types.
                        self.materialize_struct_node(struct_id, hint)
                    }
                    Err(msg) => {
                        // Invalid type name should be surfaced early.
                        panic!("invalid Type::Path `{hint}`: {msg}");
                    }
                }
            }
            Type::Array(inner, len_expr) => {
                // Try to resolve the array length at allocation time.
                let len: Option<usize> = eval_index_const_or_err(&self.ctx, None, len_expr);

                match len {
                    // Known length: eagerly materialize each element.
                    Some(n) => {
                        let mut elems = IMap::new();
                        for i in 0..n {
                            let child = self.alloc_node_for_type(&format!("{hint}_{i}"), inner);
                            elems.insert(i, child);
                        }
                        StoreNode::Array {
                            len: Some(n),
                            elems,
                        }
                    }

                    // Unknown length: keep an empty array shell; any indexed access
                    // with constant index will still panic if element was never written.
                    None => StoreNode::array(None),
                }
            }

            // Map types are treated as opaque scalars; their contents are not modeled symbolically.
            Type::Map { .. } => {
                let surface = self.fresh_sym(&format!("{hint}_map"), SymType::F);
                let val = self.pack_scalar_with_symtype_mut(surface, &SymType::F, hint);
                StoreNode::scalar(val)
            }

            Type::Tuple(elems) => {
                let mut children = IMap::new();
                for (i, elem_ty) in elems.iter().enumerate() {
                    let child = self.alloc_node_for_type(&format!("{hint}_{i}"), elem_ty);
                    children.insert(i, child);
                }
                StoreNode::Array {
                    len: Some(elems.len()),
                    elems: children,
                }
            }

            // Function types are not allowed in value allocation; report as unimplemented.
            Type::Function { .. } => {
                unimplemented!(
                    "alloc_node_for_type: function types are unsupported for value allocation (hint: {hint})"
                );
            }
        }
    }
}
