use im::HashMap as IMap;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use crate::ast::*;
use crate::checker::symbolic::context::{Context, PathKind};
use crate::checker::symbolic::eval_index_const_or_err;
use crate::checker::symbolic::expr::FIELD_MODULUS;
use crate::checker::symbolic::expr::{BoolExpr, SymExpr, SymType};

/// Persistent store node for symbolic memory.
#[derive(Clone, Debug)]
pub enum StoreNode {
    /// Scalar expression.
    Scalar(SymExpr),

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
    fn scalar(e: SymExpr) -> Self {
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
                out.push((a.clone(), b.clone()));
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
    pub fn query_scalar(&self, e: &Expr) -> Option<SymExpr> {
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
    range_hints: HashMap<String, (i128, i128)>,
    fresh: usize,
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
            range_hints: HashMap::new(),
            fresh: 0,
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
        // Harvest simple range hints attached to individual variables.
        match &cond {
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
        self.path_cond.push(cond);
        self
    }

    fn cache_key_for_expr(value: &SymExpr) -> String {
        match value {
            SymExpr::Var(name, _) => format!("var:{name}"),
            other => format!("expr:{other:?}"),
        }
    }

    fn record_range_hint(&mut self, value: &SymExpr, min: i128, max: i128) {
        if min > max {
            return;
        }
        if let SymExpr::Var(name, _) = value {
            self.range_hints
                .entry(name.clone())
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
    }

    fn record_eq_hint(&mut self, a: &SymExpr, b: &SymExpr) {
        if let (SymExpr::Var(name, _), SymExpr::Int(k)) = (a, b) {
            self.record_range_hint(&SymExpr::Var(name.clone(), SymType::Bool), *k, *k);
        }
    }

    /// Lookup a recorded range for a variable, if any.
    fn hint_for_var(&self, name: &str) -> Option<(i128, i128)> {
        self.range_hints.get(name).copied()
    }

    fn symtype_range(sty: &SymType) -> Option<(i128, i128)> {
        match *sty {
            SymType::Bool => Some((0, 1)),
            SymType::Uint(w) if w > 0 && w < 127 => {
                let max = 1_i128.checked_shl(w as u32)?.saturating_sub(1);
                Some((0, max))
            }
            SymType::Int(w) if w > 0 && w < 127 => {
                let hi = 1_i128.checked_shl((w - 1) as u32)?.saturating_sub(1);
                let lo = -(1_i128.checked_shl((w - 1) as u32)?);
                Some((lo, hi))
            }
            SymType::F => Some((0, FIELD_MODULUS - 1)),
            _ => None,
        }
    }

    fn range_add(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
        a.0.checked_add(b.0)
            .and_then(|lo| a.1.checked_add(b.1).map(|hi| (lo, hi)))
    }

    fn range_sub(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
        a.0.checked_sub(b.1)
            .and_then(|lo| a.1.checked_sub(b.0).map(|hi| (lo, hi)))
    }

    fn range_mul(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
        let cands = [
            a.0.checked_mul(b.0)?,
            a.0.checked_mul(b.1)?,
            a.1.checked_mul(b.0)?,
            a.1.checked_mul(b.1)?,
        ];
        let lo = *cands.iter().min()?;
        let hi = *cands.iter().max()?;
        Some((lo, hi))
    }

    /// Conservative range inference for a symbolic expression using recorded hints.
    /// Returns (min, max) if a finite interval can be derived.
    pub fn symexpr_range(&self, e: &SymExpr) -> Option<(i128, i128)> {
        match e {
            SymExpr::Int(k) => Some((*k, *k)),
            SymExpr::Var(name, sty) => {
                if let Some(h) = self.hint_for_var(name) {
                    return Some(h);
                }
                Self::symtype_range(sty)
            }
            SymExpr::Neg(inner) => {
                let (lo, hi) = self.symexpr_range(inner)?;
                Some((-hi, -lo))
            }
            SymExpr::Add(xs) => {
                let mut acc = Some((0_i128, 0_i128));
                for x in xs {
                    let xr = self.symexpr_range(x)?;
                    acc = acc.and_then(|a| Self::range_add(a, xr));
                }
                acc
            }
            SymExpr::Mul(xs) => {
                let mut it = xs.iter();
                let first = self.symexpr_range(it.next()?)?;
                let mut acc = first;
                for x in it {
                    let xr = self.symexpr_range(x)?;
                    acc = match Self::range_mul(acc, xr) {
                        Some(r) => r,
                        None => return None,
                    };
                }
                Some(acc)
            }
            SymExpr::Sub(a, b) => {
                let ra = self.symexpr_range(a)?;
                let rb = self.symexpr_range(b)?;
                Self::range_sub(ra, rb)
            }
            SymExpr::Div(a, b) => {
                // Very conservative: if divisor range straddles 0 or is unknown, give up.
                let ra = self.symexpr_range(a)?;
                let rb = self.symexpr_range(b)?;
                if rb.0 <= 0 && rb.1 >= 0 {
                    return None;
                }
                // Use bounds via endpoints.
                let cands = [
                    ra.0.checked_div(rb.0)?,
                    ra.0.checked_div(rb.1)?,
                    ra.1.checked_div(rb.0)?,
                    ra.1.checked_div(rb.1)?,
                ];
                let lo = *cands.iter().min()?;
                let hi = *cands.iter().max()?;
                Some((lo, hi))
            }
            SymExpr::Ite(_, t, e) => {
                let rt = self.symexpr_range(t)?;
                let re = self.symexpr_range(e)?;
                Some((std::cmp::min(rt.0, re.0), std::cmp::max(rt.1, re.1)))
            }
            SymExpr::Mod(_, m) => {
                if let SymExpr::Int(k) = **m {
                    if k > 0 {
                        return Some((0, k - 1));
                    }
                }
                None
            }
        }
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
        self.map_reads
            .iter()
            .find(|r| {
                r.base_id == base_id && r.base_repr == base_repr && r.clk == *clk && r.addr == *addr
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
        self.map_reads.push(MapReadRecord {
            base_id,
            base_repr,
            clk,
            addr,
            clk_prev,
            value,
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
        matches!(self.status, ExecStatus::Step)
    }

    /// State is terminal for the current control region (Break/Return).
    pub fn is_terminal(&self) -> bool {
        !matches!(self.status, ExecStatus::Step)
    }

    /// Returns `true` if the given AST expression has field sort.
    pub fn is_field_expr(&self, e: &Expr) -> bool {
        if let Some(ty) = self.infer_expr_type(e) {
            matches!(self.type_map(&ty), Ok(SymType::F))
        } else {
            false
        }
    }

    /// Tries to infer expression type using dynamic store information first,
    /// then falls back to static context-based inference.
    pub fn infer_expr_type(&self, e: &Expr) -> Option<Type> {
        // Prefer dynamic sort from a materialized scalar node.
        if let Some(node) = self.query_expr_node(e) {
            if let StoreNode::Scalar(se) = node {
                if let Some(sty) = Self::symexpr_sort(se) {
                    return Some(self.ctx.sym_type_to_builtin_type(&sty));
                }
            }
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
                        StoreNode::scalar(self.fresh_sym(hint, sty))
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
                StoreNode::scalar(self.fresh_sym(&format!("{hint}_map"), SymType::F))
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
