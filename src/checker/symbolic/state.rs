use im::HashMap as IMap;
use std::collections::BTreeSet;
use std::rc::Rc;

use crate::ast::*;
use crate::checker::symbolic::context::{Context, PathKind};
use crate::checker::symbolic::eval_index_const_or_err;
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

/// Symbolic state with path condition and persistent store.
#[derive(Clone, Debug)]
pub struct SymState {
    pub ctx: Rc<Context>,
    pub path_cond: Vec<BoolExpr>,
    pub store: Store,
    pub status: ExecStatus,
    fresh: usize,
}

impl SymState {
    pub fn new(ctx: Rc<Context>) -> Self {
        Self {
            ctx,
            path_cond: Vec::new(),
            store: Store::default(),
            status: ExecStatus::Step,
            fresh: 0,
        }
    }

    /// Return a new state with an additional path constraint appended.
    pub fn with_pc(mut self, cond: BoolExpr) -> Self {
        self.path_cond.push(cond);
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

    pub fn query_expr_node(&self, e: &Expr) -> Option<&StoreNode> {
        match e {
            Expr::Path { ref_id, .. } => {
                let vid = (*ref_id)?;
                self.store.get(vid)
            }
            Expr::Field { base, name, .. } => {
                let sid = match self.ctx.infer_expr_type(base.as_ref()) {
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

    /// Map an AST type to a symbolic sort for variable creation.
    /// Only builtin scalars are mappable; structs/arrays/functions are not.
    pub fn type_map(&self, ty: &Type) -> Result<SymType, String> {
        match self.ctx.classify_type(ty) {
            Ok(PathKind::Builtin) => {
                // Parse terminal name: "bool" | "field" | "uN" | "iN".
                let Type::Path { segments, .. } = ty else {
                    unreachable!("classify_type returned Builtin for non-Path");
                };
                let last = segments
                    .last()
                    .expect("non-empty path")
                    .to_ascii_lowercase();
                if last == "bool" {
                    return Ok(SymType::Bool);
                }
                if last == "field" || last == "f" {
                    return Ok(SymType::F);
                }
                if let Some(bits) = last.strip_prefix('u') {
                    let w = bits
                        .parse::<usize>()
                        .map_err(|_| format!("invalid uint width in type name: {}", last))?;
                    return Ok(SymType::Uint(w));
                }
                if let Some(bits) = last.strip_prefix('i') {
                    let w = bits
                        .parse::<usize>()
                        .map_err(|_| format!("invalid int width in type name: {}", last))?;
                    return Ok(SymType::Int(w));
                }
                Err(format!("unknown builtin type name: {}", last))
            }
            Ok(PathKind::Struct(_sid)) => {
                // Composite types do not map to a scalar sort.
                Err("cannot map struct type to SymType".to_string())
            }
            Err(e) => Err(e),
        }
    }

    pub fn fresh_sym(&mut self, hint: &str, ty: SymType) -> SymExpr {
        let id = self.fresh;
        self.fresh += 1;
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
                Param::Typed { id, name, ty } => {
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
                // Length must be constant at runtime for indexing; unknown is allowed at allocation.
                let len: Option<usize> = eval_index_const_or_err(&self.ctx, None, len_expr);
                let _ = &**inner; // elements are lazily materialized upon indexed writes/reads
                StoreNode::array(len)
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
