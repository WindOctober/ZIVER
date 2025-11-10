use im::HashMap as IMap;
use std::rc::Rc;

use crate::ast::*;
use crate::checker::symbolic::context::{Context, PathKind};
use crate::checker::symbolic::eval_len_const_or_err;
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
}

/// Symbolic state with path condition and persistent store.
#[derive(Clone, Debug)]
pub struct SymState {
    pub ctx: Rc<Context>,
    pub path_cond: BoolExpr,
    pub store: Store,
    fresh: usize,
}

impl SymState {
    pub fn new(ctx: Rc<Context>) -> Self {
        Self {
            ctx,
            path_cond: BoolExpr::Bool(true),
            store: Store::default(),
            fresh: 0,
        }
    }

    /// Map an AST type to a symbolic sort for variable creation.
    /// Only builtin scalars are mappable; structs/arrays/functions are not.
    fn type_map(&self, ty: &Type) -> Result<SymType, String> {
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

    fn fresh_sym(&mut self, hint: &str, ty: SymType) -> SymExpr {
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
                let len: Option<usize> = eval_len_const_or_err(len_expr);
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
