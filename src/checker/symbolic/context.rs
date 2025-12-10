use crate::{
    ast::*,
    checker::symbolic::expr::{SymExpr, SymType},
    checker::symbolic::state::MemoryEventKind,
    utils::{SetConfig, module_resolver::Module},
};
use std::collections::HashMap;

/// Per-struct member index used for field/method lookup.
#[derive(Clone, Debug)]
pub enum MemberIndex {
    Field { field_id: i64 },
    Method { func_id: i64 },
}

impl MemberIndex {
    /// Returns field id if this member is a field.
    pub fn as_field_id(&self) -> Option<i64> {
        match self {
            MemberIndex::Field { field_id } => Some(*field_id),
            _ => None,
        }
    }
    /// Returns function id if this member is a method.
    pub fn as_func_id(&self) -> Option<i64> {
        match self {
            MemberIndex::Method { func_id } => Some(*func_id),
            _ => None,
        }
    }
}

/// Metadata describing a lookup chip that participates in a permutation pair.
#[derive(Clone, Debug)]
pub struct MemoryChipMeta {
    pub kind: MemoryEventKind,
    pub partner: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    Builtin,     // primitive scalar type
    Struct(i64), // struct type by name lookup
    Enum(i64),   // enum type by name lookup
}

/// Minimal typing info used by symbolic execution and light inference.
#[derive(Clone, Debug, Default)]
struct TypeCtx {
    var_types: HashMap<i64, Type>,   // var_id -> declared type
    const_types: HashMap<i64, Type>, // const_id -> type
    const_ints: HashMap<i64, u64>,
    field_types: HashMap<i64, Type>, // field_id -> type
    fn_sigs: HashMap<i64, (Vec<Type>, Option<Type>)>, // func_id -> (params, ret?)
}

/// Global initialization context (flat namespace).
#[derive(Clone, Debug, Default)]
pub struct Context {
    next_sym_id: usize,
    funcs: HashMap<i64, Func>, // func_id -> Func
    struct_fields: HashMap<i64, HashMap<String, MemberIndex>>, // struct_id -> { name -> member }
    struct_names: HashMap<i64, String>, // struct_id -> struct name
    struct_index: HashMap<String, i64>, // struct name -> struct_id
    types: TypeCtx,
    func_owner: HashMap<i64, i64>, // record method ownership (func_id -> struct_id)
    memory_chips: HashMap<String, MemoryChipMeta>, // lookup chip metadata (lowercase)
    enum_names: HashMap<i64, String>, // enum_id -> enum name
    enum_index: HashMap<String, i64>, // enum name -> enum_id
    enum_widths: HashMap<i64, usize>, // enum_id -> backing integer width
    pub config: SetConfig,
}

impl Context {
    /// Default width for integer literals.
    const DEFAULT_INT_WIDTH: usize = 64;
    /// Default width for enum-backed scalar values.
    const DEFAULT_ENUM_WIDTH: usize = 32;

    /// Returns the struct id associated with a component or struct name.
    pub fn struct_id_by_name(&self, name: &str) -> Option<i64> {
        self.struct_index.get(name).copied()
    }

    /// Returns the canonical name of a struct given its id.
    fn struct_name(&self, struct_id: i64) -> Option<&String> {
        self.struct_names.get(&struct_id)
    }

    /// Returns the member map of a struct if available.
    pub fn struct_members(&self, struct_id: i64) -> Option<&HashMap<String, MemberIndex>> {
        self.struct_fields.get(&struct_id)
    }

    /// Return the symbolic scalar type used to represent an enum discriminant.
    pub fn enum_sym_type(&self, enum_id: i64) -> SymType {
        let bits = self
            .enum_widths
            .get(&enum_id)
            .copied()
            .unwrap_or(Self::DEFAULT_ENUM_WIDTH);
        SymType::Uint(bits)
    }

    /// Constructs a canonical `Type::Path` for the given struct id.
    /// The resulting path uses the struct's name as its terminal segment.
    pub fn struct_type(&self, struct_id: i64) -> Option<Type> {
        self.struct_name(struct_id).map(|name| Type::Path {
            segments: vec![name.clone()],
            ref_id: Some(struct_id),
        })
    }

    /// Resolve field_id by (struct_id, field name).
    pub fn field_id_of(&self, struct_id: i64, name: &str) -> Option<i64> {
        self.struct_members(struct_id)
            .and_then(|m| m.get(name))
            .and_then(|mi| mi.as_field_id())
    }

    /// Look up the literal integer value of a constant by id, if available.
    /// Only constants defined as a single `Expr::Int` are recorded here.
    pub fn const_int(&self, id: i64) -> Option<u64> {
        self.types.const_ints.get(&id).copied()
    }

    /// Construct builtin `bool` type.
    pub fn builtin_bool_type(&self) -> Type {
        Type::Path {
            ref_id: None,
            segments: vec!["bool".to_string()],
        }
    }

    /// Construct builtin field type (`field`).
    pub fn builtin_field_type(&self) -> Type {
        Type::Path {
            ref_id: None,
            segments: vec!["field".to_string()],
        }
    }

    /// Construct builtin unsigned integer type `u{bits}`.
    pub fn builtin_uint_type(&self, bits: usize) -> Type {
        Type::Path {
            ref_id: None,
            segments: vec![format!("u{}", bits)],
        }
    }

    /// Construct builtin signed integer type `i{bits}`.
    pub fn builtin_int_type(&self, bits: usize) -> Type {
        Type::Path {
            ref_id: None,
            segments: vec![format!("i{}", bits)],
        }
    }

    /// Map an AST type to a builtin scalar SymType, if possible.
    /// Only builtin scalars are mapped; structs/arrays/functions are rejected.
    pub fn builtin_type_to_sym_type(&self, ty: &Type) -> Option<SymType> {
        match self.classify_type(ty) {
            Ok(PathKind::Builtin) => {
                let Type::Path { segments, .. } = ty else {
                    unreachable!("classify_type returned Builtin for non-Path");
                };
                let last = segments.last()?.to_ascii_lowercase();

                // Ignore Selector Variable.
                if last == "selector" {
                    return Some(SymType::Bool);
                }

                if last == "bool" {
                    return Some(SymType::Bool);
                }
                if last == "field" || last == "f" {
                    return Some(SymType::F);
                }
                if last == "timestamp" {
                    return Some(SymType::Uint(64));
                }
                if last == "word" {
                    return Some(SymType::Uint(32));
                }
                if let Some(bits) = last.strip_prefix('u') {
                    let w = bits.parse::<usize>().ok()?;
                    return Some(SymType::Uint(w));
                }
                if let Some(bits) = last.strip_prefix('i') {
                    let w = bits.parse::<usize>().ok()?;
                    return Some(SymType::Int(w));
                }

                None
            }
            Ok(PathKind::Enum(enum_id)) => Some(self.enum_sym_type(enum_id)),
            Ok(PathKind::Struct(_)) => None,
            Err(_) => None,
        }
    }

    /// Return a builtin constant (value, type) by name, if supported.
    pub fn builtin_const(&self, name: &str) -> Option<(SymExpr, Type)> {
        match name.to_ascii_lowercase().as_str() {
            "one" => Some((SymExpr::Int(1), self.builtin_field_type())),
            "zero" => Some((SymExpr::Int(0), self.builtin_field_type())),
            _ => None,
        }
    }

    /// Map a scalar SymType back to a builtin AST type.
    pub fn sym_type_to_builtin_type(&self, sty: &SymType) -> Type {
        match *sty {
            SymType::Bool => self.builtin_bool_type(),
            SymType::F => self.builtin_field_type(),
            SymType::Uint(w) => self.builtin_uint_type(w),
            SymType::Int(w) => self.builtin_int_type(w),
        }
    }

    /// Combine two SymType values under a binary operator.
    /// Returns the resulting SymType if the combination is well-typed.
    pub fn combine_sym_types_for_binary(
        &self,
        op: &BinOp,
        lhs: SymType,
        rhs: SymType,
    ) -> Option<SymType> {
        use SymType::*;

        // Comparison and equality always return Bool if operands are compatible.
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let compatible = match (&lhs, &rhs) {
                    (F, F) => true,
                    (Uint(_), Uint(_)) => true,
                    (Int(_), Int(_)) => true,
                    (Bool, Bool) => true,
                    (Bool, Uint(_)) | (Uint(_), Bool) => true,
                    _ => false,
                };
                if compatible {
                    return Some(Bool);
                } else {
                    return None;
                }
            }

            // Logical operators only work on Bool.
            BinOp::And | BinOp::Or => {
                if lhs == Bool && rhs == Bool {
                    return Some(Bool);
                } else {
                    return None;
                }
            }

            // All other operators are treated as arithmetic-like.
            _ => {}
        }

        // Arithmetic-like operators.
        match (lhs, rhs) {
            // Field operations: only F with F.
            (F, F) => Some(F),

            // Unsigned integers: widen to max width.
            (Uint(w1), Uint(w2)) => Some(Uint(std::cmp::max(w1, w2))),

            // Signed integers: widen to max width.
            (Int(w1), Int(w2)) => Some(Int(std::cmp::max(w1, w2))),

            // Mixed signed/unsigned: promote to signed with max width.
            (Int(wi), Uint(wu)) | (Uint(wu), Int(wi)) => Some(Int(std::cmp::max(wi, wu))),

            // Bool with Uint: treat Bool as u1.
            (Bool, Uint(w)) | (Uint(w), Bool) => {
                let w_bool = 1;
                Some(Uint(std::cmp::max(w, w_bool)))
            }

            // Arithmetic on Bool-only: treat as u1.
            (Bool, Bool) => Some(Uint(1)),

            // Other combinations are rejected (e.g. Bool with Field, Field with Int/Uint).
            _ => None,
        }
    }

    /// Query the static type of a non-function id.
    /// Looks up var, const, or field types only.
    pub fn query_type(&self, id: i64) -> Option<&Type> {
        self.types
            .var_types
            .get(&id)
            .or_else(|| self.types.const_types.get(&id))
            .or_else(|| self.types.field_types.get(&id))
    }

    /// Strictly classify a `Type::Path` using `struct_index` by terminal name.
    /// Precondition: `ty` must be `Type::Path`; otherwise this function panics.
    pub fn classify_type(&self, ty: &Type) -> Result<PathKind, String> {
        // Precondition check: accept only Path, reject others immediately.
        let segments = match ty {
            Type::Path { segments, .. } => segments,
            other => {
                return Err(format!(
                    "cannot classify non-path type as builtin/struct: {:?}",
                    other
                ));
            }
        };

        #[inline]
        fn is_builtin(name: &str) -> bool {
            // Extend to your DSL's primitive set as needed.
            matches!(
                name.to_ascii_lowercase().as_str(),
                "bool"
                    | "field"
                    | "f"
                    | "word"
                    | "u8"
                    | "u16"
                    | "u24"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "i32"
                    | "i64"
                    | "selector"
                    | "timestamp"
            )
        }

        let last = segments
            .last()
            .ok_or_else(|| "empty type path".to_string())?
            .as_str();

        // Name-first policy: struct names take precedence.
        if let Some(&sid) = self.struct_index.get(last) {
            return Ok(PathKind::Struct(sid));
        }
        if let Some(&eid) = self.enum_index.get(last) {
            return Ok(PathKind::Enum(eid));
        }
        if is_builtin(last) {
            return Ok(PathKind::Builtin);
        }
        Err(format!("unknown type path by name: {}", last))
    }

    /// Determine the `(clk_prev, value)` pair type produced by a map access.
    /// If the map value is already a tuple with at least two elements, reuse its head.
    /// Otherwise default to `(timestamp, value)`.
    pub fn map_return_pair_types(&self, ts_ty: &Type, val_ty: &Type) -> (Type, Type) {
        match val_ty {
            Type::Tuple(elems) if elems.len() >= 2 => (elems[0].clone(), elems[1].clone()),
            _ => (ts_ty.clone(), val_ty.clone()),
        }
    }

    /// Register a pair of lookup chips that form a permutation relation.
    pub fn register_memory_permutation(&mut self, send: &str, receive: &str) {
        let s = send.to_ascii_lowercase();
        let r = receive.to_ascii_lowercase();

        self.memory_chips.insert(
            s.clone(),
            MemoryChipMeta {
                kind: MemoryEventKind::Send,
                partner: Some(r.clone()),
            },
        );
        self.memory_chips.insert(
            r.clone(),
            MemoryChipMeta {
                kind: MemoryEventKind::Receive,
                partner: Some(s),
            },
        );
    }

    /// Lookup metadata for a memory-related chip name.
    pub fn memory_chip(&self, name: &str) -> Option<&MemoryChipMeta> {
        self.memory_chips.get(&name.to_ascii_lowercase())
    }

    /// Best-effort static type inference from ids already attached to nodes.
    pub fn infer_expr_type_static(&self, e: &Expr) -> Option<Type> {
        match e {
            // Integer literals: give them a default builtin integer type.
            Expr::Int(_) => Some(self.builtin_uint_type(Self::DEFAULT_INT_WIDTH)),

            // Boolean literals: builtin bool type.
            Expr::Bool(_) => Some(self.builtin_bool_type()),

            Expr::Path { ref_id, segments } => {
                if let Some(id) = *ref_id {
                    if let Some(ty) = self.types.var_types.get(&id) {
                        return Some(ty.clone());
                    }
                    if let Some(ty) = self.types.const_types.get(&id) {
                        return Some(ty.clone());
                    }
                    if self.funcs.contains_key(&id) {
                        return Some(Type::Function { ref_id: Some(id) });
                    }
                }
                // Fallback to known builtin constants (e.g., `one`, `zero`).
                if let Some(last) = segments.last() {
                    if let Some((_val, ty)) = self.builtin_const(last) {
                        return Some(ty);
                    }
                }
                None
            }

            Expr::Field { ref_id, base, name } => {
                if let Some(id) = *ref_id {
                    if let Some(ty) = self.types.field_types.get(&id) {
                        return Some(ty.clone());
                    }
                    if self.funcs.contains_key(&id) {
                        return Some(Type::Function { ref_id: Some(id) });
                    }
                }
                if let Expr::MapIndex { base: map_base, .. } = base.as_ref() {
                    if let Some(Type::Map {
                        timestamp, value, ..
                    }) = self.infer_expr_type_static(map_base)
                    {
                        let (ts_ty, val_ty) =
                            self.map_return_pair_types(timestamp.as_ref(), value.as_ref());
                        return match name.as_str() {
                            "0" | "clk_prev" => Some(ts_ty),
                            "1" | "value" => Some(val_ty),
                            _ => None,
                        };
                    }
                }
                if let Some(Type::Tuple(elems)) = self.infer_expr_type_static(base) {
                    if let Ok(idx) = name.parse::<usize>() {
                        return elems.get(idx).cloned();
                    }
                }
                // Fallback: use the base expression type if we cannot resolve field id directly.
                self.infer_expr_type_static(base)
            }

            Expr::Call(callee, _args) => self.infer_expr_type_static(callee),

            Expr::Index(base, _idx) => {
                if let Some(Type::Array(inner, _)) = self.infer_expr_type_static(base) {
                    return Some((*inner).clone());
                }
                None
            }

            Expr::MapIndex { base, .. } => {
                if let Some(Type::Map {
                    timestamp, value, ..
                }) = self.infer_expr_type_static(base)
                {
                    let (ts_ty, val_ty) =
                        self.map_return_pair_types(timestamp.as_ref(), value.as_ref());
                    return Some(Type::Tuple(vec![ts_ty, val_ty]));
                }
                None
            }

            // Binary expression type inference via SymType normalization.
            Expr::Binary { op, lhs, rhs } => {
                let lt = self.infer_expr_type_static(lhs)?;
                let rt = self.infer_expr_type_static(rhs)?;

                // Only builtin scalar types participate in this normalization.
                let ls = self.builtin_type_to_sym_type(&lt)?;
                let rs = self.builtin_type_to_sym_type(&rt)?;

                let res_sym = self.combine_sym_types_for_binary(op, ls, rs)?;
                Some(self.sym_type_to_builtin_type(&res_sym))
            }

            Expr::Paren(inner) => self.infer_expr_type_static(inner),
        }
    }

    /// Returns the function definition associated with the given identifier.
    pub fn func_def(&self, id: i64) -> Option<&Func> {
        self.funcs.get(&id)
    }

    /// Query function signature by id.
    pub fn fn_sig(&self, id: i64) -> Option<&(Vec<Type>, Option<Type>)> {
        self.types.fn_sigs.get(&id)
    }

    /// Returns the struct_id that owns this function if it is a method.
    /// None means it's a free function (not a struct method).
    pub fn method_owner(&self, func_id: i64) -> Option<i64> {
        self.func_owner.get(&func_id).copied()
    }

    /// Convenience: check if `func_id` is a method of `struct_id`.
    pub fn is_method_of(&self, func_id: i64, struct_id: i64) -> bool {
        self.func_owner.get(&func_id).copied() == Some(struct_id)
    }
    /// Resolve a method id by struct id and method name.
    pub fn resolve_method_on_struct(&self, struct_id: i64, method_name: &str) -> Option<i64> {
        let members = self.struct_members(struct_id)?;
        match members.get(method_name)? {
            MemberIndex::Method { func_id } => Some(*func_id),
            _ => None,
        }
    }

    /// Resolve a call callee from an lvalue.
    /// Handles qualified methods like `TypeName::method(...)`.
    pub fn resolve_call_from_lvalue(&self, callee: &LValue) -> (i64, Option<SymExpr>) {
        // Qualified static method: TypeName::method(...)
        if let Some(struct_id) = callee.ref_id {
            if callee.tails.len() == 1 {
                if let LvTail::Field { name } = &callee.tails[0] {
                    if let Some(fid) = self.resolve_method_on_struct(struct_id, name.as_str()) {
                        return (fid, None);
                    }
                }
            }
        }

        // Fallback: use ref_id as a function id if present.
        if let Some(fid) = callee.ref_id {
            return (fid, None);
        }

        panic!("cannot resolve function call from lvalue: {:?}", callee);
    }
}

/// Single global symbol table + stack of local frames.
#[derive(Default, Clone)]
struct Scope {
    globals: HashMap<String, i64>,
    locals: Vec<HashMap<String, i64>>,
}

impl Scope {
    fn new() -> Self {
        Self {
            globals: HashMap::new(),
            locals: Vec::new(),
        }
    }
    fn push(&mut self) {
        self.locals.push(HashMap::new());
    }
    fn pop(&mut self) {
        self.locals.pop();
    }

    fn insert_local(&mut self, name: String, id: i64) {
        if let Some(top) = self.locals.last_mut() {
            top.insert(name, id);
        } else {
            self.globals.insert(name, id);
        }
    }
    fn insert_global(&mut self, name: String, id: i64) {
        self.globals.insert(name, id);
    }

    /// Locals from inner to outer, then globals.
    fn resolve_name(&self, name: &str) -> Option<i64> {
        for frame in self.locals.iter().rev() {
            if let Some(id) = frame.get(name) {
                return Some(*id);
            }
        }
        self.globals.get(name).cloned()
    }

    /// Take the last path segment (e.g., a::b::C => "C") and resolve it.
    fn resolve_path(&self, segs: &[String]) -> Option<i64> {
        segs.last().and_then(|last| self.resolve_name(last))
    }
}

fn fresh_id(next: &mut usize) -> i64 {
    let id = *next as i64;
    *next += 1;
    id
}

/// Evaluate an enum variant value into a concrete `u64`.
/// Supports integer literals and references to other integer constants.
fn eval_enum_value(expr: &Expr, ctx: &Context) -> Result<u64, String> {
    match expr {
        Expr::Int(k) => Ok(*k),
        Expr::Paren(inner) => eval_enum_value(inner, ctx),
        Expr::Path {
            ref_id: Some(cid), ..
        } => ctx
            .const_int(*cid)
            .ok_or_else(|| "enum discriminant must resolve to an integer constant".to_string()),
        _ => Err(format!(
            "unsupported enum discriminant expression: {:?}",
            expr
        )),
    }
}

/// Build flat globals, resolve types/exprs/functions, and collect exec-time indices.
/// All top-level symbols from all modules are global; `import` is ignored in this prototype.
pub fn init_context(mods: &mut [Module]) -> Context {
    let mut ctx = Context::default();
    let mut scope = Scope::new();

    // Publish all top-level items into the global table.
    for m in mods.iter_mut() {
        for item in m.file.items.iter_mut() {
            match item {
                Item::Import { .. } | Item::Component { .. } => {}
                Item::Const { id, name, .. } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
                }
                Item::Enum {
                    id, name, variants, ..
                } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
                    ctx.enum_index.insert(name.clone(), nid);
                    ctx.enum_names.insert(nid, name.clone());

                    // Seed variant ids so they are globally visible like constants.
                    for v in variants.iter_mut() {
                        let vid = fresh_id(&mut ctx.next_sym_id);
                        v.id = Some(vid);
                        scope.insert_global(v.name.clone(), vid);
                    }
                }
                Item::Struct { id, name, .. } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
                    ctx.struct_index.insert(name.clone(), nid);
                    ctx.struct_names.insert(nid, name.clone());
                }
                Item::Function { id, func } => {
                    let fid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(fid);
                    scope.insert_global(func.name.clone(), fid);
                }
            }
        }
    }

    // Resolve internals with flat visibility.
    for m in mods.iter_mut() {
        scope.push();

        for item in m.file.items.iter_mut() {
            match item {
                Item::Import { .. } => {}

                Item::Const { ty, value, id, .. } => {
                    resolve_type_ids_flat(ty, &scope, &mut ctx);
                    resolve_expr_ids_flat(value, &scope, &mut ctx);
                    if let Some(cid) = *id {
                        ctx.types.const_types.insert(cid, ty.clone());
                        if let Expr::Int(k) = value {
                            ctx.types.const_ints.insert(cid, *k);
                        } else {
                            unimplemented!(
                                "non-literal const initializer: only `Expr::Int` is recorded in const_ints for now"
                            );
                        }
                    }
                }

                Item::Enum {
                    id: enum_id,
                    name,
                    variants,
                } => {
                    let enum_id = enum_id.expect("enum id set");
                    // Default backing width for enums; can be customized later.
                    ctx.enum_widths
                        .entry(enum_id)
                        .or_insert(Context::DEFAULT_ENUM_WIDTH);

                    let mut next_value: u64 = 0;
                    for v in variants.iter_mut() {
                        if v.id.is_none() {
                            let vid = fresh_id(&mut ctx.next_sym_id);
                            v.id = Some(vid);
                            scope.insert_global(v.name.clone(), vid);
                        }

                        if let Some(val) = &mut v.value {
                            resolve_expr_ids_flat(val, &scope, &mut ctx);
                        }

                        let value = match &v.value {
                            Some(expr) => eval_enum_value(expr, &ctx).unwrap_or_else(|e| {
                                panic!(
                                    "enum `{}` variant `{}` has invalid value: {}",
                                    name, v.name, e
                                )
                            }),
                            None => next_value,
                        };
                        next_value = value.saturating_add(1);

                        let vid = v.id.expect("enum variant id set");
                        let ty = Type::Path {
                            segments: vec![name.clone()],
                            ref_id: Some(enum_id),
                        };
                        ctx.types.const_types.insert(vid, ty);
                        ctx.types.const_ints.insert(vid, value);
                    }
                }

                Item::Struct {
                    id: s_id, fields, ..
                } => {
                    let struct_id = s_id.expect("struct id set");
                    let mut mmap = HashMap::with_capacity(fields.len());
                    for f in fields.iter_mut() {
                        let fid = fresh_id(&mut ctx.next_sym_id);
                        f.id = Some(fid);
                        let mut fty = f.ty.clone();
                        resolve_type_ids_flat(&mut fty, &scope, &mut ctx);
                        ctx.types.field_types.insert(fid, fty);
                        mmap.insert(f.name.clone(), MemberIndex::Field { field_id: fid });
                    }
                    ctx.struct_fields.insert(struct_id, mmap);
                }

                Item::Component {
                    name: comp_name,
                    members,
                    ..
                } => {
                    let struct_id = *ctx
                        .struct_index
                        .get(comp_name)
                        .expect("Component must pair with same-named Struct");

                    ctx.struct_fields.entry(struct_id).or_default();

                    for mem in members.iter_mut() {
                        match mem {
                            Member::Computation(fun) | Member::Constraint(fun) => {
                                if fun.id.is_none() {
                                    let fid = fresh_id(&mut ctx.next_sym_id);
                                    fun.id = Some(fid);
                                }
                                let fid = fun.id.unwrap();
                                ctx.struct_fields
                                    .get_mut(&struct_id)
                                    .unwrap()
                                    .insert(fun.name.clone(), MemberIndex::Method { func_id: fid });

                                ctx.func_owner.insert(fid, struct_id);
                            }
                        }
                    }

                    // Store function signatures and resolve bodies.
                    for mem in members.iter_mut() {
                        match mem {
                            Member::Computation(fun) | Member::Constraint(fun) => {
                                let param_tys: Vec<Type> = fun
                                    .params
                                    .iter()
                                    .filter_map(|p| match p {
                                        Param::Typed { ty, .. } => {
                                            let mut t = ty.clone();
                                            resolve_type_ids_flat(&mut t, &scope, &mut ctx);
                                            Some(t)
                                        }
                                        _ => None,
                                    })
                                    .collect();

                                let ret_ty = fun.ret.as_ref().map(|t| {
                                    let mut r = t.clone();
                                    resolve_type_ids_flat(&mut r, &scope, &mut ctx);
                                    r
                                });

                                let fid = fun.id.expect("func id must exist");
                                ctx.types.fn_sigs.insert(fid, (param_tys, ret_ty));
                                resolve_func_flat(fun, &mut ctx, &mut scope);
                                ctx.funcs.insert(fid, fun.clone());
                            }
                        }
                    }
                }

                Item::Function { func, .. } => {
                    if func.id.is_none() {
                        let fid = fresh_id(&mut ctx.next_sym_id);
                        func.id = Some(fid);
                    }

                    let param_tys: Vec<Type> = func
                        .params
                        .iter()
                        .filter_map(|p| match p {
                            Param::Typed { ty, .. } => {
                                let mut t = ty.clone();
                                resolve_type_ids_flat(&mut t, &scope, &mut ctx);
                                Some(t)
                            }
                            _ => None,
                        })
                        .collect();

                    let ret_ty = func.ret.as_ref().map(|t| {
                        let mut r = t.clone();
                        resolve_type_ids_flat(&mut r, &scope, &mut ctx);
                        r
                    });

                    let fid = func.id.expect("func id must exist");
                    ctx.types.fn_sigs.insert(fid, (param_tys, ret_ty));
                    resolve_func_flat(func, &mut ctx, &mut scope);
                    ctx.funcs.insert(fid, func.clone());
                }
            }
        }

        scope.pop();
    }

    // Builtin memory permutation: Send <-> Receive.
    ctx.register_memory_permutation("Send", "Receive");
    // Instruction-level permutation used for CPU <-> chip wiring.
    ctx.register_memory_permutation("SendInstruction", "ReceiveInstruction");

    ctx
}

/// Resolve expressions. Field access binds to field_id or func_id using the base type.
fn resolve_expr_ids_flat(e: &mut Expr, scope: &Scope, ctx: &mut Context) {
    match e {
        Expr::Int(_) | Expr::Bool(_) => {}

        Expr::Path { segments, ref_id } => {
            *ref_id = scope.resolve_path(segments);
        }

        Expr::Call(callee, args) => {
            resolve_expr_ids_flat(callee, scope, ctx);
            for a in args.iter_mut() {
                resolve_expr_ids_flat(a, scope, ctx);
            }
        }

        Expr::Index(base, idx) => {
            resolve_expr_ids_flat(base, scope, ctx);
            resolve_expr_ids_flat(idx, scope, ctx);
        }

        Expr::MapIndex { base, keys } => {
            resolve_expr_ids_flat(base, scope, ctx);
            for k in keys.iter_mut() {
                resolve_expr_ids_flat(k, scope, ctx);
            }
        }

        Expr::Field { base, name, ref_id } => {
            resolve_expr_ids_flat(base, scope, ctx);

            // Determine the static type of the base expression.
            let base_ty = ctx.infer_expr_type_static(base);

            // If base is a struct value (Type::Path with struct_id), resolve the member.
            if let Some(Type::Path {
                ref_id: Some(struct_id),
                ..
            }) = base_ty
            {
                if let Some(members) = ctx.struct_fields.get(&struct_id) {
                    if let Some(member) = members.get(name) {
                        match member {
                            MemberIndex::Field { field_id } => {
                                *ref_id = Some(*field_id);
                            }
                            MemberIndex::Method { func_id } => {
                                *ref_id = Some(*func_id);
                            }
                        }
                        return;
                    }
                }
            }
            // Unknown member or non-struct base: keep ref_id=None for later diagnostics.
        }

        Expr::Binary { lhs, rhs, .. } => {
            resolve_expr_ids_flat(lhs, scope, ctx);
            resolve_expr_ids_flat(rhs, scope, ctx);
        }

        Expr::Paren(inner) => resolve_expr_ids_flat(inner, scope, ctx),
    }
}

/// Resolve types that may contain paths or const-length expressions.
fn resolve_type_ids_flat(ty: &mut Type, scope: &Scope, ctx: &mut Context) {
    match ty {
        Type::Path { segments, ref_id } => {
            *ref_id = scope.resolve_path(segments);
        }
        Type::Array(inner, len_expr) => {
            resolve_type_ids_flat(inner, scope, ctx);
            resolve_expr_ids_flat(len_expr, scope, ctx); // allow const exprs in length
        }
        Type::Tuple(elems) => {
            for t in elems.iter_mut() {
                resolve_type_ids_flat(t, scope, ctx);
            }
        }
        Type::Map {
            timestamp,
            key,
            value,
        } => {
            resolve_type_ids_flat(timestamp, scope, ctx);
            resolve_type_ids_flat(key, scope, ctx);
            resolve_type_ids_flat(value, scope, ctx);
        }
        Type::Function { ref_id: _ } => {
            // Function type only carries id; nothing to resolve here.
        }
    }
}

/// Resolve params/locals/body in a fresh local frame; seed TypeCtx.var_types.
fn resolve_func_flat(fun: &mut Func, ctx: &mut Context, scope: &mut Scope) {
    scope.push();
    let fid = fun.id.expect("func id must exist");
    let owner_struct = ctx.method_owner(fid);

    for p in &mut fun.params {
        match p {
            Param::SelfParam { id } => {
                let nid = fresh_id(&mut ctx.next_sym_id);
                *id = Some(nid);

                // Bind the implicit `self` parameter into the current local scope.
                scope.insert_local("self".to_string(), nid);

                if let Some(sid) = owner_struct {
                    // Construct a canonical `Type::Path` pointing to the owning struct.
                    // The terminal segment reuses the struct's declared name,
                    let ty = ctx
                        .struct_type(sid)
                        .unwrap_or_else(|| panic!("no struct name recorded for struct_id {}", sid));
                    ctx.types.var_types.insert(nid, ty);
                }
            }
            Param::Typed { id, name, ty, .. } => {
                let nid = fresh_id(&mut ctx.next_sym_id);
                *id = Some(nid);
                resolve_type_ids_flat(ty, scope, ctx);
                scope.insert_local(name.clone(), nid);
                ctx.types.var_types.insert(nid, ty.clone());
            }
        }
    }

    if let Some(ret) = &mut fun.ret {
        resolve_type_ids_flat(ret, scope, ctx);
    }
    for s in &mut fun.body {
        resolve_stmt_ids_flat(s, ctx, scope);
    }

    scope.pop();
}

/// Resolve statements and bind locals.
fn resolve_stmt_ids_flat(s: &mut Stmt, ctx: &mut Context, scope: &mut Scope) {
    match s {
        Stmt::VarDecl { id, ty, name, init } => {
            let nid = fresh_id(&mut ctx.next_sym_id);
            *id = Some(nid);
            resolve_type_ids_flat(ty, scope, ctx);
            resolve_expr_ids_flat(init, scope, ctx);
            scope.insert_local(name.clone(), nid);
            ctx.types.var_types.insert(nid, ty.clone());
        }
        Stmt::Assign { target, value } | Stmt::AndAssign { target, value } => {
            resolve_lvalue_ids_flat(target, scope, ctx);
            resolve_expr_ids_flat(value, scope, ctx);
        }
        Stmt::For {
            id,
            var,
            start,
            end,
            body,
        } => {
            resolve_expr_ids_flat(start, scope, ctx);
            resolve_expr_ids_flat(end, scope, ctx);
            scope.push();
            let nid = fresh_id(&mut ctx.next_sym_id);
            *id = Some(nid);
            scope.insert_local(var.clone(), nid);
            for st in body.iter_mut() {
                resolve_stmt_ids_flat(st, ctx, scope);
            }
            scope.pop();
        }
        Stmt::If {
            cond,
            then_branch,
            else_branch,
        } => {
            resolve_expr_ids_flat(cond, scope, ctx);

            scope.push();
            for st in then_branch.iter_mut() {
                resolve_stmt_ids_flat(st, ctx, scope);
            }
            scope.pop();

            scope.push();
            for st in else_branch.iter_mut() {
                resolve_stmt_ids_flat(st, ctx, scope);
            }
            scope.pop();
        }
        Stmt::AssertBool(e) | Stmt::AssertZero(e) => resolve_expr_ids_flat(e, scope, ctx),
        Stmt::AssertEq(a, b) => {
            resolve_expr_ids_flat(a, scope, ctx);
            resolve_expr_ids_flat(b, scope, ctx);
        }
        Stmt::AssertRange { value, ty } => {
            resolve_expr_ids_flat(value, scope, ctx);
            resolve_type_ids_flat(ty, scope, ctx);
        }
        Stmt::Lookup { chip, opcode, args } => {
            resolve_expr_ids_flat(opcode, scope, ctx);
            for a in args.iter_mut() {
                resolve_expr_ids_flat(a, scope, ctx);
            }
            // Chip identifiers are treated as builtin paths; no scope resolution required.
            for seg in chip.iter_mut() {
                *seg = seg.clone();
            }
        }
        Stmt::Call { callee, args } => {
            resolve_lvalue_ids_flat(callee, scope, ctx);
            for a in args.iter_mut() {
                resolve_expr_ids_flat(a, scope, ctx);
            }
        }
        Stmt::Return(e) => resolve_expr_ids_flat(e, scope, ctx),
    }
}

/// Resolve the lvalue head now; field tails are deferred to exec-time.
fn resolve_lvalue_ids_flat(lv: &mut LValue, scope: &Scope, ctx: &mut Context) {
    lv.ref_id = scope.resolve_path(&lv.head);
    for tail in lv.tails.iter_mut() {
        match tail {
            LvTail::Index(idx) => resolve_expr_ids_flat(idx, scope, ctx),
            LvTail::MapIndex(k1, k2) => {
                resolve_expr_ids_flat(k1, scope, ctx);
                resolve_expr_ids_flat(k2, scope, ctx);
            }
            _ => {}
        }
    }
}
