use crate::{ast::*, utils::module_resolver::Module};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    Builtin,     // primitive scalar type
    Struct(i64), // struct type by name lookup
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
}

impl Context {
    /// Returns the canonical name of a struct given its id.
    fn struct_name(&self, struct_id: i64) -> Option<&String> {
        self.struct_names.get(&struct_id)
    }

    /// Returns the member map of a struct if available.
    pub fn struct_members(&self, struct_id: i64) -> Option<&HashMap<String, MemberIndex>> {
        self.struct_fields.get(&struct_id)
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
        let Type::Path { segments, .. } = ty else {
            unreachable!("classify_path_by_name_strict: expected Type::Path, got non-Path");
        };

        #[inline]
        fn is_builtin(name: &str) -> bool {
            // Extend to your DSL's primitive set as needed.
            matches!(
                name.to_ascii_lowercase().as_str(),
                "bool" | "field" | "u8" | "u16" | "u32" | "u64" | "u128" | "i32" | "i64"
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
        if is_builtin(last) {
            return Ok(PathKind::Builtin);
        }
        Err(format!("unknown type path by name: {}", last))
    }

    /// Best-effort static type inference from ids already attached to nodes.
    pub fn infer_expr_type(&self, e: &Expr) -> Option<Type> {
        match e {
            Expr::Int(_) => None,
            Expr::Bool(_) => None,

            Expr::Path { ref_id, .. } => {
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
                None
            }

            Expr::Field { ref_id, base, .. } => {
                if let Some(id) = *ref_id {
                    if let Some(ty) = self.types.field_types.get(&id) {
                        return Some(ty.clone());
                    }
                    if self.funcs.contains_key(&id) {
                        return Some(Type::Function { ref_id: Some(id) });
                    }
                }
                self.infer_expr_type(base)
            }

            Expr::Call(callee, _args) => self.infer_expr_type(callee),

            Expr::Index(base, _idx) => {
                if let Some(Type::Array(inner, _)) = self.infer_expr_type(base) {
                    return Some((*inner).clone());
                }
                None
            }

            Expr::Binary { .. } => None,
            Expr::Paren(inner) => self.infer_expr_type(inner),
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

/// Build flat globals, resolve types/exprs/functions, and collect exec-time indices.
/// All top-level symbols from all modules are global; `import` is ignored in this prototype.
pub fn init_context(mods: &mut [Module]) -> Context {
    let mut ctx = Context::default();
    let mut scope = Scope::new();

    // Publish all top-level items into the global table.
    for m in mods.iter_mut() {
        for item in m.file.items.iter_mut() {
            match item {
                Item::Import { .. } => {}
                Item::Const { id, name, .. } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
                }
                Item::Struct { id, name, .. } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
                    ctx.struct_index.insert(name.clone(), nid);
                    ctx.struct_names.insert(nid, name.clone());
                }
                Item::Component { id, name, .. } => {
                    let nid = fresh_id(&mut ctx.next_sym_id);
                    *id = Some(nid);
                    scope.insert_global(name.clone(), nid);
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

                    // Ensure the struct has a member map to extend with methods.
                    ctx.struct_fields.entry(struct_id).or_default();

                    // Allocate function ids, expose globally, and bind as methods of the struct.
                    for mem in members.iter_mut() {
                        match mem {
                            Member::Computation(fun) | Member::Constraint(fun) => {
                                if fun.id.is_none() {
                                    let fid = fresh_id(&mut ctx.next_sym_id);
                                    fun.id = Some(fid);
                                    scope.insert_global(fun.name.clone(), fid);
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
            }
        }

        scope.pop();
    }

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

        Expr::Field { base, name, ref_id } => {
            resolve_expr_ids_flat(base, scope, ctx);

            // Determine the static type of the base expression.
            let base_ty = ctx.infer_expr_type(base);

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
            Param::Typed { id, name, ty } => {
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
            resolve_lvalue_ids_flat(target, scope);
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
        Stmt::AssertBool(e) => resolve_expr_ids_flat(e, scope, ctx),
        Stmt::AssertEq(a, b) => {
            resolve_expr_ids_flat(a, scope, ctx);
            resolve_expr_ids_flat(b, scope, ctx);
        }
        Stmt::Call { callee, args } => {
            resolve_lvalue_ids_flat(callee, scope);
            for a in args.iter_mut() {
                resolve_expr_ids_flat(a, scope, ctx);
            }
        }
        Stmt::Return(e) => resolve_expr_ids_flat(e, scope, ctx),
    }
}

/// Resolve the lvalue head now; field tails are deferred to exec-time.
fn resolve_lvalue_ids_flat(lv: &mut LValue, scope: &Scope) {
    lv.ref_id = scope.resolve_path(&lv.head);
}
