use im::Vector;

use crate::{
    ast::{BinOp, Expr, Func, LValue, LvTail, Member, Stmt, Type},
    checker::symbolic::{
        context::Context,
        expr::{BoolExpr, SymExpr, SymType},
        state::{ExecStatus, Store, StoreNode, SymState},
    },
};

pub trait SymbolicExecutor {
    /// Execute one step and produce successor states.
    /// For non-return statements/expressions, the first item is None.
    fn execute(self, state: SymState) -> Vector<(Option<SymExpr>, SymState)>;
}

fn write_to_lvalue(ctx: &Context, store: Store, lv: &LValue, val: SymExpr) -> Store {
    let head_id = lv
        .ref_id
        .expect("lvalue head must be resolved to a binding id");
    let root = store
        .get(head_id)
        .cloned()
        .unwrap_or_else(|| panic!("lvalue head id {} not found in store", head_id));

    // Carry static type while descending along tails
    let mut cur_ty = ctx
        .query_type(head_id)
        .cloned()
        .unwrap_or_else(|| panic!("no static type for lvalue head {}", head_id));

    fn write_tail(
        ctx: &Context,
        mut node: StoreNode,
        cur_ty: &mut Type, // static type accumulator
        tails: &[LvTail],
        val: SymExpr,
    ) -> StoreNode {
        if tails.is_empty() {
            return match node {
                StoreNode::Scalar(_) => StoreNode::Scalar(val),
                StoreNode::Struct { fields } => match val {
                    SymExpr::Var(_, _) | SymExpr::Ite(_, _, _) => {
                        let new_fields = fields
                            .iter()
                            .map(|(fid, _)| (*fid, StoreNode::Scalar(val.clone())))
                            .collect();
                        StoreNode::Struct { fields: new_fields }
                    }
                    _ => panic!("struct assignment requires symbolic aggregate value"),
                },
                StoreNode::Array { .. } => {
                    panic!("assigning a scalar to an array without selecting an element")
                }
            };
        }

        match (&mut node, &tails[0]) {
            (StoreNode::Struct { fields }, LvTail::Field { name, .. }) => {
                // cur_ty must be struct; resolve (sid, fid) via Context
                let sid = match cur_ty {
                    Type::Path {
                        ref_id: Some(sid), ..
                    } => *sid,
                    _ => panic!("field selection on non-struct static type"),
                };
                let fid = ctx
                    .field_id_of(sid, name)
                    .unwrap_or_else(|| panic!("unknown field `{}` for struct_id {}", name, sid));

                // advance static type to field type
                let fty = ctx
                    .query_type(fid)
                    .cloned()
                    .unwrap_or_else(|| panic!("missing static type for field {}", fid));
                *cur_ty = fty;

                let child = fields
                    .get(&fid)
                    .cloned()
                    .unwrap_or_else(|| panic!("field `{}` (id={}) not materialized", name, fid));
                let new_child = write_tail(ctx, child, cur_ty, &tails[1..], val);
                let new_fields = fields.update(fid, new_child);
                StoreNode::Struct { fields: new_fields }
            }

            (StoreNode::Array { len, elems }, LvTail::Index(idx_expr)) => {
                // cur_ty must be an array; advance to inner type
                let inner = match cur_ty {
                    Type::Array(inner, _) => (&**inner).clone(),
                    _ => panic!("indexing on non-array static type"),
                };
                *cur_ty = inner;

                let idx = match idx_expr {
                    Expr::Int(k) => *k as usize,
                    _ => panic!("array index must be a concrete usize literal"),
                };
                if let Some(l) = *len {
                    if idx >= l {
                        panic!("array index {} out of bounds {}", idx, l);
                    }
                }
                if tails.len() != 1 {
                    panic!("nested write under array element is not supported");
                }
                let new_cell = StoreNode::Scalar(val);
                let new_elems = elems.update(idx, new_cell);
                StoreNode::Array {
                    len: *len,
                    elems: new_elems,
                }
            }

            _ => panic!("lvalue tail does not match node shape"),
        }
    }

    let updated = write_tail(ctx, root, &mut cur_ty, &lv.tails, val);
    store.set(head_id, updated)
}

impl SymbolicExecutor for Member {
    fn execute(self, state: SymState) -> Vector<(Option<SymExpr>, SymState)> {
        match self {
            Member::Computation(f) | Member::Constraint(f) => f.execute(state),
        }
    }
}

impl SymbolicExecutor for Func {
    fn execute(self, mut state: SymState) -> Vector<(Option<SymExpr>, SymState)> {
        // Initialize parameters; materialize `self` if method.
        let fid = self.id.expect("function id must be set");
        let self_struct_id = state.ctx.method_owner(fid);
        state.init_params_for_func(&self, self_struct_id);

        // Start with one live state
        let mut live: Vector<SymState> = Vector::unit(state);
        let mut terminals: Vector<(Option<SymExpr>, SymState)> = Vector::new();

        for stmt in self.body {
            let mut next_live: Vector<SymState> = Vector::new();

            for st in live.into_iter() {
                for (maybe_ret, s_next) in stmt.clone().execute(st) {
                    if s_next.is_terminal() {
                        terminals.push_back((maybe_ret, s_next));
                    } else {
                        next_live.push_back(s_next);
                    }
                }
            }

            live = next_live;
            if live.is_empty() {
                break;
            }
        }

        terminals
    }
}

impl SymbolicExecutor for Stmt {
    fn execute(self, st: SymState) -> Vector<(Option<SymExpr>, SymState)> {
        if !st.is_active() {
            return Vector::new();
        }

        // Evaluate Boolean expressions with sequential semantics.
        fn eval_bool_expr(e: Expr, st: SymState) -> (BoolExpr, SymState) {
            match e {
                Expr::Bool(b) => (BoolExpr::Bool(b), st),
                Expr::Paren(inner) => eval_bool_expr(*inner, st),
                Expr::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                } => {
                    // Sequential: eval lhs then rhs on resulting state
                    let l = lhs.eval(st);
                    if l.len() != 1 {
                        panic!("branching in AssertBool(Eq.lhs) unsupported");
                    }
                    let (lv, s1) = l[0].clone();

                    let r = rhs.eval(s1);
                    if r.len() != 1 {
                        panic!("branching in AssertBool(Eq.rhs) unsupported");
                    }
                    let (rv, s2) = r[0].clone();

                    (lv.eq_to(rv), s2)
                }
                _ => panic!("unsupported Boolean expression in AssertBool"),
            }
        }

        match self {
            Stmt::AssertEq(a, b) => {
                // Sequential: lhs → rhs
                let la = a.eval(st);
                if la.len() != 1 {
                    panic!("branching in AssertEq(lhs) unsupported");
                }
                let (av, s1) = la[0].clone();

                let lb = b.eval(s1);
                if lb.len() != 1 {
                    panic!("branching in AssertEq(rhs) unsupported");
                }
                let (bv, mut s2) = lb[0].clone();

                s2 = s2.with_pc(av.eq_to(bv));
                Vector::unit((None, s2))
            }

            Stmt::AssertBool(e) => {
                let (cond, s1) = eval_bool_expr(e, st);
                let s2 = s1.with_pc(cond);
                Vector::unit((None, s2))
            }

            Stmt::VarDecl { id, ty, init, .. } => {
                let vid = id.expect("variable id must be assigned during resolve");
                ty.assert_not_function("variable declaration");

                let mut out = Vector::new();

                // Evaluate initializer; branching is allowed
                let evals = init.eval(st);
                if evals.is_empty() {
                    panic!("initializer evaluation produced no result");
                }

                for (v, mut s1) in evals {
                    // Variables of non-scalar type are not supported yet
                    if !ty.is_scalar(&s1.ctx) {
                        panic!("non-scalar variable declaration not supported");
                    }

                    // Insert the initialized scalar value into the store
                    s1.store = s1.store.set(vid, StoreNode::Scalar(v));
                    out.push_back((None, s1));
                }

                out
            }

            Stmt::Assign { target, value } => {
                let evals = value.eval(st);
                if evals.len() != 1 {
                    panic!("branching RHS in Assign unsupported");
                }
                let (v, mut s1) = evals[0].clone();
                s1.store = write_to_lvalue(&s1.ctx, s1.store.clone(), &target, v);
                Vector::unit((None, s1))
            }

            Stmt::AndAssign { target, value } => {
                // Sequential: read current first, then evaluate RHS on post-read state.
                let as_expr = lvalue_to_expr(&target);
                let cur_vals = as_expr.eval(st);
                if cur_vals.len() != 1 {
                    panic!("branching read in AndAssign unsupported");
                }
                let (cur, s_after_read) = cur_vals[0].clone();

                let rhs_vals = value.eval(s_after_read);
                if rhs_vals.len() != 1 {
                    panic!("branching RHS in AndAssign unsupported");
                }
                let (rhs, mut s1) = rhs_vals[0].clone();

                let cond = BoolExpr::and(vec![cur.ne(SymExpr::Int(0)), rhs.ne(SymExpr::Int(0))]);
                let newv = SymExpr::Ite(
                    Box::new(cond),
                    Box::new(SymExpr::Int(1)),
                    Box::new(SymExpr::Int(0)),
                );
                s1.store = write_to_lvalue(&s1.ctx, s1.store.clone(), &target, newv);
                Vector::unit((None, s1))
            }

            Stmt::For { .. } => Vector::unit((None, st)),

            Stmt::Call { .. } => Vector::unit((None, st)),

            Stmt::Return(e) => {
                let vals = e.eval(st);
                if vals.is_empty() {
                    panic!("return expression produced no value");
                }
                let mut out = Vector::new();
                for (v, sret) in vals {
                    out.push_back((Some(v), sret.with_status(ExecStatus::Return)));
                }
                out
            }
        }
    }
}

impl Expr {
    pub fn eval(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        // Sequential binary eval helper
        fn eval_bin<F>(
            op_name: &'static str,
            lhs: Expr,
            rhs: Expr,
            state: SymState,
            f: F,
        ) -> Vector<(SymExpr, SymState)>
        where
            F: Fn(SymExpr, SymExpr) -> SymExpr,
        {
            let l = lhs.eval(state);
            if l.len() != 1 {
                panic!("branching in Binary({}) lhs unsupported", op_name);
            }
            let (lv, s1) = l[0].clone();

            let r = rhs.eval(s1);
            if r.len() != 1 {
                panic!("branching in Binary({}) rhs unsupported", op_name);
            }
            let (rv, s2) = r[0].clone();

            Vector::unit((f(lv, rv), s2))
        }

        match self {
            Expr::Int(k) => Vector::unit((SymExpr::Int(k as i128), state)),

            Expr::Paren(inner) => (*inner).eval(state),

            Expr::Path { ref_id, segments } => {
                if let Some(v) = state.store.query_scalar(&Expr::Path {
                    ref_id,
                    segments: segments.clone(),
                }) {
                    return Vector::unit((v, state));
                }
                let id = ref_id.expect("unresolved path in expression");
                let ty = state
                    .ctx
                    .query_type(id)
                    .cloned()
                    .unwrap_or_else(|| panic!("no static type for id {}", id));
                let sty = state.type_map(&ty).unwrap_or(SymType::F);
                let name = segments.last().cloned().unwrap_or_else(|| "tmp".into());
                Vector::unit((SymExpr::Var(name, sty), state))
            }

            Expr::Field { base, name, .. } => {
                let sid = match state.ctx.infer_expr_type(base.as_ref()) {
                    Some(Type::Path {
                        ref_id: Some(sid), ..
                    }) => sid,
                    _ => panic!("field base is not struct with resolved struct_id"),
                };
                let fid = state
                    .ctx
                    .field_id_of(sid, &name)
                    .unwrap_or_else(|| panic!("unknown field `{}` for struct_id {}", name, sid));
                let base_node = state
                    .query_expr_node(base.as_ref())
                    .unwrap_or_else(|| panic!("field base not found in store"));
                let child = match base_node {
                    StoreNode::Struct { fields } => fields.get(&fid).unwrap_or_else(|| {
                        panic!("field `{}` (id={}) not materialized", name, fid)
                    }),
                    _ => panic!("field base is not struct node"),
                };
                if let StoreNode::Scalar(se) = child {
                    Vector::unit((se.clone(), state))
                } else {
                    panic!("field `{}` is not scalar", name);
                }
            }

            Expr::Index(base, idx) => {
                let idx_val = match *idx {
                    Expr::Int(k) => k as usize,
                    _ => panic!("array index must be concrete usize literal"),
                };
                let base_node = state
                    .query_expr_node(base.as_ref())
                    .unwrap_or_else(|| panic!("array base not found in store"));
                match base_node {
                    StoreNode::Array { elems, .. } => {
                        let cell = elems
                            .get(&idx_val)
                            .unwrap_or_else(|| panic!("array elem {} uninitialized", idx_val));
                        if let StoreNode::Scalar(se) = cell {
                            Vector::unit((se.clone(), state))
                        } else {
                            panic!("array elem is not scalar");
                        }
                    }
                    _ => panic!("indexing requires array base"),
                }
            }

            Expr::Binary {
                op: BinOp::Add,
                lhs,
                rhs,
            } => eval_bin("Add", *lhs, *rhs, state, |a, b| a + b),
            Expr::Binary {
                op: BinOp::Sub,
                lhs,
                rhs,
            } => eval_bin("Sub", *lhs, *rhs, state, |a, b| a - b),
            Expr::Binary {
                op: BinOp::Mul,
                lhs,
                rhs,
            } => eval_bin("Mul", *lhs, *rhs, state, |a, b| a * b),

            Expr::Binary {
                op: BinOp::BitAnd,
                lhs,
                rhs,
            } => eval_bin("BitAnd", *lhs, *rhs, state, |a, b| {
                let cond = BoolExpr::and(vec![a.ne(SymExpr::Int(0)), b.ne(SymExpr::Int(0))]);
                SymExpr::Ite(
                    Box::new(cond),
                    Box::new(SymExpr::Int(1)),
                    Box::new(SymExpr::Int(0)),
                )
            }),

            Expr::Bool(_) | Expr::Binary { op: BinOp::Eq, .. } => {
                panic!("Boolean-valued expressions must be checked in Boolean contexts");
            }

            Expr::Call(callee, _args) => {
                // Function call may have side effects; evaluated sequentially if needed later.
                let (fid, name_hint) = match *callee {
                    Expr::Path {
                        ref_id: Some(fid),
                        ref segments,
                    } => (
                        fid,
                        segments.last().cloned().unwrap_or_else(|| "call".into()),
                    ),
                    _ => panic!("unsupported callee form for call"),
                };
                let (_params, ret_opt) = state
                    .ctx
                    .fn_sig(fid)
                    .cloned()
                    .unwrap_or_else(|| panic!("missing function signature for id {}", fid));
                let sty = if let Some(ret_ty) = ret_opt {
                    state.type_map(&ret_ty).unwrap_or(SymType::F)
                } else {
                    panic!("void-returning function used in expression");
                };
                Vector::unit((SymExpr::Var(format!("ret_of_{}", name_hint), sty), state))
            }
        }
    }
}

fn lvalue_to_expr(lv: &LValue) -> Expr {
    let mut e = Expr::Path {
        segments: lv.head.clone(),
        ref_id: lv.ref_id,
    };
    for t in &lv.tails {
        match t {
            LvTail::Field { name } => {
                e = Expr::Field {
                    base: Box::new(e),
                    name: name.clone(),
                    ref_id: None,
                }
            }
            LvTail::Index(idx) => {
                e = Expr::Index(Box::new(e), Box::new(idx.clone()));
            }
        }
    }
    e
}
