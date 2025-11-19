use im::Vector;

use crate::{
    ast::{BinOp, Expr, Func, LValue, LvTail, Member, Param, Stmt, Type},
    checker::symbolic::{
        context::{Context, PathKind},
        eval_index_const_or_err,
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
        store: &Store,
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
                let new_child = write_tail(ctx, store, child, cur_ty, &tails[1..], val);
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

                let idx =
                    eval_index_const_or_err(ctx, Some(store), idx_expr).unwrap_or_else(|| {
                        panic!(
                            "array index must be a concrete integer literal or constant identifier"
                        )
                    });
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

    let updated = write_tail(ctx, &store, root, &mut cur_ty, &lv.tails, val);
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

            Stmt::For {
                id,
                var: _,
                start,
                end,
                body,
            } => {
                // Enforce that the loop bounds are compile-time constants
                // (literals or constant identifiers).
                let lo = eval_index_const_or_err(&st.ctx, None, &start).unwrap_or_else(|| {
                    panic!(
                        "for-loop lower bound must be a constant integer or const identifier: `{:?}`",
                        start
                    )
                });
                let hi = eval_index_const_or_err(&st.ctx, None, &end).unwrap_or_else(|| {
                    panic!(
                        "for-loop upper bound must be a constant integer or const identifier: `{:?}`",
                        end
                    )
                });

                // Rust-style semantics: if lo >= hi, the loop body is skipped.
                if lo >= hi {
                    return Vector::unit((None, st));
                }

                let vid = id.expect("loop variable id must be assigned during resolve");

                // Start from the incoming state; single-path unrolling for now.
                let mut live: Vector<SymState> = Vector::unit(st);
                let mut terminals: Vector<(Option<SymExpr>, SymState)> = Vector::new();

                for k in lo..hi {
                    let mut next_live: Vector<SymState> = Vector::new();

                    for s in live.into_iter() {
                        let mut s_iter = s.clone();
                        s_iter.store = s_iter
                            .store
                            .set(vid, StoreNode::Scalar(SymExpr::Int(k as i128)));

                        let mut inner_live: Vector<SymState> = Vector::unit(s_iter);

                        for stmt in body.clone() {
                            let mut tmp: Vector<SymState> = Vector::new();
                            for s_inner in inner_live.into_iter() {
                                if !s_inner.is_active() {
                                    tmp.push_back(s_inner);
                                    continue;
                                }

                                let res = stmt.clone().execute(s_inner);
                                if res.is_empty() {
                                    panic!("loop body statement produced no successor states");
                                }
                                if res.len() != 1 {
                                    panic!("branching inside for-loop body is not supported");
                                }

                                let (ret, s_next) = res[0].clone();
                                if let Some(rv) = ret {
                                    // Propagate the return value and status out of the loop.
                                    terminals.push_back((
                                        Some(rv),
                                        s_next.with_status(ExecStatus::Return),
                                    ));
                                } else {
                                    tmp.push_back(s_next);
                                }
                            }
                            inner_live = tmp;
                            if inner_live.is_empty() {
                                break;
                            }
                        }

                        for s_final in inner_live {
                            next_live.push_back(s_final);
                        }
                    }

                    live = next_live;
                    // If a return has been produced, we can break out of the entire for-loop early.
                    if !terminals.is_empty() || live.is_empty() {
                        break;
                    }
                }

                if !terminals.is_empty() {
                    // Allow treating multiple returns as multiple paths; given your current
                    // single-path design, you may also panic when len != 1 if necessary.
                    return terminals;
                }

                if live.len() != 1 {
                    panic!("branching across for-loop iterations is not supported");
                }
                let s_final = live[0].clone();
                Vector::unit((None, s_final))
            }

            Stmt::Call { callee, args } => {
                // Statement-level calls are modeled as concrete invocations of
                // the target function or method. The callee may be a free
                // function or a struct method `x.m(...)`.

                // Evaluate arguments sequentially under single-path semantics.
                let mut s = st;
                let mut arg_vals = Vec::with_capacity(args.len());
                for arg in args {
                    let vals = arg.eval(s);
                    if vals.len() != 1 {
                        panic!("branching in call argument is not supported");
                    }
                    let (v, s1) = vals[0].clone();
                    arg_vals.push(v);
                    s = s1;
                }

                // Normalize the callee to an expression and resolve the target.
                let callee_expr = lvalue_to_expr(&callee);
                let (fid, receiver_info) = resolve_callee_expr(&s, &callee_expr);

                // Retrieve the callee body from the global context.
                let func = s
                    .ctx
                    .func_def(fid)
                    .cloned()
                    .unwrap_or_else(|| panic!("missing function body for id {}", fid));

                // Instantiate a callee state that shares context, store, and
                // accumulated path condition with the caller.
                let mut callee_state = s.clone();
                callee_state.status = ExecStatus::Step;

                // Initialize formal parameters from evaluated arguments.
                // For methods, the receiver node is aliased through `self`.
                let mut arg_iter = arg_vals.into_iter();
                let mut self_binding: Option<(i64, i64)> = None; // (caller_vid, callee_vid)

                for p in &func.params {
                    match p {
                        Param::SelfParam { id } => {
                            let callee_vid =
                                id.expect("self parameter id must be assigned during resolve");

                            let (caller_vid, struct_id) = receiver_info
                                .unwrap_or_else(|| panic!("self parameter without receiver"));

                            let recv_node = callee_state
                                .store
                                .get(caller_vid)
                                .cloned()
                                .unwrap_or_else(|| {
                                    panic!(
                                        "receiver variable id {} (struct_id={}) not found in store",
                                        caller_vid, struct_id
                                    )
                                });

                            callee_state.store =
                                callee_state.store.clone().set(callee_vid, recv_node);
                            self_binding = Some((caller_vid, callee_vid));
                        }

                        Param::Typed { id, ty, .. } => {
                            let callee_vid =
                                id.expect("parameter id must be assigned during resolve");
                            let value = arg_iter
                                .next()
                                .unwrap_or_else(|| panic!("insufficient arguments in call"));

                            if !ty.is_scalar(&callee_state.ctx) {
                                panic!(
                                    "non-scalar parameter types in calls are not yet supported: `{:?}`",
                                    ty
                                );
                            }

                            callee_state.store = callee_state
                                .store
                                .clone()
                                .set(callee_vid, StoreNode::Scalar(value));
                        }
                    }
                }

                if arg_iter.next().is_some() {
                    panic!("too many arguments supplied to call");
                }

                // Execute the callee under single-path semantics.
                let results = func.clone().execute(callee_state);
                if results.len() != 1 {
                    panic!("branching in function call is not supported");
                }
                let (_ret, mut s_end) = results[0].clone();

                // For methods, propagate the final `self` node back to the
                // receiver binding in the caller.
                if let Some((caller_vid, callee_vid)) = self_binding {
                    let node = s_end.store.get(callee_vid).cloned().unwrap_or_else(|| {
                        panic!(
                            "callee `self` binding id {} not found in final store",
                            callee_vid
                        )
                    });
                    s_end.store = s_end.store.clone().set(caller_vid, node);
                }

                // A statement-level call does not cause the caller to return.
                s_end.status = ExecStatus::Step;

                Vector::unit((None, s_end))
            }

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
                let idx_val = eval_index_const_or_err(&state.ctx, Some(&state.store), &idx)
                    .unwrap_or_else(|| {
                        panic!(
                            "array index must be a concrete integer literal, const identifier, or scalar store integer: `{:?}`",
                            idx
                        )
                    });
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

            Expr::Call(callee, args) => {
                // Calls in expression position are executed symbolically in the
                // same way as statement-level calls. The callee may be a free
                // function or a struct method. Side effects on the store are
                // preserved and the returned symbolic value is propagated.

                // Evaluate arguments sequentially under single-path semantics.
                let mut s = state;
                let mut arg_vals = Vec::with_capacity(args.len());
                for arg in args {
                    let vals = arg.eval(s);
                    if vals.len() != 1 {
                        panic!("branching in call argument is not supported");
                    }
                    let (v, s1) = vals[0].clone();
                    arg_vals.push(v);
                    s = s1;
                }

                // Resolve function identifier and, for methods, the receiver.
                let (fid, receiver_info) = resolve_callee_expr(&s, &callee);

                // Retrieve the callee body from the global context.
                let func = s
                    .ctx
                    .func_def(fid)
                    .cloned()
                    .unwrap_or_else(|| panic!("missing function body for id {}", fid));

                // Instantiate a callee state that shares context, store, and
                // accumulated path condition with the caller.
                let mut callee_state = s.clone();
                callee_state.status = ExecStatus::Step;

                // Initialize formal parameters from evaluated arguments. For
                // methods, the receiver node is aliased through `self`.
                let mut arg_iter = arg_vals.into_iter();
                let mut self_binding: Option<(i64, i64)> = None; // (caller_vid, callee_vid)

                for p in &func.params {
                    match p {
                        Param::SelfParam { id } => {
                            let callee_vid =
                                id.expect("self parameter id must be assigned during resolve");

                            let (caller_vid, struct_id) = receiver_info
                                .unwrap_or_else(|| panic!("self parameter without receiver"));

                            let recv_node = callee_state
                                .store
                                .get(caller_vid)
                                .cloned()
                                .unwrap_or_else(|| {
                                    panic!(
                                        "receiver variable id {} (struct_id={}) not found in store",
                                        caller_vid, struct_id
                                    )
                                });

                            callee_state.store =
                                callee_state.store.clone().set(callee_vid, recv_node);
                            self_binding = Some((caller_vid, callee_vid));
                        }

                        Param::Typed { id, ty, .. } => {
                            let callee_vid =
                                id.expect("parameter id must be assigned during resolve");
                            let value = arg_iter
                                .next()
                                .unwrap_or_else(|| panic!("insufficient arguments in call"));

                            if !ty.is_scalar(&callee_state.ctx) {
                                panic!(
                                    "non-scalar parameter types in calls are not yet supported: `{:?}`",
                                    ty
                                );
                            }

                            callee_state.store = callee_state
                                .store
                                .clone()
                                .set(callee_vid, StoreNode::Scalar(value));
                        }
                    }
                }

                if arg_iter.next().is_some() {
                    panic!("too many arguments supplied to call");
                }

                // Execute the callee under single-path semantics.
                let results = func.clone().execute(callee_state);
                if results.len() != 1 {
                    panic!("branching in expression-level call is not supported");
                }
                let (ret_opt, mut s_end) = results[0].clone();

                // Propagate the final `self` node back to the receiver binding.
                if let Some((caller_vid, callee_vid)) = self_binding {
                    let node = s_end.store.get(callee_vid).cloned().unwrap_or_else(|| {
                        panic!(
                            "callee `self` binding id {} not found in final store",
                            callee_vid
                        )
                    });
                    s_end.store = s_end.store.clone().set(caller_vid, node);
                }

                // Expression position requires a return value.
                let ret =
                    ret_opt.unwrap_or_else(|| panic!("void-returning function used in expression"));

                // The caller continues execution after the call.
                s_end.status = ExecStatus::Step;

                Vector::unit((ret, s_end))
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
/// Resolves a callee expression in either statement or expression position.
///
/// Returns the function identifier and, for method calls, the pair
/// `(receiver_vid, struct_id)` describing the receiver variable and its type.
fn resolve_callee_expr(state: &SymState, callee: &Expr) -> (i64, Option<(i64, i64)>) {
    match callee {
        // Free function: f(...)
        Expr::Path {
            ref_id: Some(fid), ..
        } => {
            if state.ctx.fn_sig(*fid).is_none() {
                panic!("callee id {} does not denote a function", fid);
            }
            (*fid, None)
        }

        // Method call: x.m(...). The field may already be resolved to a
        // function id or still carry only the member name.
        Expr::Field { base, name, ref_id } => {
            // Infer the static type of the receiver expression.
            let base_ty = state.ctx.infer_expr_type(base.as_ref()).unwrap_or_else(|| {
                panic!("failed to infer static type for method receiver in call")
            });

            let struct_id = match state.ctx.classify_type(&base_ty) {
                Ok(PathKind::Struct(sid)) => sid,
                Ok(PathKind::Builtin) => {
                    panic!(
                        "method receiver must be a struct value, got builtin type `{:?}`",
                        base_ty
                    )
                }
                Err(e) => {
                    panic!("method receiver has invalid type `{:?}`: {}", base_ty, e)
                }
            };

            // Restrict the receiver to be a simple variable path for now.
            let receiver_vid = match base.as_ref() {
                Expr::Path {
                    ref_id: Some(vid), ..
                } => *vid,
                _ => panic!("method receiver must be a struct-valued variable path"),
            };

            // If the field has already been resolved to a function id, prefer it.
            if let Some(fid) = ref_id {
                if state.ctx.fn_sig(*fid).is_some() {
                    return (*fid, Some((receiver_vid, struct_id)));
                }
            }

            // Otherwise, look up the method in the struct member table by name.
            let members = state.ctx.struct_members(struct_id).unwrap_or_else(|| {
                panic!(
                    "no member table recorded for struct_id {} when resolving method `{}`",
                    struct_id, name
                )
            });

            let mi = members.get(name).unwrap_or_else(|| {
                panic!(
                    "unknown method `{}` on struct_id {} while resolving call",
                    name, struct_id
                )
            });

            let fid = mi
                .as_func_id()
                .unwrap_or_else(|| panic!("member `{}` is not a method", name));

            (fid, Some((receiver_vid, struct_id)))
        }

        _ => {
            panic!("unsupported callee form for call resolution");
        }
    }
}
