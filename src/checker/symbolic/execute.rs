use im::Vector;

use crate::{
    ast::{BinOp, Expr, Func, LValue, LvTail, Member, Param, Stmt, Type},
    checker::symbolic::{
        context::{Context, PathKind},
        eval_index_const_or_err,
        expr::{BoolExpr, FIELD_MODULUS, SymExpr, SymType},
        state::{ExecStatus, MemoryEventKind, Store, StoreNode, SymState},
    },
    utils::SolverKind,
};

/// Logical place of a method receiver inside the store:
/// root variable and a sequence of field / index steps.
#[derive(Clone, Debug)]
struct ReceiverPlace {
    root_vid: i64,
    steps: Vec<ReceiverStep>,
}

#[derive(Clone, Debug)]
enum ReceiverStep {
    Field(i64),
    Index(usize),
}

fn sym_bounds(sty: &SymType) -> Option<(i128, i128, usize)> {
    match *sty {
        SymType::Bool => Some((0, 1, 1)),
        SymType::Uint(w) if w > 0 && w < 127 => {
            let max = 1_i128.checked_shl(w as u32)?.saturating_sub(1);
            Some((0, max, w))
        }
        SymType::Int(w) if w > 0 && w < 127 => {
            let hi = 1_i128.checked_shl((w - 1) as u32)?.saturating_sub(1);
            let lo = -(1_i128.checked_shl((w - 1) as u32)?);
            Some((lo, hi, w))
        }
        _ => None,
    }
}

/// Drop a field modulus reduction when the inferred range already lies inside the field.
fn mod_if_needed(expr: SymExpr, state: &SymState) -> SymExpr {
    if let Some((lo, hi)) = state.symexpr_range(&expr) {
        if lo >= 0 && hi < FIELD_MODULUS {
            return expr;
        }
    }
    expr.mod_field()
}

/// Helper to enforce single-result evaluations.
fn expect_single<T: Clone>(vals: Vector<T>, ctx: &str) -> T {
    if vals.len() != 1 {
        panic!("{} produced {} results (expected 1)", ctx, vals.len());
    }
    vals[0].clone()
}

/// Decompose an 8-bit value into fresh Boolean bits and return (bits, reconstructed_sum, state).
fn decompose_byte(mut state: SymState, prefix: &str) -> (Vec<SymExpr>, SymExpr, SymState) {
    let mut bits = Vec::with_capacity(8);
    let mut acc = SymExpr::Int(0);
    for i in 0..8 {
        let bit = state.fresh_sym(&format!("{}_{}", prefix, i), SymType::Bool);
        state = state.with_pc(BoolExpr::Range {
            value: bit.clone(),
            min: 0,
            max: 1,
            bits: Some(1),
        });
        acc = acc + bit.clone() * SymExpr::Int(1_i128 << (i as u32));
        bits.push(bit);
    }
    (bits, acc, state)
}

/// Decompose a u32 value into Boolean bits and return (bits, updated_state).
fn decompose_u32_bits(state: SymState, value: SymExpr, prefix: &str) -> (Vec<SymExpr>, SymState) {
    state.decompose_u32_bits_cached(value, prefix)
}

/// Constrain `out = lhs AND rhs` over 8-bit values via bit decomposition.
fn constrain_byte_and(state: SymState, out: SymExpr, lhs: SymExpr, rhs: SymExpr) -> SymState {
    let mut state = state;
    for v in [out.clone(), lhs.clone(), rhs.clone()] {
        state = state.with_pc(BoolExpr::Range {
            value: v,
            min: 0,
            max: 255,
            bits: Some(8),
        });
    }

    let (lhs_bits, lhs_acc, state) = decompose_byte(state, "byte_and_l");
    let (rhs_bits, rhs_acc, state) = decompose_byte(state, "byte_and_r");
    let (out_bits, out_acc, mut state) = decompose_byte(state, "byte_and_out");

    for ((lb, rb), ob) in lhs_bits.iter().zip(rhs_bits.iter()).zip(out_bits.iter()) {
        let prod = SymExpr::Mul(vec![lb.clone(), rb.clone()]);
        state = state.with_pc(ob.clone().eq_to(prod));
    }

    state = state.with_pc(lhs.eq_to(lhs_acc));
    state = state.with_pc(rhs.eq_to(rhs_acc));
    state.with_pc(out.eq_to(out_acc))
}

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
            (_, LvTail::MapIndex(_, _)) => {
                panic!("assignment through map indexing is not supported");
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
    fn execute(self, state: SymState) -> Vector<(Option<SymExpr>, SymState)> {
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
        // Any state that reaches the end of the body without an explicit return
        // is treated as a terminal fall-through with no return value.
        for st in live {
            terminals.push_back((None, st));
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
            fn cmp_int<F>(lhs: &SymExpr, rhs: &SymExpr, f: F) -> Option<BoolExpr>
            where
                F: Fn(i128, i128) -> bool,
            {
                match (lhs, rhs) {
                    (SymExpr::Int(a), SymExpr::Int(b)) => Some(BoolExpr::Bool(f(*a, *b))),
                    _ => None,
                }
            }

            match e {
                Expr::Bool(b) => (BoolExpr::Bool(b), st),

                Expr::Paren(inner) => eval_bool_expr(*inner, st),

                Expr::Binary { op, lhs, rhs } => {
                    // Sequential: eval lhs then rhs on resulting state.
                    let (lv, s1) = expect_single(lhs.eval(st), "BoolExpr(lhs)");
                    let (rv, s2) = expect_single(rhs.eval(s1), "BoolExpr(rhs)");

                    let cond = match op {
                        BinOp::Eq => {
                            cmp_int(&lv, &rv, |a, b| a == b).unwrap_or_else(|| lv.eq_to(rv))
                        }
                        BinOp::Ne => cmp_int(&lv, &rv, |a, b| a != b).unwrap_or_else(|| lv.ne(rv)),
                        BinOp::Lt => cmp_int(&lv, &rv, |a, b| a < b).unwrap_or_else(|| lv.lt(rv)),
                        BinOp::Le => cmp_int(&lv, &rv, |a, b| a <= b).unwrap_or_else(|| lv.le(rv)),
                        BinOp::Gt => cmp_int(&lv, &rv, |a, b| a > b).unwrap_or_else(|| lv.gt(rv)),
                        BinOp::Ge => cmp_int(&lv, &rv, |a, b| a >= b).unwrap_or_else(|| lv.ge(rv)),

                        // Logical operators treat non-zero as true.
                        BinOp::And => {
                            if let Some(b) = cmp_int(&lv, &rv, |a, b| a != 0 && b != 0) {
                                return (b, s2);
                            }
                            let c1 = lv.ne(SymExpr::Int(0));
                            let c2 = rv.ne(SymExpr::Int(0));
                            BoolExpr::and(vec![c1, c2])
                        }
                        BinOp::Or => {
                            if let Some(b) = cmp_int(&lv, &rv, |a, b| a != 0 || b != 0) {
                                return (b, s2);
                            }
                            let c1 = lv.ne(SymExpr::Int(0));
                            let c2 = rv.ne(SymExpr::Int(0));
                            BoolExpr::or(vec![c1, c2])
                        }

                        // Not a Boolean operator in this context.
                        other => {
                            panic!("non-Boolean binary operator in condition: `{:?}`", other);
                        }
                    };

                    (cond, s2)
                }

                _ => panic!("unsupported Boolean expression in condition: `{:?}`", e),
            }
        }

        /// Evaluate a scalar compound assignment like `x op= e` with branching.
        /// The lvalue is read first, then the RHS is evaluated on each post-read state.
        /// For every pair (cur, rhs) the `combine` function builds the new scalar value.
        fn eval_scalar_assign_update<F>(
            target: &LValue,
            value: &Expr,
            st: SymState,
            op_name: &'static str,
            combine: F,
        ) -> Vector<(Option<SymExpr>, SymState)>
        where
            F: Fn(SymExpr, SymExpr) -> SymExpr,
        {
            // Read current value of the lvalue as an expression.
            let as_expr = lvalue_to_expr(target);
            let cur_vals = as_expr.eval(st);
            if cur_vals.is_empty() {
                panic!("{}: lvalue read produced no result", op_name);
            }

            let mut out: Vector<(Option<SymExpr>, SymState)> = Vector::new();

            // For each possible current value, evaluate RHS sequentially.
            for (cur, s_after_read) in cur_vals {
                let rhs_vals = value.clone().eval(s_after_read);
                if rhs_vals.is_empty() {
                    panic!("{}: RHS produced no result", op_name);
                }

                for (rhs, mut s_rhs) in rhs_vals {
                    let newv = combine(cur.clone(), rhs);
                    s_rhs.store = write_to_lvalue(&s_rhs.ctx, s_rhs.store.clone(), target, newv);
                    out.push_back((None, s_rhs));
                }
            }

            out
        }

        match self {
            Stmt::AssertEq(a, b) => {
                // Sequential: lhs → rhs
                let (av, s1) = expect_single(a.eval(st), "AssertEq(lhs)");
                let (bv, s2) = expect_single(b.eval(s1), "AssertEq(rhs)");

                let cond = av.eq_to(bv);
                let states = Self::split_on_bool_mul_eq_zero(s2, cond);

                let mut out = Vector::new();
                for s in states {
                    out.push_back((None, s));
                }
                out
            }

            Stmt::AssertBool(e) => {
                // Boolean expressions: literals, comparisons, and && / ||.
                if matches!(
                    &e,
                    Expr::Bool(_)
                        | Expr::Binary {
                            op: BinOp::Eq
                                | BinOp::Ne
                                | BinOp::Lt
                                | BinOp::Le
                                | BinOp::Gt
                                | BinOp::Ge
                                | BinOp::And
                                | BinOp::Or,
                            ..
                        }
                ) {
                    let (cond, s1) = eval_bool_expr(e, st);
                    let s2 = s1.with_pc(cond);
                    return Vector::unit((None, s2));
                }

                // Lvalue-like expressions: path / field / index chain.
                match &e {
                    Expr::Path { .. } | Expr::Field { .. } | Expr::Index(..) => {
                        let vals = e.clone().eval(st);
                        if vals.len() != 1 {
                            panic!("branching in AssertBool(lvalue) is unsupported");
                        }
                        let (v, s1) = vals[0].clone();
                        // Other lvalues are constrained to be 0/1.
                        let zero = SymExpr::Int(0);
                        let one = SymExpr::Int(1);
                        let guard = BoolExpr::or(vec![v.clone().eq_to(zero), v.eq_to(one)]);
                        let s2 = s1.with_pc(guard);
                        Vector::unit((None, s2))
                    }

                    other => {
                        panic!(
                            "unsupported Boolean expression in AssertBool: `{:?}`",
                            other
                        );
                    }
                }
            }

            Stmt::AssertZero(e) => {
                let (v, s1) = expect_single(e.eval(st), "assert_zero");
                let cond = v.eq_to(SymExpr::Int(0));
                let mut out = Vector::new();
                for s in Self::split_on_bool_mul_eq_zero(s1, cond) {
                    out.push_back((None, s));
                }
                out
            }

            Stmt::AssertRange { value, ty } => {
                let sym_ty = st
                    .ctx
                    .builtin_type_to_sym_type(&ty)
                    .unwrap_or_else(|| panic!("assert_range requires a builtin scalar type"));
                let evals = value.eval(st);
                if evals.is_empty() {
                    panic!("assert_range expression produced no value");
                }
                let (min, max, bits) = sym_bounds(&sym_ty)
                    .unwrap_or_else(|| panic!("assert_range does not support type {:?}", sym_ty));

                let mut out = Vector::new();
                for (v, s1) in evals {
                    let cond = BoolExpr::Range {
                        value: v,
                        min,
                        max,
                        bits: Some(bits),
                    };
                    out.push_back((None, s1.with_pc(cond)));
                }
                out
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
                let (v, mut s1) = expect_single(value.eval(st), "Assign RHS");
                s1.store = write_to_lvalue(&s1.ctx, s1.store.clone(), &target, v);
                Vector::unit((None, s1))
            }

            Stmt::AndAssign { target, value } => {
                // Boolean-style `&=` over 0/1-encoded integers.
                eval_scalar_assign_update(&target, &value, st, "AndAssign", |cur, rhs| {
                    let cond =
                        BoolExpr::and(vec![cur.ne(SymExpr::Int(0)), rhs.ne(SymExpr::Int(0))]);
                    SymExpr::ite(cond, SymExpr::Int(1), SymExpr::Int(0))
                })
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Evaluate the Boolean condition under sequential semantics.
                let (bcond, s_after_cond) = eval_bool_expr(cond, st);

                // Execute a straight-line block while preserving the multi-path
                // propagation discipline used in function-level symbolic execution.
                fn exec_block(
                    mut live: Vector<SymState>,
                    block: &Vec<Stmt>,
                ) -> Vector<(Option<SymExpr>, SymState)> {
                    let mut out: Vector<(Option<SymExpr>, SymState)> = Vector::new();

                    for stmt in block.clone() {
                        let mut next_live: Vector<SymState> = Vector::new();

                        for s in live.into_iter() {
                            if !s.is_active() {
                                // Inactive states bypass the computation and are forwarded unchanged.
                                next_live.push_back(s);
                                continue;
                            }

                            let res = stmt.clone().execute(s);
                            if res.is_empty() {
                                panic!("block statement produced no successor states");
                            }

                            for (ret, s_next) in res {
                                if s_next.is_terminal() {
                                    // Terminal states (return/break) are emitted directly to the caller.
                                    out.push_back((ret, s_next));
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

                    // Remaining non-terminal states are returned with an empty return value.
                    for s in live {
                        out.push_back((None, s));
                    }

                    out
                }

                // Construct the symbolic states for the two branches with
                // their respective path conditions.
                let const_guard = if let BoolExpr::Bool(b) = &bcond {
                    Some(*b)
                } else {
                    None
                };
                let then_start = s_after_cond.clone().with_pc(bcond.clone());
                let else_start = s_after_cond.with_pc(bcond.not());

                // Short-circuit constant branches to avoid unnecessary path explosion.
                if const_guard == Some(true) {
                    return exec_block(Vector::unit(then_start), &then_branch);
                }
                if const_guard == Some(false) {
                    return exec_block(Vector::unit(else_start), &else_branch);
                }

                let mut res_then = exec_block(Vector::unit(then_start), &then_branch);
                let res_else = exec_block(Vector::unit(else_start), &else_branch);

                // Combine all successors from both branches.
                res_then.append(res_else);
                res_then
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

                // Start from the incoming state; now we allow branching across iterations.
                let mut live: Vector<SymState> = Vector::unit(st);
                let mut terminals: Vector<(Option<SymExpr>, SymState)> = Vector::new();

                for k in lo..hi {
                    let mut next_live: Vector<SymState> = Vector::new();

                    for s in live.into_iter() {
                        // Inactive states just flow through the loop unchanged.
                        if !s.is_active() {
                            next_live.push_back(s);
                            continue;
                        }

                        // Bind loop variable for this iteration.
                        let mut s_iter = s.clone();
                        s_iter.store = s_iter
                            .store
                            .set(vid, StoreNode::Scalar(SymExpr::Int(k as i128)));

                        // Execute the body as a mini "block executor" with branching.
                        let mut inner_live: Vector<SymState> = Vector::unit(s_iter);

                        for stmt in body.clone() {
                            let mut tmp: Vector<SymState> = Vector::new();

                            for s_inner in inner_live.into_iter() {
                                if !s_inner.is_active() {
                                    // Terminal/ inactive states flow out of the body unchanged.
                                    tmp.push_back(s_inner);
                                    continue;
                                }

                                let res = stmt.clone().execute(s_inner);
                                if res.is_empty() {
                                    panic!("loop body statement produced no successor states");
                                }

                                for (ret, s_next) in res {
                                    if let Some(rv) = ret {
                                        // Return from inside the loop: record as terminal.
                                        terminals.push_back((
                                            Some(rv),
                                            s_next.with_status(ExecStatus::Return),
                                        ));
                                    } else if s_next.is_terminal() {
                                        // Other terminal statuses (e.g., Break/Continue if added later).
                                        terminals.push_back((None, s_next));
                                    } else {
                                        tmp.push_back(s_next);
                                    }
                                }
                            }

                            inner_live = tmp;
                            if inner_live.is_empty() {
                                break;
                            }
                        }

                        // States that survive the whole body go to the next iteration.
                        for s_final in inner_live {
                            next_live.push_back(s_final);
                        }
                    }

                    live = next_live;
                    // If a return has been produced, or nothing remains live, exit the loop early.
                    if !terminals.is_empty() || live.is_empty() {
                        break;
                    }
                }

                // Collect all terminal states (from returns etc.) and non-terminal ones
                // that reached the end of the loop.
                let mut out: Vector<(Option<SymExpr>, SymState)> = Vector::new();
                for t in terminals {
                    out.push_back(t);
                }
                for s_final in live {
                    out.push_back((None, s_final));
                }

                out
            }
            Stmt::Lookup { chip, opcode, args } => {
                let chip_name = chip
                    .last()
                    .map(|c| c.to_ascii_lowercase())
                    .unwrap_or_else(|| "".to_string());

                if chip_name == "bytechip" {
                    if args.len() < 2 {
                        panic!("ByteChip lookup expects at least two payload arguments");
                    }

                    let (opcode_val, mut state_after_opcode) =
                        expect_single(opcode.eval(st), "lookup opcode");
                    let opcode_int = match opcode_val {
                        SymExpr::Int(k) => k,
                        other => panic!("opcode must be an integer literal, got {:?}", other),
                    };

                    let mut payload_vals = Vec::new();
                    for e in args.into_iter() {
                        let (v, s_next) =
                            expect_single(e.eval(state_after_opcode.clone()), "lookup payload");
                        payload_vals.push(v);
                        state_after_opcode = s_next;
                    }

                    match opcode_int {
                        0 => {
                            let len = payload_vals.len();
                            if len < 2 {
                                panic!("ByteChip opcode 0 requires two payload values");
                            }

                            let mut s_cur = state_after_opcode;
                            for v in payload_vals[len - 2..].iter() {
                                s_cur = s_cur.with_pc(BoolExpr::Range {
                                    value: v.clone(),
                                    min: 0,
                                    max: 255,
                                    bits: Some(8),
                                });
                            }
                            Vector::unit((None, s_cur))
                        }
                        1 => {
                            if payload_vals.len() < 3 {
                                panic!("ByteChip opcode 1 (AND) requires three payload values");
                            }
                            let mut s_cur = state_after_opcode;
                            let out = payload_vals[0].clone();
                            let lhs = payload_vals[1].clone();
                            let rhs = payload_vals[2].clone();
                            s_cur = constrain_byte_and(s_cur, out, lhs, rhs);
                            Vector::unit((None, s_cur))
                        }
                        other => panic!("unsupported ByteChip opcode {}", other),
                    }
                } else if let Some(meta) = st.ctx.memory_chip(&chip_name).cloned() {
                    if args.len() < 3 {
                        panic!("Memory send/receive expects clk, addr, value");
                    }

                    let (opcode_val, mut state_after_opcode) =
                        expect_single(opcode.eval(st), "lookup opcode");
                    if !matches!(opcode_val, SymExpr::Int(_)) {
                        panic!(
                            "memory lookup opcode must be an integer literal, got {:?}",
                            opcode_val
                        );
                    }

                    let mut payload_vals = Vec::new();
                    for e in args.into_iter() {
                        let (v, s_next) =
                            expect_single(e.eval(state_after_opcode.clone()), "lookup payload");
                        payload_vals.push(v);
                        state_after_opcode = s_next;
                    }

                    let clk = payload_vals[0].clone();
                    let addr = payload_vals[1].clone();
                    let val = payload_vals[2].clone();

                    state_after_opcode =
                        state_after_opcode.add_memory_event(meta.kind, clk, addr, val);
                    Vector::unit((None, state_after_opcode))
                } else {
                    panic!("unsupported lookup chip `{:?}`", chip);
                }
            }
            Stmt::Call { callee, args } => {
                // Normalize callee to an expression once.
                let callee_expr = lvalue_to_expr(&callee);

                // Try builtin calls first. Arguments are evaluated only if the callee
                // is recognized as a builtin.
                if let Some(res) = try_eval_builtin_call(st.clone(), &callee_expr, args.clone()) {
                    if res.is_empty() {
                        panic!("builtin statement-level call produced no successor states");
                    }
                    let mut out = Vector::new();
                    for (_v, s1) in res {
                        out.push_back((None, s1));
                    }
                    return out;
                }

                // Regular function or method call: parameter handling is type-directed.
                let results = eval_regular_call(st, callee_expr, args);
                if results.is_empty() {
                    panic!("statement-level call produced no successor states");
                }

                let mut out: Vector<(Option<SymExpr>, SymState)> = Vector::new();
                for (_ret_opt, s_end) in results {
                    out.push_back((None, s_end));
                }

                out
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

impl Stmt {
    /// Splits on constraints of the form b * rest == 0 with a single Bool factor.
    fn split_on_bool_mul_eq_zero(state: SymState, cond: BoolExpr) -> Vector<SymState> {
        fn extract_bool_factor(lhs: SymExpr, rhs: SymExpr) -> Option<(SymExpr, SymExpr)> {
            fn handle_product(prod: SymExpr) -> Option<(SymExpr, SymExpr)> {
                let factors = match prod {
                    SymExpr::Mul(vs) => vs,
                    _ => return None,
                };

                let mut bool_idx: Option<usize> = None;
                for (i, f) in factors.iter().enumerate() {
                    if let SymExpr::Var(_, SymType::Bool) = f {
                        if bool_idx.is_some() {
                            return None;
                        }
                        bool_idx = Some(i);
                    }
                }
                let idx = bool_idx?;

                let mut rest = Vec::new();
                let mut bool_factor: Option<SymExpr> = None;
                for (i, f) in factors.into_iter().enumerate() {
                    if i == idx {
                        bool_factor = Some(f);
                    } else {
                        rest.push(f);
                    }
                }

                let b = bool_factor?;
                let rest_expr = match rest.len() {
                    0 => SymExpr::Int(1),
                    1 => rest.into_iter().next().unwrap(),
                    _ => SymExpr::Mul(rest),
                };
                Some((b, rest_expr))
            }

            match (lhs.clone(), rhs.clone()) {
                (SymExpr::Mul(_), SymExpr::Int(0)) => handle_product(lhs),
                (SymExpr::Int(0), SymExpr::Mul(_)) => handle_product(rhs),
                _ => None,
            }
        }

        match cond.clone() {
            BoolExpr::Eq(lhs, rhs) => {
                if let Some((bool_var, rest)) = extract_bool_factor(lhs, rhs) {
                    let zero = SymExpr::Int(0);
                    let one = SymExpr::Int(1);

                    let cond_b0 = bool_var.clone().eq_to(zero.clone());
                    let cond_b1 = bool_var.eq_to(one);
                    let cond_r0 = rest.eq_to(zero);

                    let mut out = Vector::new();
                    let s1 = state.clone().with_pc(cond_b0);
                    out.push_back(s1);
                    let s2 = state.with_pc(cond_b1).with_pc(cond_r0);
                    out.push_back(s2);
                    return out;
                }
            }
            _ => {}
        }

        Vector::unit(state.with_pc(cond))
    }
}
impl Expr {
    pub fn eval(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        /// Sequential binary eval helper that allows branching on both sides.
        /// For each left result (lv, s1) and each right result (rv, s2),
        /// produces one combined expression f(lv, rv) under state s2.
        fn eval_bin<F>(
            op_name: &'static str,
            lhs: Expr,
            rhs: Expr,
            state: SymState,
            f: F,
        ) -> Vector<(SymExpr, SymState)>
        where
            F: Fn(SymExpr, SymExpr, &SymState) -> SymExpr,
        {
            // First evaluate lhs under the incoming state.
            let l_res = lhs.eval(state);
            if l_res.is_empty() {
                panic!("Binary({}) lhs produced no result", op_name);
            }

            let mut out: Vector<(SymExpr, SymState)> = Vector::new();

            // For each lhs result, evaluate rhs sequentially on its state.
            for (lv, s1) in l_res {
                let r_res = rhs.clone().eval(s1);
                if r_res.is_empty() {
                    panic!("Binary({}) rhs produced no result", op_name);
                }

                for (rv, s2) in r_res {
                    let combined = f(lv.clone(), rv, &s2);
                    out.push_back((combined, s2));
                }
            }

            out
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
                if let Some(cid) = ref_id {
                    if let Some(k) = state.ctx.const_int(cid) {
                        return Vector::unit((SymExpr::Int(k as i128), state));
                    }
                }
                if ref_id.is_none() {
                    if let Some(last) = segments.last() {
                        if let Some((val, _ty)) = state.ctx.builtin_const(last) {
                            return Vector::unit((val, state));
                        }
                    }
                    panic!("unresolved path in expression: {:?}", segments);
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
                if let Expr::MapIndex {
                    base: map_base,
                    keys,
                } = base.as_ref()
                {
                    if keys.len() != 2 {
                        panic!("map index expects exactly two keys (timestamp, addr)");
                    }

                    let (clk_prev, val, s_next) = eval_map_index_projection(
                        state,
                        map_base.as_ref(),
                        keys[0].clone(),
                        keys[1].clone(),
                        name.as_str(),
                    );

                    let out = match name.as_str() {
                        "clk_prev" | "0" => clk_prev,
                        "value" | "1" => val,
                        other => panic!("unknown map projection `{}`", other),
                    };

                    return Vector::unit((out, s_next));
                }

                let sid = match state.infer_expr_type(base.as_ref()) {
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
                            panic!("array elem is not scalar: {:?} (index: {:?})", base, idx);
                        }
                    }
                    _ => panic!("indexing requires array base"),
                }
            }
            Expr::MapIndex { base: _, keys } => {
                panic!(
                    "map index must be projected via `.clk_prev` or `.value`, found {:?}",
                    keys
                );
            }
            Expr::Binary {
                op: BinOp::Add,
                lhs,
                rhs,
            } => {
                // Decide field vs integer addition by static type.
                let bin = Expr::Binary {
                    op: BinOp::Add,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                if state.is_field_expr(&bin) {
                    eval_bin("Add", *lhs, *rhs, state, |a, b, s| mod_if_needed(a + b, s))
                } else {
                    eval_bin("Add", *lhs, *rhs, state, |a, b, _| a + b)
                }
            }

            Expr::Binary {
                op: BinOp::Sub,
                lhs,
                rhs,
            } => {
                // Field subtraction is modeled modulo the field prime.
                let bin = Expr::Binary {
                    op: BinOp::Sub,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                if state.is_field_expr(&bin) {
                    eval_bin("Sub", *lhs, *rhs, state, |a, b, s| mod_if_needed(a - b, s))
                } else {
                    eval_bin("Sub", *lhs, *rhs, state, |a, b, _| a - b)
                }
            }

            Expr::Binary {
                op: BinOp::Mul,
                lhs,
                rhs,
            } => {
                let bin = Expr::Binary {
                    op: BinOp::Mul,
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };

                if state.is_field_expr(&bin) {
                    let lhs_ty = state.infer_expr_type(lhs.as_ref());
                    let rhs_ty = state.infer_expr_type(rhs.as_ref());

                    let use_mod = match (lhs_ty, rhs_ty) {
                        (Some(lt), Some(rt)) => {
                            let sty_l = state.type_map(&lt).ok();
                            let sty_r = state.type_map(&rt).ok();
                            match (sty_l, sty_r) {
                                (Some(sl), Some(sr)) => !Self::product_safe_without_mod(&sl, &sr),
                                _ => true,
                            }
                        }
                        _ => true,
                    };

                    if use_mod {
                        eval_bin("Mul", *lhs, *rhs, state, |a, b, s| mod_if_needed(a * b, s))
                    } else {
                        eval_bin("Mul", *lhs, *rhs, state, |a, b, _| a * b)
                    }
                } else {
                    eval_bin("Mul", *lhs, *rhs, state, |a, b, _| a * b)
                }
            }

            Expr::Binary {
                op: BinOp::BitAnd,
                lhs,
                rhs,
            } => eval_bin("BitAnd", *lhs, *rhs, state, |a, b, _| {
                let cond = BoolExpr::and(vec![a.ne(SymExpr::Int(0)), b.ne(SymExpr::Int(0))]);
                SymExpr::Ite(
                    Box::new(cond),
                    Box::new(SymExpr::Int(1)),
                    Box::new(SymExpr::Int(0)),
                )
            }),

            // Treat a literal Boolean as 0/1.
            Expr::Bool(b) => {
                let cond = BoolExpr::Bool(b);
                let v = cond.as_int();
                Vector::unit((v, state))
            }

            // Equality as 0/1.
            Expr::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } => eval_bin("Eq", *lhs, *rhs, state, |a, b, _| a.eq_to(b).as_int()),

            // Inequality as 0/1.
            Expr::Binary {
                op: BinOp::Ne,
                lhs,
                rhs,
            } => eval_bin("Ne", *lhs, *rhs, state, |a, b, _| a.ne(b).as_int()),

            // Less-than as 0/1.
            Expr::Binary {
                op: BinOp::Lt,
                lhs,
                rhs,
            } => eval_bin("Lt", *lhs, *rhs, state, |a, b, _| a.lt(b).as_int()),

            // Less-or-equal as 0/1.
            Expr::Binary {
                op: BinOp::Le,
                lhs,
                rhs,
            } => eval_bin("Le", *lhs, *rhs, state, |a, b, _| a.le(b).as_int()),

            // Greater-than as 0/1.
            Expr::Binary {
                op: BinOp::Gt,
                lhs,
                rhs,
            } => eval_bin("Gt", *lhs, *rhs, state, |a, b, _| a.gt(b).as_int()),

            // Greater-or-equal as 0/1.
            Expr::Binary {
                op: BinOp::Ge,
                lhs,
                rhs,
            } => eval_bin("Ge", *lhs, *rhs, state, |a, b, _| a.ge(b).as_int()),

            // Logical AND (&&) as 0/1 using non-zero test.
            Expr::Binary {
                op: BinOp::And,
                lhs,
                rhs,
            } => eval_bin("And", *lhs, *rhs, state, |a, b, _| {
                let c1 = a.ne(SymExpr::Int(0));
                let c2 = b.ne(SymExpr::Int(0));
                BoolExpr::and(vec![c1, c2]).as_int()
            }),

            // Logical OR (||) as 0/1 using non-zero test.
            Expr::Binary {
                op: BinOp::Or,
                lhs,
                rhs,
            } => eval_bin("Or", *lhs, *rhs, state, |a, b, _| {
                let c1 = a.ne(SymExpr::Int(0));
                let c2 = b.ne(SymExpr::Int(0));
                BoolExpr::or(vec![c1, c2]).as_int()
            }),

            Expr::Call(callee, args) => {
                // Move out the callee expression once.
                let callee_expr = *callee;

                // Try builtin call first. Arguments are evaluated only if the callee
                // is recognized as a builtin.
                if let Some(res) = try_eval_builtin_call(state.clone(), &callee_expr, args.clone())
                {
                    return res;
                }

                // Regular function or method call with type-directed parameter binding.
                let results = eval_regular_call(state, callee_expr, args);
                if results.is_empty() {
                    panic!("expression-level call produced no successor states");
                }

                let mut out: Vector<(SymExpr, SymState)> = Vector::new();
                for (ret_opt, s_end) in results {
                    let ret = ret_opt
                        .unwrap_or_else(|| panic!("void-returning function used in expression"));
                    out.push_back((ret, s_end));
                }

                out
            }
        }
    }

    /// Returns an upper bound on |v| for the given symbolic type.
    fn symtype_max_abs(st: &SymType) -> Option<i128> {
        match st {
            SymType::Bool => Some(1),
            SymType::Uint(w) => {
                if *w >= 63 {
                    return None;
                }
                Some((1_i128 << w) - 1)
            }
            SymType::Int(w) => {
                if *w == 0 || *w >= 62 {
                    return None;
                }
                Some(1_i128 << (w - 1))
            }
            SymType::F => Some(FIELD_MODULUS - 1),
        }
    }

    /// Returns true if lhs * rhs cannot overflow the field range [0, p).
    fn product_safe_without_mod(lhs: &SymType, rhs: &SymType) -> bool {
        let max_l = match Self::symtype_max_abs(lhs) {
            Some(v) if v >= 0 => v,
            _ => return false,
        };
        let max_r = match Self::symtype_max_abs(rhs) {
            Some(v) if v >= 0 => v,
            _ => return false,
        };

        if max_l == 0 || max_r == 0 {
            return true;
        }

        match max_l.checked_mul(max_r) {
            Some(prod) => prod < FIELD_MODULUS,
            None => false,
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
            LvTail::MapIndex(k1, k2) => {
                e = Expr::MapIndex {
                    base: Box::new(e),
                    keys: vec![k1.clone(), k2.clone()],
                };
            }
        }
    }
    e
}

/// Evaluate call arguments sequentially and return values with the final state.
fn eval_call_args(mut state: SymState, args: Vec<Expr>) -> (Vec<SymExpr>, SymState) {
    let mut vals = Vec::with_capacity(args.len());
    for arg in args {
        let (v, s1) = expect_single(arg.eval(state), "call argument");
        vals.push(v);
        state = s1;
    }
    (vals, state)
}

/// Evaluate a map access projection `map[clk, addr].{clk_prev|value}` while caching the pair.
fn eval_map_index_projection(
    mut state: SymState,
    base: &Expr,
    clk_expr: Expr,
    addr_expr: Expr,
    _field: &str,
) -> (SymExpr, SymExpr, SymState) {
    // Resolve the map base for id/type and apply any side effects.
    let base_id = match base {
        Expr::Path { ref_id, .. } => *ref_id,
        _ => None,
    };
    let base_repr = format!("{:?}", base);
    let (_map_val, s_after_base) = expect_single(base.clone().eval(state), "map base");
    state = s_after_base;

    // Determine the map element types.
    let (ts_ty, val_ty) = match base {
        Expr::Path {
            ref_id: Some(vid), ..
        } => match state.ctx.query_type(*vid) {
            Some(Type::Map {
                timestamp, value, ..
            }) => ((**timestamp).clone(), (**value).clone()),
            other => panic!("map access on non-map type: {:?}", other),
        },
        _ => panic!("map access requires a named map variable"),
    };
    let (ret_ts_ty, ret_val_ty) = state
        .ctx
        .map_return_pair_types(&ts_ty, &val_ty);

    // Evaluate keys.
    let (clk, s1) = expect_single(clk_expr.eval(state), "map key clk");
    let (addr, mut s2) = expect_single(addr_expr.eval(s1), "map key addr");

    // Reuse cached pair if present.
    if let Some((prev, val)) = s2.find_map_read(base_id, &base_repr, &clk, &addr) {
        return (prev, val, s2);
    }

    // Fresh symbols for the returned pair.
    let ts_sym = s2
        .type_map(&ret_ts_ty)
        .unwrap_or_else(|e| panic!("map timestamp type mapping failed: {e}"));
    let val_sym_ty = s2
        .type_map(&ret_val_ty)
        .unwrap_or_else(|e| panic!("map value type mapping failed: {e}"));

    let clk_prev = s2.fresh_sym("map_clk_prev", ts_sym);
    let val = s2.fresh_sym("map_val", val_sym_ty);

    // Record memory events and cache.
    s2 = s2.add_memory_event(
        MemoryEventKind::Send,
        clk_prev.clone(),
        addr.clone(),
        val.clone(),
    );
    s2 = s2.add_memory_event(
        MemoryEventKind::Receive,
        clk.clone(),
        addr.clone(),
        val.clone(),
    );
    s2 = s2.record_map_read(base_id, base_repr, clk, addr, clk_prev.clone(), val.clone());

    (clk_prev, val, s2)
}

/// Try to evaluate a builtin call (scalar method or free function).
/// Arguments are evaluated as scalars only when the callee is recognized as builtin.
fn try_eval_builtin_call(
    state: SymState,
    callee_expr: &Expr,
    args: Vec<Expr>,
) -> Option<Vector<(SymExpr, SymState)>> {
    // Builtin scalar methods, e.g. `a.inverse()`.
    if let Expr::Field { base, name, .. } = callee_expr {
        if let Some(base_ty) = state.infer_expr_type(base.as_ref()) {
            if let Ok(PathKind::Builtin) = state.ctx.classify_type(&base_ty) {
                let (arg_vals, s_after_args) = eval_call_args(state, args);
                return Some(eval_builtin_method_call(
                    s_after_args,
                    *base.clone(),
                    &base_ty,
                    name.as_str(),
                    arg_vals,
                ));
            }
        }
    }

    // Free builtin functions, e.g. `to_field(x)`, `to_u32(x)`, `to_word(x)`.
    if let Expr::Path { segments, .. } = callee_expr {
        if let Some(last) = segments.last() {
            match last.as_str() {
                "to_field" | "to_u32" | "to_word" | "and" | "extract_bit_u32" | "from_u32" => {
                    let (arg_vals, s_after_args) = eval_call_args(state, args.clone());
                    return Some(eval_builtin_free_fn_call(
                        s_after_args,
                        last.as_str(),
                        args,
                        arg_vals,
                    ));
                }
                _ => {}
            }
        }
    }

    None
}

/// Evaluate a regular function or struct method call (non-builtin).
/// The return value is optional to support both void-returning and value-returning callees.
fn eval_regular_call(
    state: SymState,
    callee_expr: Expr,
    args: Vec<Expr>,
) -> Vector<(Option<SymExpr>, SymState)> {
    let (fid, receiver_place) = resolve_callee_expr(&state, &callee_expr);

    let func = state
        .ctx
        .func_def(fid)
        .cloned()
        .unwrap_or_else(|| panic!("missing function body for id {}", fid));

    let mut callee_state = state.clone();
    callee_state.status = ExecStatus::Step;

    // We bind arguments according to the static function signature.
    let mut arg_iter = args.into_iter();
    let mut self_binding: Option<(ReceiverPlace, i64)> = None;

    for p in &func.params {
        match p {
            Param::SelfParam { id } => {
                let callee_vid = id.expect("self parameter id must be assigned during resolve");

                let place = receiver_place
                    .clone()
                    .unwrap_or_else(|| panic!("self parameter without receiver"));

                let recv_node = load_receiver_node(&callee_state.store, &place);

                callee_state.store = callee_state.store.clone().set(callee_vid, recv_node);
                self_binding = Some((place, callee_vid));
            }

            Param::Typed { id, ty, .. } => {
                let callee_vid = id.expect("parameter id must be assigned during resolve");
                let arg_expr = arg_iter
                    .next()
                    .unwrap_or_else(|| panic!("insufficient arguments in call"));

                // Scalar parameters keep the old `SymExpr`-based semantics.
                if ty.is_scalar(&callee_state.ctx) {
                    let (v, s1) =
                        expect_single(arg_expr.eval(callee_state), "scalar argument in call");
                    callee_state = s1;
                    callee_state.store = callee_state
                        .store
                        .clone()
                        .set(callee_vid, StoreNode::Scalar(v));
                } else {
                    // Aggregate parameters (structs, arrays, etc.) are passed by copying
                    // the corresponding store node for the argument place.
                    let node = callee_state.query_expr_node(&arg_expr).unwrap_or_else(|| {
                        panic!(
                            "aggregate argument `{:?}` not found as a materialized place",
                            arg_expr
                        )
                    });
                    callee_state.store = callee_state.store.clone().set(callee_vid, node.clone());
                }
            }
        }
    }

    if arg_iter.next().is_some() {
        panic!("too many arguments supplied to call");
    }

    let results = func.clone().execute(callee_state);
    if results.is_empty() {
        panic!("call produced no successor states");
    }

    let mut out: Vector<(Option<SymExpr>, SymState)> = Vector::new();

    for (ret_opt, mut s_end) in results {
        // If we bound `self` via a receiver place, write back any updates.
        if let Some((place, callee_vid)) = self_binding.clone() {
            let node = s_end.store.get(callee_vid).cloned().unwrap_or_else(|| {
                panic!(
                    "callee `self` binding id {} not found in final store",
                    callee_vid
                )
            });
            s_end.store = store_receiver_node(s_end.store.clone(), &place, node);
        }

        s_end.status = ExecStatus::Step;
        out.push_back((ret_opt, s_end));
    }

    out
}

/// Resolves a callee expression in either statement or expression position.
///
/// Returns the function identifier and, for method calls, the logical
/// location of the receiver inside the store.
fn resolve_callee_expr(state: &SymState, callee: &Expr) -> (i64, Option<ReceiverPlace>) {
    match callee {
        // Free function: f(...)
        Expr::Path { ref_id, segments } => {
            // If already resolved to a function id, use it.
            if let Some(fid) = ref_id {
                if state.ctx.fn_sig(*fid).is_some() {
                    return (*fid, None);
                }
            }

            // Associated method: TypeName::method(...)
            if segments.len() >= 2 {
                let type_name = &segments[segments.len() - 2];
                let method_name = &segments[segments.len() - 1];

                if let Some(struct_id) = state.ctx.struct_id_by_name(type_name) {
                    let members = state.ctx.struct_members(struct_id).unwrap_or_else(|| {
                        panic!(
                            "missing member table for struct `{}` (id = {})",
                            type_name, struct_id
                        )
                    });

                    let mi = members.get(method_name).unwrap_or_else(|| {
                        panic!(
                            "unknown associated method `{}` on struct `{}`",
                            method_name, type_name
                        )
                    });

                    let fid = mi.as_func_id().unwrap_or_else(|| {
                        panic!(
                            "member `{}` on struct `{}` is not a method",
                            method_name, type_name
                        )
                    });

                    return (fid, None);
                }
            }

            panic!(
                "unsupported callee Path for call resolution: segments = {:?}, ref_id = {:?}",
                segments, ref_id
            );
        }

        // Either TypeName::method(...) or place.method(...)
        Expr::Field { base, name, ref_id } => {
            // Associated method: TypeName::method(...)
            if let Expr::Path {
                segments,
                ref_id: Some(sid),
            } = base.as_ref()
            {
                if let Some(last) = segments.last() {
                    if let Some(struct_id) = state.ctx.struct_id_by_name(last) {
                        if struct_id == *sid {
                            // Prefer an already resolved function id.
                            if let Some(fid) = ref_id {
                                if state.ctx.fn_sig(*fid).is_some() {
                                    return (*fid, None);
                                }
                            }

                            let members =
                                state.ctx.struct_members(struct_id).unwrap_or_else(|| {
                                    panic!(
                                        "missing member table for struct `{}` (id = {})",
                                        last, struct_id
                                    )
                                });

                            let mi = members.get(name).unwrap_or_else(|| {
                                panic!("unknown associated method `{}` on struct `{}`", name, last)
                            });

                            let fid = mi.as_func_id().unwrap_or_else(|| {
                                panic!("member `{}` on struct `{}` is not a method", name, last)
                            });

                            return (fid, None);
                        }
                    }
                }
            }

            // Instance method: place.method(...)
            let base_ty = state
                .infer_expr_type(base.as_ref())
                .unwrap_or_else(|| panic!("cannot infer type for method receiver in call"));

            let struct_id = match state.ctx.classify_type(&base_ty) {
                Ok(PathKind::Struct(sid)) => sid,
                Ok(PathKind::Builtin) => {
                    panic!(
                        "method receiver must be a struct, got builtin type `{:?}`",
                        base_ty
                    )
                }
                Err(e) => {
                    panic!(
                        "invalid method receiver type `{:?}` in call: {}",
                        base_ty, e
                    )
                }
            };

            let receiver_place = build_receiver_place(state, base.as_ref());

            // Use pre-resolved function id if available.
            if let Some(fid) = ref_id {
                if state.ctx.fn_sig(*fid).is_some() {
                    return (*fid, Some(receiver_place));
                }
            }

            // Fallback to member lookup by name.
            let members = state.ctx.struct_members(struct_id).unwrap_or_else(|| {
                panic!(
                    "missing member table for struct_id {} when resolving method `{}`",
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

            (fid, Some(receiver_place))
        }

        _ => {
            panic!("unsupported callee form for call resolution: {:?}", callee);
        }
    }
}

/// Decompose a place-like expression (path / field / index chain)
/// into a root binding id and a sequence of concrete steps.
fn build_receiver_place(state: &SymState, e: &Expr) -> ReceiverPlace {
    fn go(state: &SymState, e: &Expr) -> (i64, Vec<ReceiverStep>) {
        match e {
            // Base case: plain variable path.
            Expr::Path {
                ref_id: Some(vid), ..
            } => (*vid, Vec::new()),

            // Field selection: base.field
            Expr::Field { base, name, .. } => {
                let (root, mut steps) = go(state, base.as_ref());

                // Static type of the base struct.
                let base_ty = state.infer_expr_type(base.as_ref()).unwrap_or_else(|| {
                    panic!(
                        "failed to infer type for field base in receiver: {:?}",
                        base
                    )
                });

                let sid = match state.ctx.classify_type(&base_ty) {
                    Ok(PathKind::Struct(sid)) => sid,
                    Ok(PathKind::Builtin) => {
                        panic!(
                            "field receiver in method call must be a struct, got builtin `{:?}`",
                            base_ty
                        )
                    }
                    Err(e) => {
                        panic!(
                            "invalid type for field receiver in method call `{:?}`: {}",
                            base_ty, e
                        )
                    }
                };

                let fid = state.ctx.field_id_of(sid, name).unwrap_or_else(|| {
                    panic!(
                        "unknown field `{}` on struct_id {} in method receiver",
                        name, sid
                    )
                });

                steps.push(ReceiverStep::Field(fid));
                (root, steps)
            }

            // Index selection: base[idx]
            Expr::Index(base, idx) => {
                let (root, mut steps) = go(state, base.as_ref());
                let idx_val = eval_index_const_or_err(&state.ctx, Some(&state.store), idx)
                    .unwrap_or_else(|| {
                        panic!(
                            "array index in method receiver must be a concrete integer: `{:?}`",
                            idx
                        )
                    });
                steps.push(ReceiverStep::Index(idx_val));
                (root, steps)
            }

            _ => {
                panic!(
                    "method receiver must be a place expression (path/field/index chain), got `{:?}`",
                    e
                );
            }
        }
    }

    let (root_vid, steps) = go(state, e);
    ReceiverPlace { root_vid, steps }
}

/// Load the store node at the receiver place.
fn load_receiver_node(store: &Store, place: &ReceiverPlace) -> StoreNode {
    let mut node = store.get(place.root_vid).cloned().unwrap_or_else(|| {
        panic!(
            "receiver root variable id {} not found in store",
            place.root_vid
        )
    });

    for step in &place.steps {
        match (step, &node) {
            (ReceiverStep::Field(fid), StoreNode::Struct { fields }) => {
                let child = fields.get(fid).unwrap_or_else(|| {
                    panic!(
                        "receiver struct missing field id {} while loading receiver",
                        fid
                    )
                });
                node = child.clone();
            }
            (ReceiverStep::Index(i), StoreNode::Array { len, elems }) => {
                if let Some(l) = len {
                    if *i >= *l {
                        panic!(
                            "receiver array index {} out of bounds (len = {}) while loading",
                            i, l
                        );
                    }
                }
                let child = elems.get(i).unwrap_or_else(|| {
                    panic!(
                        "receiver array element {} uninitialized while loading receiver",
                        i
                    )
                });
                node = child.clone();
            }
            (step, bad) => {
                panic!(
                    "receiver place shape mismatch while loading: step {:?} on node {:?}",
                    step, bad
                );
            }
        }
    }

    node
}

/// Write back an updated node to the receiver place.
fn store_receiver_node(store: Store, place: &ReceiverPlace, new_node: StoreNode) -> Store {
    fn write_rec(cur: StoreNode, steps: &[ReceiverStep], leaf: &StoreNode) -> StoreNode {
        if steps.is_empty() {
            return leaf.clone();
        }

        match (&steps[0], cur) {
            (ReceiverStep::Field(fid), StoreNode::Struct { fields }) => {
                let child = fields.get(fid).cloned().unwrap_or_else(|| {
                    panic!(
                        "receiver struct missing field id {} while writing back",
                        fid
                    )
                });
                let updated_child = write_rec(child, &steps[1..], leaf);
                let new_fields = fields.update(*fid, updated_child);
                StoreNode::Struct { fields: new_fields }
            }

            (ReceiverStep::Index(i), StoreNode::Array { len, elems }) => {
                let child = elems.get(i).cloned().unwrap_or_else(|| {
                    panic!(
                        "receiver array element {} uninitialized while writing back",
                        i
                    )
                });
                let updated_child = write_rec(child, &steps[1..], leaf);
                let new_elems = elems.update(*i, updated_child);
                StoreNode::Array {
                    len,
                    elems: new_elems,
                }
            }

            (step, bad) => {
                panic!(
                    "receiver place shape mismatch while writing back: step {:?} on node {:?}",
                    step, bad
                );
            }
        }
    }

    let root = store.get(place.root_vid).cloned().unwrap_or_else(|| {
        panic!(
            "receiver root variable id {} not found when writing back",
            place.root_vid
        )
    });

    let updated_root = write_rec(root, &place.steps, &new_node);
    store.set(place.root_vid, updated_root)
}

fn eval_builtin_free_fn_call(
    mut state: SymState,
    name: &str,
    mut orig_args: Vec<Expr>,
    mut arg_vals: Vec<SymExpr>,
) -> Vector<(SymExpr, SymState)> {
    match name {
        "to_field" => {
            if arg_vals.len() != 1 {
                panic!("`to_field` expects exactly one argument");
            }
            let src = arg_vals.remove(0);

            let res = state.fresh_sym("to_field", SymType::F);
            let eq = res.clone().eq_to(src);
            state = state.with_pc(eq);

            Vector::unit((res, state))
        }

        "to_u32" => {
            if arg_vals.len() != 1 || orig_args.len() != 1 {
                panic!("`to_u32` expects exactly one argument");
            }

            let src_expr = orig_args.remove(0);
            let src_val = arg_vals.remove(0);

            let src_ty_opt = state.infer_expr_type(&src_expr);

            match state.ctx.config.solver.kind {
                SolverKind::Cvc5Ff => {
                    // Only allow u8 / bool / field here.
                    let allowed = if let Some(src_ty) = src_ty_opt.clone() {
                        match state.type_map(&src_ty) {
                            Ok(SymType::Uint(8)) | Ok(SymType::Bool) | Ok(SymType::F) => true,
                            _ => false,
                        }
                    } else {
                        false
                    };

                    if !allowed {
                        panic!(
                            "`to_u32` under cvc5_ff is only allowed on u8/bool/field arguments; \
                             got static type {:?} for expression `{:?}` (possible field-domain issue)",
                            src_ty_opt, src_expr
                        );
                    }

                    // Transparent cast: keep the original value.
                    return Vector::unit((src_val, state));
                }

                // For non-cvc5_ff backends, keep the old encoding.
                _ => {
                    let res = state.fresh_sym("to_u32", SymType::Uint(32));
                    let eq = res.clone().eq_to(src_val);
                    state = state.with_pc(eq);
                    return Vector::unit((res, state));
                }
            }
        }

        "and" => {
            if arg_vals.len() != 2 {
                panic!("`and` expects exactly two arguments");
            }
            let lhs = arg_vals.remove(0);
            let rhs = arg_vals.remove(0);
            let res = state.fresh_sym("and", SymType::Uint(8));
            let state = constrain_byte_and(state, res.clone(), lhs, rhs);
            Vector::unit((res, state))
        }

        "extract_bit_u32" => {
            if arg_vals.len() != 2 || orig_args.len() != 2 {
                panic!("`extract_bit_u32` expects exactly two arguments");
            }
            let _value_expr = orig_args.remove(0);
            let idx_expr = orig_args.remove(0);
            let value = arg_vals.remove(0);
            let idx_val = arg_vals.remove(0);

            let idx_const = match idx_val {
                SymExpr::Int(k) => k,
                other => panic!(
                    "`extract_bit_u32` index must be a concrete integer literal, got {:?}",
                    other
                ),
            };
            if idx_const < 0 || idx_const >= 32 {
                panic!(
                    "`extract_bit_u32` index must be in [0,32), got {} for expr {:?}",
                    idx_const, idx_expr
                );
            }

            let (bits, state) = decompose_u32_bits(state, value, "extract_bit");
            let bit = bits[idx_const as usize].clone();

            Vector::unit((bit, state))
        }

        "from_u32" => {
            if arg_vals.len() != 1 {
                panic!("`from_u32` expects exactly one argument");
            }
            let src = arg_vals.remove(0);
            let res = state.fresh_sym("from_u32", SymType::F);
            let state = state.with_pc(res.clone().eq_to(src));
            Vector::unit((res, state))
        }

        "to_word" => {
            if arg_vals.len() != 1 || orig_args.len() != 1 {
                panic!("`to_word` expects exactly one argument");
            }

            let src_expr = orig_args.remove(0);
            let src_val = arg_vals.remove(0);

            // Require a plain variable path as input.
            match src_expr {
                Expr::Path { .. } => {}
                other => {
                    panic!(
                        "`to_word` expects a variable path as argument, got expression `{:?}`",
                        other
                    );
                }
            }

            // Require the static type to be u32.
            let src_ty_opt = state.infer_expr_type(&src_expr);
            let sty = src_ty_opt
                .as_ref()
                .and_then(|t| state.type_map(t).ok())
                .unwrap_or_else(|| {
                    panic!(
                        "`to_word` failed to infer symbolic sort for expression `{:?}`",
                        src_expr
                    )
                });

            match sty {
                SymType::Uint(32) => {}
                other => {
                    panic!(
                        "`to_word` expects a u32-typed argument, got symbolic sort {:?} for expression `{:?}`",
                        other, src_expr
                    );
                }
            }

            // Model [u8; 4] as four fresh Uint(8) bytes in range [0, 255].
            let mut word = Vec::with_capacity(4);
            for i in 0..4 {
                let b = state.fresh_sym(&format!("to_word_b{}", i), SymType::Uint(8));
                let zero = SymExpr::Int(0);
                let max = SymExpr::Int(255);

                // 0 <= b <= 255
                let ge_zero = b.clone().ge(zero);
                let le_max = b.clone().le(max);
                state = state.with_pc(ge_zero);
                state = state.with_pc(le_max);

                word.push(b);
            }

            // Link the 4 bytes back to the original u32 using little-endian encoding:
            // src == b0 + 256 * (b1 + 256 * (b2 + 256 * b3))
            let two_fifty_six = SymExpr::Int(256);
            let acc3 = word[3].clone();
            let acc2 = word[2].clone() + two_fifty_six.clone() * acc3;
            let acc1 = word[1].clone() + two_fifty_six.clone() * acc2;
            let acc0 = word[0].clone() + two_fifty_six * acc1;
            let eq = acc0.eq_to(src_val.clone());
            state = state.with_pc(eq);

            // The byte array is represented implicitly by the four byte variables
            // and the above constraints. We keep the scalar return as the original u32.
            Vector::unit((src_val, state))
        }

        other => {
            panic!("unsupported builtin free function `{}`", other);
        }
    }
}

/// Evaluate a builtin scalar method like `field.inverse()`.
fn eval_builtin_method_call(
    state: SymState,
    base_expr: Expr,
    base_ty: &Type,
    method_name: &str,
    arg_vals: Vec<SymExpr>,
) -> Vector<(SymExpr, SymState)> {
    let (recv, mut s1) = expect_single(
        base_expr.eval(state),
        &format!("builtin method receiver `{}`", method_name),
    );

    if !arg_vals.is_empty() {
        panic!(
            "builtin method `{}` on type `{:?}` does not accept arguments",
            method_name, base_ty
        );
    }

    let sty = s1
        .type_map(base_ty)
        .unwrap_or_else(|e| panic!("builtin method type mapping failed: {e}"));

    match (sty, method_name) {
        // field.inverse() : field
        (SymType::F, "inverse") => {
            // Fresh field-typed variable for the inverse.
            let inv = s1.fresh_sym("inverse", SymType::F);

            let zero = SymExpr::Int(0);
            let one = SymExpr::Int(1);

            // (a == 0)
            let recv_eq_zero = recv.clone().eq_to(zero);

            // ((a * inv) mod p == 1)  -- true field inverse relation
            let recv_times_inv = (recv.clone() * inv.clone()).mod_field();
            let recv_times_inv_eq_one = recv_times_inv.eq_to(one);

            let guard = BoolExpr::or(vec![recv_eq_zero, recv_times_inv_eq_one]);
            s1 = s1.with_pc(guard);

            Vector::unit((inv, s1))
        }

        (sty, name) => {
            panic!(
                "unsupported builtin method `{}` for scalar sort `{:?}`",
                name, sty
            );
        }
    }
}
