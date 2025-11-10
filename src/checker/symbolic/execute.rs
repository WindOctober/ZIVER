use im::Vector;

use crate::{
    ast::{BinOp, Expr, Func, Member, Stmt},
    checker::symbolic::{
        expr::{BoolExpr, SymExpr},
        state::SymState,
    },
};

pub trait SymbolicExecutor {
    fn execute(self, state: SymState) -> Vector<(SymExpr, SymState)>;
}

impl SymbolicExecutor for Member {
    fn execute(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        match self {
            Member::Computation(f) | Member::Constraint(f) => f.execute(state),
        }
    }
}

impl SymbolicExecutor for Func {
    fn execute(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        // We maintain a frontier of live (non-terminated) states as we
        // scan statements. Any Return will emit a terminal branch.
        let mut live: Vector<SymState> = Vector::unit(state);
        let mut terminals: Vector<(SymExpr, SymState)> = Vector::new();

        for stmt in self.body {
            let mut next_live: Vector<SymState> = Vector::new();

            for st in live.into_iter() {
                match &stmt {
                    Stmt::AssertEq(a, b) => {
                        // Inline build of a Boolean constraint: (== a b).
                        let ae = (&*a).clone().execute(st.clone());
                        let be = (&*b).clone().execute(st.clone());
                        // The expression executor should yield exactly one arithmetic value
                        // in this minimal setting. If multiple, it means branching expressions,
                        // which we do not support yet.
                        if ae.len() != 1 || be.len() != 1 {
                            panic!("Expression branching is not supported in AssertEq.");
                        }
                        let (av, mut s1) = ae[0].clone();
                        let (bv, _s2) = be[0].clone();
                        // Accumulate the equality into the path condition.
                        s1 = s1.with_pc(av.eq_to(bv));
                        next_live.push_back(s1);
                    }

                    Stmt::AssertBool(e) => {
                        // Inline Boolean evaluation for the limited subset we support.
                        // Currently supports: Bool(true/false), Paren, Binary(Eq, …).
                        let cond = match e {
                            Expr::Bool(b) => BoolExpr::Bool(*b),
                            Expr::Paren(x) => {
                                // Evaluate recursively on the inner expression in-place.
                                match &**x {
                                    Expr::Bool(b) => BoolExpr::Bool(*b),
                                    Expr::Binary {
                                        op: BinOp::Eq,
                                        lhs,
                                        rhs,
                                    } => {
                                        let l = (&**lhs).clone().execute(st.clone());
                                        let r = (&**rhs).clone().execute(st.clone());
                                        if l.len() != 1 || r.len() != 1 {
                                            panic!(
                                                "Expression branching is not supported in AssertBool(Eq)."
                                            );
                                        }
                                        let (lv, _) = l[0].clone();
                                        let (rv, _) = r[0].clone();
                                        lv.eq_to(rv)
                                    }
                                    _ => panic!("Unsupported Boolean form inside Paren."),
                                }
                            }
                            Expr::Binary {
                                op: BinOp::Eq,
                                lhs,
                                rhs,
                            } => {
                                let l = (&**lhs).clone().execute(st.clone());
                                let r = (&**rhs).clone().execute(st.clone());
                                if l.len() != 1 || r.len() != 1 {
                                    panic!(
                                        "Expression branching is not supported in AssertBool(Eq)."
                                    );
                                }
                                let (lv, _) = l[0].clone();
                                let (rv, _) = r[0].clone();
                                lv.eq_to(rv)
                            }
                            _ => panic!("Unsupported Boolean expression in AssertBool."),
                        };
                        let mut s2 = st.clone();
                        s2 = s2.with_pc(cond);
                        next_live.push_back(s2);
                    }

                    Stmt::Return(e) => {
                        // Evaluate the return expression arithmetically and emit branches.
                        let vals = e.clone().execute(st);
                        if vals.is_empty() {
                            panic!("Return expression produced no value.");
                        }
                        for (v, sret) in vals {
                            terminals.push_back((v, sret));
                        }
                    }

                    // Placeholders: These demand an environment/memory model to map
                    // lvalues to addresses (var_id, offset) and to implement store effects.
                    Stmt::VarDecl { .. } => {
                        unimplemented!(
                            "VarDecl requires a variable environment and allocation semantics."
                        );
                    }
                    Stmt::Assign { .. } => {
                        unimplemented!(
                            "Assign requires an lvalue-to-address mapping and store updates."
                        );
                    }
                    Stmt::AndAssign { .. } => {
                        unimplemented!(
                            "AndAssign requires an lvalue-to-address mapping and logical semantics."
                        );
                    }
                    Stmt::For { .. } => {
                        unimplemented!(
                            "For requires a path-splitting strategy or an invariant-guided summarization."
                        );
                    }
                    Stmt::Call { .. } => {
                        unimplemented!(
                            "Top-level Call statements require call semantics and possibly side effects."
                        );
                    }
                }
            }

            // If this statement did not terminate all live states, continue.
            live = next_live;
            if live.is_empty() {
                // All paths have terminated (e.g., via Return).
                break;
            }
        }

        terminals
    }
}

impl SymbolicExecutor for Stmt {
    fn execute(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        // For statements, we define the following minimal contract:
        // - Non-terminating statements yield an empty set (they only update the state).
        // - A Return yields one or more terminal branches.
        match self {
            Stmt::Return(e) => e.execute(state),
            Stmt::AssertEq(_, _)
            | Stmt::AssertBool(_)
            | Stmt::VarDecl { .. }
            | Stmt::Assign { .. }
            | Stmt::AndAssign { .. }
            | Stmt::For { .. }
            | Stmt::Call { .. } => Vector::new(),
        }
    }
}

impl SymbolicExecutor for Expr {
    fn execute(self, state: SymState) -> Vector<(SymExpr, SymState)> {
        // Expressions return arithmetic SymExprs under the given state.
        // Boolean expressions are not returned here; they are handled inline
        // by statements that require Boolean guards (e.g., AssertBool/branching).
        match self {
            Expr::Int(k) => {
                let mut out = Vector::new();
                out.push_back((SymExpr::Int(k as i128), state));
                out
            }
            Expr::Path { segments, .. } => {
                // Minimal name-to-symbol mapping: treat a path as a symbolic variable.
                // If you need an environment with SSA or address-based loads, plug it here.
                let name = segments.join("::");
                let mut out = Vector::new();
                out.push_back((SymExpr::Var(name), state));
                out
            }
            Expr::Paren(e) => e.execute(state),

            Expr::Binary {
                op: BinOp::Add,
                lhs,
                rhs,
            } => {
                let l = (*lhs).execute(state.clone());
                let r = (*rhs).execute(state);
                if l.len() != 1 || r.len() != 1 {
                    panic!("Expression branching is not supported for arithmetic Binary(Add).");
                }
                let (lv, s1) = l[0].clone();
                let (rv, _s2) = r[0].clone();
                let mut out = Vector::new();
                out.push_back((lv + rv, s1));
                out
            }
            Expr::Binary {
                op: BinOp::Sub,
                lhs,
                rhs,
            } => {
                let l = (*lhs).execute(state.clone());
                let r = (*rhs).execute(state);
                if l.len() != 1 || r.len() != 1 {
                    panic!("Expression branching is not supported for arithmetic Binary(Sub).");
                }
                let (lv, s1) = l[0].clone();
                let (rv, _s2) = r[0].clone();
                let mut out = Vector::new();
                out.push_back((lv - rv, s1));
                out
            }
            Expr::Binary {
                op: BinOp::Mul,
                lhs,
                rhs,
            } => {
                let l = (*lhs).execute(state.clone());
                let r = (*rhs).execute(state);
                if l.len() != 1 || r.len() != 1 {
                    panic!("Expression branching is not supported for arithmetic Binary(Mul).");
                }
                let (lv, s1) = l[0].clone();
                let (rv, _s2) = r[0].clone();
                let mut out = Vector::new();
                out.push_back((lv * rv, s1));
                out
            }

            // Boolean and side-effectful forms are intentionally excluded here.
            Expr::Bool(_) | Expr::Binary { op: BinOp::Eq, .. } => {
                panic!(
                    "Boolean-valued expressions are not returned as SymExpr; they must be consumed by statements expecting Boolean guards (e.g., AssertBool)."
                );
            }
            Expr::Binary {
                op: BinOp::BitAnd, ..
            } => {
                unimplemented!(
                    "BitAnd requires a precise semantics choice (bitwise vs. logical) before mapping to SymExpr."
                );
            }
            Expr::Call(_, _) | Expr::Index(_, _) | Expr::Field { .. } => {
                unimplemented!(
                    "Call/Index/Field require an environment and memory model to interpret."
                );
            }
        }
    }
}
