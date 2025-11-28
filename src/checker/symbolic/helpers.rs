use crate::checker::symbolic::expr::{BoolExpr, SymExpr, SymType};

impl SymExpr {
    /// Rewrite all variables with the given name to use a new symbolic sort.
    pub fn rewrite_var_sort(self, target: &str, new_ty: &SymType) -> SymExpr {
        match self {
            SymExpr::Var(name, _) if name == target => SymExpr::Var(name, new_ty.clone()),

            SymExpr::Neg(inner) => SymExpr::Neg(Box::new(inner.rewrite_var_sort(target, new_ty))),

            SymExpr::Add(xs) => SymExpr::Add(
                xs.into_iter()
                    .map(|e| e.rewrite_var_sort(target, new_ty))
                    .collect(),
            ),

            SymExpr::Mul(xs) => SymExpr::Mul(
                xs.into_iter()
                    .map(|e| e.rewrite_var_sort(target, new_ty))
                    .collect(),
            ),

            SymExpr::Sub(a, b) => SymExpr::Sub(
                Box::new(a.rewrite_var_sort(target, new_ty)),
                Box::new(b.rewrite_var_sort(target, new_ty)),
            ),

            SymExpr::Div(a, b) => SymExpr::Div(
                Box::new(a.rewrite_var_sort(target, new_ty)),
                Box::new(b.rewrite_var_sort(target, new_ty)),
            ),

            SymExpr::Mod(a, b) => SymExpr::Mod(
                Box::new(a.rewrite_var_sort(target, new_ty)),
                Box::new(b.rewrite_var_sort(target, new_ty)),
            ),

            SymExpr::Ite(cond, t, e2) => SymExpr::Ite(
                Box::new(cond.rewrite_var_sort(target, new_ty)),
                Box::new(t.rewrite_var_sort(target, new_ty)),
                Box::new(e2.rewrite_var_sort(target, new_ty)),
            ),

            other => other,
        }
    }
}

impl BoolExpr {
    /// Rewrite all occurrences of the given variable name inside this Boolean guard.
    pub fn rewrite_var_sort(self, target: &str, new_ty: &SymType) -> BoolExpr {
        match self {
            BoolExpr::Bool(v) => BoolExpr::Bool(v),

            BoolExpr::Not(inner) => BoolExpr::Not(Box::new(inner.rewrite_var_sort(target, new_ty))),

            BoolExpr::And(xs) => BoolExpr::And(
                xs.into_iter()
                    .map(|c| c.rewrite_var_sort(target, new_ty))
                    .collect(),
            ),

            BoolExpr::Or(xs) => BoolExpr::Or(
                xs.into_iter()
                    .map(|c| c.rewrite_var_sort(target, new_ty))
                    .collect(),
            ),

            BoolExpr::Eq(a, b) => BoolExpr::Eq(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),

            BoolExpr::Ne(a, b) => BoolExpr::Ne(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),

            BoolExpr::Le(a, b) => BoolExpr::Le(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),

            BoolExpr::Lt(a, b) => BoolExpr::Lt(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),

            BoolExpr::Ge(a, b) => BoolExpr::Ge(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),

            BoolExpr::Gt(a, b) => BoolExpr::Gt(
                a.rewrite_var_sort(target, new_ty),
                b.rewrite_var_sort(target, new_ty),
            ),
        }
    }
}
