use crate::{
    ast::Expr,
    checker::symbolic::{context::Context, expr::SymExpr, state::Store},
};

pub mod context;
pub mod execute;
pub mod expr;
pub(crate) mod state;

/// Evaluate an expression as a concrete array index `usize` if possible.
/// Accepted forms are:
///   * integer literal, e.g., `42`
///   * parenthesized literal, e.g., `(42)`
///   * a path that resolves either
///       - to a compile-time constant whose definition is a literal integer, or
///       - to a scalar store cell holding a concrete `SymExpr::Int`.
pub fn eval_index_const_or_err(ctx: &Context, store: Option<&Store>, e: &Expr) -> Option<usize> {
    match e {
        // Pure literal.
        Expr::Int(k) if *k <= usize::MAX as u64 => Some(*k as usize),

        // Parenthesized expression: recurse structurally.
        Expr::Paren(inner) => eval_index_const_or_err(ctx, store, inner),

        // Identifier or path: first consult the runtime store (if any),
        // then fall back to compile-time consts.
        Expr::Path { ref_id, segments } => {
            // 1) Runtime resolution via store.
            if let Some(st) = store {
                if let Some(node) = st.query_scalar(&Expr::Path {
                    ref_id: *ref_id,
                    segments: segments.clone(),
                }) {
                    if let SymExpr::Int(k) = node {
                        if k >= 0 && (k as u128) <= (usize::MAX as u128) {
                            return Some(k as usize);
                        }
                    }
                }
            }

            // 2) Compile-time const resolution via `Context.const_int`.
            if let Some(cid) = *ref_id {
                if let Some(k) = ctx.const_int(cid) {
                    if k <= usize::MAX as u64 {
                        return Some(k as usize);
                    }
                }
            }
            None
        }

        // Unsupported index expression form.
        _ => None,
    }
}
