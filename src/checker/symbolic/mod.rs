use crate::ast::Expr;

pub mod context;
pub mod execute;
pub mod expr;
pub(crate) mod state;

/// Evaluate an expression as a concrete array index `usize` if possible.
fn eval_index_const_or_err(e: &Expr) -> Option<usize> {
    match e {
        Expr::Int(k) if *k <= usize::MAX as u64 => Some(*k as usize),
        Expr::Paren(inner) => eval_index_const_or_err(inner),
        _ => None,
    }
}

/// Evaluate an expression as a concrete array length `usize` if possible.
fn eval_len_const_or_err(e: &Expr) -> Option<usize> {
    eval_index_const_or_err(e)
}
