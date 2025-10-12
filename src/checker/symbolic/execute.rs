use im::Vector;

use crate::{
    ast::Member,
    checker::symbolic::{expr::SymExpr, state::SymbolicState},
};

pub trait SymbolicExecutor {
    fn execute(self) -> Vector<(SymExpr, SymbolicState)>;
}

impl SymbolicExecutor for Member {
    fn execute(self) -> Vector<(SymExpr, SymbolicState)> {
        todo!()
    }
}
