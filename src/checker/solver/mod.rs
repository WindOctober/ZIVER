use crate::checker::symbolic::expr::{BoolExpr, FIELD_MODULUS};
use crate::utils::{SetConfig, SolverKind};

pub mod cvc5;
pub mod z3;

pub use cvc5::Cvc5ffBackend;
pub use z3::Z3NiaBackend;

/// Selects the SMT backend for solving.
#[derive(Clone, Debug)]
pub enum SmtBackend {
    Z3Nia,
    Cvc5Ff { cmd: String, relaxed: bool },
}

/// Select an SMT backend from user configuration.
pub fn backend_from_config(config: &SetConfig) -> SmtBackend {
    match config.solver.kind {
        SolverKind::Z3Nia => SmtBackend::Z3Nia,
        SolverKind::Cvc5Ff => SmtBackend::Cvc5Ff {
            cmd: config.solver.cvc5_cmd.clone(),
            relaxed: config.ff_relax,
        },
    }
}

/// Dispatch a single formula to the chosen backend.
pub fn check_with_solver(phi: &BoolExpr, backend: SmtBackend) -> Result<bool, String> {
    match backend {
        SmtBackend::Z3Nia => {
            let backend = Z3NiaBackend::new();
            backend.check(phi)
        }
        SmtBackend::Cvc5Ff { cmd, relaxed } => {
            let backend = Cvc5ffBackend::new(FIELD_MODULUS, relaxed);
            backend.check(phi, &cmd)
        }
    }
}
