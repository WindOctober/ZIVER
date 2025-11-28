use crate::checker::symbolic::expr::{BoolExpr, FIELD_MODULUS};

pub mod cvc5;
pub mod z3;

pub use cvc5::Cvc5ffBackend;
pub use z3::Z3NiaBackend;

/// Selects the SMT backend for solving.
#[derive(Clone, Debug)]
pub enum SmtBackend {
    Z3Nia,
    Cvc5Ff { cmd: String },
}

/// Dispatch a single formula to the chosen backend.
pub fn check_with_solver(phi: &BoolExpr, backend: SmtBackend) -> Result<bool, String> {
    match backend {
        SmtBackend::Z3Nia => {
            let backend = Z3NiaBackend::new();
            backend.check(phi)
        }
        SmtBackend::Cvc5Ff { cmd } => {
            let backend = Cvc5ffBackend::new(FIELD_MODULUS);
            backend.check(phi, &cmd)
        }
    }
}
