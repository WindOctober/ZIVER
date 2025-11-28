use crate::Args;
pub mod module_resolver;

#[derive(Clone, Debug, Default)]
pub struct SetConfig {
    pub type_refine: bool,
    pub solver: SolverConfig,
}

#[derive(Clone, Debug, Default)]
pub struct SolverConfig {
    pub kind: SolverKind,
    pub cvc5_cmd: String,
}

#[derive(Clone, Debug)]
pub enum SolverKind {
    Z3Nia,
    Cvc5Ff,
}

impl Default for SolverKind {
    fn default() -> Self {
        // Match CLI default: use cvc5_ff when no solver is specified.
        SolverKind::Cvc5Ff
    }
}

/// Build runtime configuration from CLI flags.
pub fn derive_config(args: Args) -> SetConfig {
    let solver_kind = match args.solver.as_str() {
        "z3" | "z3_nia" => SolverKind::Z3Nia,
        "cvc5" | "cvc5_ff" => SolverKind::Cvc5Ff,
        other => {
            eprintln!(
                "unknown solver `{}` (supported: z3_nia, cvc5_ff); falling back to z3_nia",
                other
            );
            SolverKind::Z3Nia
        }
    };

    SetConfig {
        type_refine: args.type_opt,
        solver: SolverConfig {
            kind: solver_kind,
            cvc5_cmd: args.cvc5_cmd,
        },
    }
}
