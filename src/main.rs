pub mod ast;
mod checker;
pub mod parser;
mod utils;
use clap::{ArgAction, Parser};
use std::path::PathBuf;
use std::rc::Rc;

use crate::checker::check_equivalence;
use crate::checker::symbolic::context::init_context;
use crate::utils::derive_config;
use crate::utils::module_resolver::resolve_and_parse_modules;

/// Command-line interface for the CZ parser.
#[derive(Parser, Debug, Clone)]
#[command(
    name = "czc",
    version,
    about = "Parse a CZ DSL file and run equivalence checking."
)]
pub struct Args {
    /// Path to the input `.cz` file. Defaults to a benchmark file if omitted.
    #[arg(value_name = "PATH")]
    pub input: Option<PathBuf>,

    /// Print the parsed AST to stdout in a pretty format.
    #[arg(long, action = ArgAction::SetTrue)]
    pub ast: bool,

    /// Enables the optimization of type-based modular arithmetic simplification (enabled by default).
    /// Use `--no-type-opt` to disable this optimization.
    #[arg(
        long = "no-type-opt",
        alias = "disable-type-opt",
        action = ArgAction::SetFalse,
        default_value_t = true
    )]
    pub type_opt: bool,

    /// Select SMT solver backend: "z3_nia" or "cvc5_ff".
    #[arg(long, value_name = "SOLVER", default_value = "cvc5_ff")]
    pub solver: String,

    /// Command or path used to invoke cvc5 when `--solver cvc5_ff` is selected.
    #[arg(long, value_name = "CMD", default_value = "cvc5")]
    pub cvc5_cmd: String,
}

fn main() {
    let args = Args::parse();
    let config = derive_config(args.clone());

    // Require a path to resolve imports on disk.
    let entry_path = args
        .input
        .unwrap_or_else(|| PathBuf::from("benchmark/IsZeroWordOperation/is_zero_word.cz"));

    // Resolve and parse the entry + imports.
    let mut modules =
        match resolve_and_parse_modules(&entry_path, &[] /* extra roots if any */) {
            Ok(ms) => ms,
            Err(e) => {
                eprintln!("error during import resolution: {e}");
                std::process::exit(1);
            }
        };

    // Build Context across all modules.
    let ctx = Rc::new(init_context(&mut modules));

    if let Err(err) = check_equivalence(&modules[0].file, Rc::clone(&ctx), config) {
        eprintln!("✖ Equivalence check failed: {err}");
        std::process::exit(1);
    } else {
        println!("✔ Equivalence check passed");
    }
}
