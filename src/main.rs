pub mod ast;
mod checker;
pub mod parser;
mod utils;

use clap::{ArgAction, Parser};
use std::path::PathBuf;

use crate::checker::check_equivalence;
use crate::checker::symbolic::context::init_context;
use crate::utils::derive_config;
use crate::utils::module_resolver::resolve_and_parse_modules;

/// Command-line interface for the CZ parser.
#[derive(Parser, Debug, Clone)]
#[command(
    name = "czc",
    version,
    about = "Parse a CZ DSL file and optionally pretty-print its AST."
)]
struct Args {
    /// Path to the input `.cz` file. Defaults to a benchmark file if omitted.
    #[arg(value_name = "PATH")]
    input: Option<PathBuf>,

    /// Print the parsed AST to stdout in a pretty format.
    #[arg(long, action = ArgAction::SetTrue)]
    ast: bool,

    /// Enables the optimization of *type-based modular arithmetic simplification* (enabled by default).
    /// Use `--no-type-opt` to disable this optimization, which is useful for conducting ablation studies.
    #[arg(long = "no-type-opt", alias = "disable-type-opt",
          action = ArgAction::SetFalse, default_value_t = true)]
    type_opt: bool,
}

fn main() {
    let args = Args::parse();
    let config = derive_config(args.clone());

    // Require a path to resolve imports on disk.
    let entry_path = args.input.unwrap_or_else(|| {
        // your default: benchmark/operations/is_zero_word.cz
        std::path::PathBuf::from("benchmark/operations/is_zero_word.cz")
    });

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
    let ctx = init_context(&mut modules);

    // If you still need a single File for later passes, you can concatenate items,
    // or adapt downstream code to consume `ctx` directly.

    // Run your checker over the entry module (modules[0]) or over all modules as you need.
    if let Err(err) = check_equivalence(&modules[0].file, config) {
        eprintln!("✖ Equivalence check failed: {err}");
        std::process::exit(1);
    } else {
        println!("✔ Equivalence check passed");
    }
}
