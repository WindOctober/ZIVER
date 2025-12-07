pub mod ast;
mod checker;
pub mod parser;
mod utils;
use clap::{ArgAction, Parser};
use std::env;
use std::path::PathBuf;
use std::rc::Rc;

use crate::checker::check_equivalence;
use crate::checker::symbolic::context::init_context;
use crate::utils::derive_config;
use crate::utils::module_resolver::resolve_and_parse_modules;

const DEFAULT_BENCHMARK: &str = "benchmark/SP1/IsZeroWordOperation/is_zero_word.cz";

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
    #[arg(long, value_name = "SOLVER", default_value = "z3_nia")]
    pub solver: String,

    /// Command or path used to invoke cvc5 when `--solver cvc5_ff` is selected.
    #[arg(long, value_name = "CMD", default_value = "cvc5")]
    pub cvc5_cmd: String,
}

fn main() {
    let args = Args::parse();
    let config = derive_config(args.clone());
    let trace = env::var("CZC_TRACE").is_ok();

    // Require a path to resolve imports on disk.
    let entry_path = args
        .input
        .unwrap_or_else(|| PathBuf::from(DEFAULT_BENCHMARK));

    if trace {
        eprintln!("CZC_TRACE: resolving entry {:?}", entry_path);
    }

    // Resolve and parse the entry + imports.
    let mut modules =
        match resolve_and_parse_modules(&entry_path, &[] /* extra roots if any */) {
            Ok(ms) => ms,
            Err(e) => {
                eprintln!("error during import resolution: {e}");
                std::process::exit(1);
            }
        };

    if trace {
        eprintln!("CZC_TRACE: parsed {} modules", modules.len());
    }

    // Build Context across all modules.
    let ctx = Rc::new(init_context(&mut modules));

    if trace {
        eprintln!(": context initialized, starting equivalence check");
    }

    if let Err(err) = check_equivalence(&modules[0].file, Rc::clone(&ctx), config) {
        eprintln!("✖ Equivalence check failed: {err}");
        std::process::exit(1);
    } else {
        println!("✔ Equivalence check passed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        checker::check_equivalence, checker::symbolic::context::init_context,
        utils::module_resolver::resolve_and_parse_modules,
    };
    use std::rc::Rc;

    fn run_case(path: &str, solver: &str) {
        let args = Args {
            input: Some(PathBuf::from(path)),
            ast: false,
            type_opt: true,
            solver: solver.to_string(),
            cvc5_cmd: "cvc5".to_string(),
        };
        let config = derive_config(args.clone());

        // Resolve and parse modules rooted at the benchmark file.
        let mut modules =
            resolve_and_parse_modules(args.input.as_ref().unwrap(), &[]).expect("parse failed");

        let ctx = Rc::new(init_context(&mut modules));

        if let Err(e) = check_equivalence(&modules[0].file, Rc::clone(&ctx), config) {
            panic!(
                "equivalence check for {} with {} failed: {}",
                path, solver, e
            );
        }
    }

    #[test]
    fn component_benchmarks_without_add4() {
        // Backend mapping mirrors the benchmark script but skips add4 (too slow for tests).
        let cases = vec![
            ("benchmark/SP1/Add/add.cz", "z3_nia"),
            ("benchmark/SP1/IsEqualWordOperation/is_equal.cz", "cvc5_ff"),
            (DEFAULT_BENCHMARK, "cvc5_ff"),
        ];

        for (path, solver) in cases {
            run_case(path, solver);
        }
    }
}
