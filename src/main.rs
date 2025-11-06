pub mod ast;
pub(crate) mod checker;
pub mod parser;
pub(crate) mod utils;

use clap::{ArgAction, Parser};
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::process::exit;

use crate::checker::check_equivalence;
use crate::utils::derive_config;
use crate::utils::dump::dump_parse_result;

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

    /// Read the source program from standard input instead of a file.
    #[arg(long, action = ArgAction::SetTrue)]
    stdin: bool,

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

    let (src, input_path) = parse_source(args.input, args.stdin);

    // Parse the file
    let result = parser::parse_file(&src).map_err(|e| e.to_string());
    dump_parse_result(&result, &input_path, args.ast);

    if let Ok(file) = &result {
        if let Err(err) = check_equivalence(file, config) {
            eprintln!("✖ Equivalence check failed: {err}");
            exit(1);
        } else {
            println!("✔ Equivalence check passed");
        }
    }
}

/// Reads and returns the source code of a CZ DSL program from the provided input.
/// Supports both file-based and standard-input modes, with a default fallback path
/// if no input is specified. Terminates immediately on any unrecoverable I/O error.
pub fn parse_source(input: Option<PathBuf>, use_stdin: bool) -> (String, Option<PathBuf>) {
    // Determine source mode.
    if use_stdin {
        use std::io::{self, Read};
        let mut buf = String::new();
        if let Err(e) = io::stdin().read_to_string(&mut buf) {
            eprintln!("error: failed to read from stdin: {e}");
            process::exit(1);
        }
        return (buf, None);
    }

    // Resolve path or fallback to default benchmark file.
    let input_path = match input {
        Some(p) => p,
        None => PathBuf::from("benchmark/operations/is_zero_word.cz"),
    };

    if !Path::new(&input_path).exists() {
        eprintln!(
            "error: input file not found: {}\n\
             hint: run `path/to/czc <path/to/file.cz>` or place the file at the default path.",
            input_path.display()
        );
        process::exit(1);
    }

    let src = match fs::read_to_string(&input_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: failed to read '{}': {e}", input_path.display());
            process::exit(1);
        }
    };

    (src, Some(input_path))
}
