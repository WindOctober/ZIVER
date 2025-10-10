pub mod ast;
pub mod parser;

use std::env;
use std::fs;
use std::path::Path;
use std::process;

fn main() {
    // Determine the input path: use CLI arg if provided, otherwise use the default benchmark file.
    let input_path = env::args()
        .nth(1)
        .unwrap_or_else(|| "benchmark/operations/is_zero_word.cz".to_string());

    // Validate that the file exists to provide an early and clear diagnostic.
    if !Path::new(&input_path).exists() {
        eprintln!(
            "error: input file not found: {}\n\
             hint: run `cargo run -- <path/to/file.cz>` or place the file at the default path.",
            input_path
        );
        process::exit(1);
    }

    // Read the entire source into memory. This is sufficient for a benchmark-scale DSL file.
    let src = match fs::read_to_string(&input_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: failed to read '{}': {e}", input_path);
            process::exit(1);
        }
    };

    // Parse the file via our pest-based frontend.
    match parser::parse_file(&src) {
        Ok(file) => {
            // Pretty-print the AST to stdout for inspection.
            println!("=== Parsed AST (source: {input_path}) ===");
            println!("{:#?}", file);
        }
        Err(e) => {
            // Report a structured error message and exit with failure.
            eprintln!("error: parse failed for '{}':\n{e}", input_path);
            process::exit(1);
        }
    }
}
