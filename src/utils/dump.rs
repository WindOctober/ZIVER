use std::fmt::Debug;
use std::path::PathBuf;
use std::process::exit;

/// Reports the result of parsing a CZ DSL file in a consistent and formatted manner.
/// On success, prints either a confirmation message or the full AST depending on the
/// command-line flag. On failure, prints an error diagnostic and terminates execution.
pub fn dump_parse_result<T: Debug>(
    result: &Result<T, String>,
    input_path: &Option<PathBuf>,
    show_ast: bool,
) {
    match result {
        Ok(file) => {
            if show_ast {
                match input_path {
                    Some(p) => println!("=== Parsed AST (source: {}) ===", p.display()),
                    None => println!("=== Parsed AST (source: <stdin>) ==="),
                }
                println!("{:#?}", file);
            } else {
                match input_path {
                    Some(p) => println!("✔ Parsed successfully: {}", p.display()),
                    None => println!("✔ Parsed successfully: <stdin>"),
                }
            }
        }
        Err(e) => {
            let src_name = input_path
                .as_ref()
                .map(|p| p.display().to_string())
                .unwrap_or_else(|| "<stdin>".into());
            eprintln!("✖ Parse error in '{}':\n{}", src_name, e);
            exit(1);
        }
    }
}
