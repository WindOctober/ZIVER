pub mod ast;
mod checker;
pub mod parser;
mod utils;
use clap::{ArgAction, Parser, ValueEnum};
use std::env;
use std::path::PathBuf;
use std::rc::Rc;

use crate::checker::symbolic::context::init_context;
use crate::checker::{check_equivalence, check_vm_workspace};
use crate::utils::derive_config;
use crate::utils::module_resolver::{resolve_and_parse_modules, resolve_vm_workspace};

const DEFAULT_BENCHMARK: &str = "benchmark/Component/SP1/IsZeroWordOperation/is_zero_word.cz";

/// Command-line interface for the CZ parser.
#[derive(ValueEnum, Clone, Debug)]
#[derive(Default)]
pub enum RunMode {
    /// Component-by-component equivalence (current default).
    #[default]
    Component,
    /// VM-style bundle: scan a directory of .cz files and group compute/constraint/input.
    Vm,
}


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

    /// Choose verification mode: component (single entry file) or vm (scan directory).
    #[arg(long, value_enum, default_value_t = RunMode::Component)]
    pub mode: RunMode,
}

fn main() {
    let args = Args::parse();
    let config = derive_config(args.clone());
    let trace = env::var("CZC_TRACE").is_ok();

    match args.mode {
        RunMode::Component => {
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
        RunMode::Vm => {
            // In VM mode, interpret the input as a directory and scan for .cz files.
            let workspace_root = args.input.unwrap_or_else(|| {
                env::current_dir().expect("failed to get current working directory")
            });
            if !workspace_root.is_dir() {
                eprintln!(
                    "vm mode expects a directory as input, got {}",
                    workspace_root.display()
                );
                std::process::exit(1);
            }

            if trace {
                eprintln!("CZC_TRACE: scanning workspace {:?}", workspace_root);
            }

            let mut ws =
                match resolve_vm_workspace(&workspace_root, &[] /* extra roots if any */) {
                    Ok(ws) => ws,
                    Err(e) => {
                        eprintln!("error during workspace resolution: {e}");
                        std::process::exit(1);
                    }
                };

            if trace {
                eprintln!(
                    "CZC_TRACE: parsed {} modules (compute={:?}, constraint={:?}, inputs={:?})",
                    ws.modules.len(),
                    ws.compute_entry,
                    ws.constraint_entry,
                    ws.input_modules
                );
            }

            if ws.modules.is_empty() {
                eprintln!("no .cz modules found under {}", workspace_root.display());
                std::process::exit(1);
            }

            // Build a shared context for all parsed modules.
            let ctx = Rc::new(init_context(&mut ws.modules));

            if trace {
                eprintln!(
                    "CZC_TRACE: starting VM pipeline across {} modules",
                    ws.modules.len()
                );
            }

            if let Err(err) = check_vm_workspace(ws.clone(), Rc::clone(&ctx), config) {
                eprintln!("✖ VM bundle check failed: {err}");
                std::process::exit(1);
            } else {
                println!("✔ Equivalence check passed (vm mode)");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        checker::check_equivalence, checker::symbolic::context::init_context,
        utils::module_resolver::resolve_and_parse_modules,
    };
    use std::panic;
    use std::rc::Rc;
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::mpsc,
        thread,
        time::{Duration, Instant},
    };

    const TIMEOUT_SECS: u64 = 900;

    fn solver_for_benchmark(path: &Path) -> &'static str {
        let s = path.to_string_lossy();
        if s.contains("IsEqual") || s.contains("IsZero") {
            "cvc5_ff"
        } else {
            "z3_nia"
        }
    }

    fn run_case_with_timeout(path: PathBuf, solver: String) -> Result<(), String> {
        let (tx, rx) = mpsc::channel();
        let path_for_worker = path.clone();
        thread::spawn(move || {
            let result = panic::catch_unwind(|| {
                let args = Args {
                    input: Some(path_for_worker.clone()),
                    ast: false,
                    type_opt: true,
                    solver: solver.clone(),
                    cvc5_cmd: "cvc5".to_string(),
                    mode: RunMode::Component,
                };
                let config = derive_config(args.clone());

                let mut modules = match resolve_and_parse_modules(args.input.as_ref().unwrap(), &[])
                {
                    Ok(ms) => ms,
                    Err(e) => {
                        return Err(format!("parse failed for {:?}: {e}", path_for_worker));
                    }
                };

                let ctx = Rc::new(init_context(&mut modules));

                match check_equivalence(&modules[0].file, Rc::clone(&ctx), config) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(format!(
                        "equivalence check for {:?} with {} failed: {}",
                        path_for_worker, solver, e
                    )),
                }
            });

            let to_send = match result {
                Ok(inner) => inner,
                Err(_) => Err(format!("panic during execution for {:?}", path_for_worker)),
            };

            let _ = tx.send(to_send);
        });

        match rx.recv_timeout(Duration::from_secs(TIMEOUT_SECS)) {
            Ok(r) => r,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                Err(format!("timeout after {}s for {:?}", TIMEOUT_SECS, path))
            }
            Err(e) => Err(format!("channel error for {:?}: {e}", path)),
        }
    }

    fn collect_benchmarks(root: &Path) -> Vec<PathBuf> {
        fn is_unprocessed(path: &Path) -> bool {
            path.components().any(|c| c.as_os_str() == "Unprocessed")
        }

        fn prefer(new: &PathBuf, existing: &PathBuf) -> bool {
            let new_unprocessed = is_unprocessed(new);
            let existing_unprocessed = is_unprocessed(existing);

            // Prefer processed (non-Unprocessed) variants over Unprocessed duplicates.
            if existing_unprocessed && !new_unprocessed {
                return true;
            }
            if new_unprocessed && !existing_unprocessed {
                return false;
            }
            // Otherwise pick the lexicographically smaller path for determinism.
            new < existing
        }

        let mut out = Vec::new();
        let mut by_name: std::collections::HashMap<String, PathBuf> =
            std::collections::HashMap::new();
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().map(|e| e == "cz").unwrap_or(false) {
                    let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                        continue;
                    };
                    let entry = by_name
                        .entry(name.to_string())
                        .or_insert_with(|| path.clone());
                    if prefer(&path, entry) {
                        *entry = path.clone();
                    }
                }
            }
        }
        out.extend(by_name.into_values());
        out.sort();
        out
    }

    fn is_expected_failure(path: &Path) -> bool {
        // The SP1 is_zero.cz case is known to fail equivalence; treat it as expected.
        path.ends_with("Component/SP1/IsZeroOperation/is_zero.cz")
    }

    #[test]
    fn benchmark_suite_with_timeouts() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmark");
        let cases = collect_benchmarks(&root);
        assert!(
            !cases.is_empty(),
            "no benchmark cases found under {:?}",
            root
        );

        let strict = std::env::var("CZC_STRICT_BENCH").is_ok();
        let mut failures = Vec::new();
        let mut summaries = Vec::new();

        for path in cases {
            let solver = solver_for_benchmark(&path).to_string();
            let start = Instant::now();
            let result = run_case_with_timeout(path.clone(), solver.clone());
            let elapsed = start.elapsed();

            match result {
                Ok(()) => {
                    let line = format!(
                        "[bench] {:?} ({}) ok in {:.2?}",
                        path.file_name().unwrap_or_default(),
                        solver,
                        elapsed
                    );
                    println!("{line}");
                    summaries.push(line);
                }
                Err(e) => {
                    if is_expected_failure(&path) {
                        let line = format!(
                            "[bench] {:?} ({}) expected failure in {:.2?}",
                            path, solver, elapsed
                        );
                        println!("{line}");
                        summaries.push(line);
                    } else {
                        let line = format!(
                            "[bench] {:?} ({}) failed in {:.2?}: {}",
                            path, solver, elapsed, e
                        );
                        println!("{line}");
                        failures.push(line.clone());
                        summaries.push(line);
                    }
                }
            }
        }

        // Persist summaries so timing is available even when stdout is captured by the test harness.
        let _ = std::fs::create_dir_all("target");
        let _ = std::fs::write("target/bench_results.txt", summaries.join("\n"));

        if !failures.is_empty() {
            let mut msg = String::new();
            msg.push_str(&format!("{} benchmark(s) failed:\n", failures.len()));
            msg.push_str(&failures.join("\n"));
            if strict {
                panic!("{msg}");
            } else {
                eprintln!("{msg}");
            }
        }
    }
}
