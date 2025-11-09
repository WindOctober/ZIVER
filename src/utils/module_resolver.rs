use crate::ast::File;
use crate::parser::parse_file;
use anyhow::{Context as AnyCtx, Result, anyhow};
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

/// A parsed module with its qualified path segments.
#[derive(Clone, Debug)]
pub struct Module {
    // pub path: Vec<String>, // e.g., ["foo","bar"] for import foo::bar;
    pub file: File,
}

/// Resolve and parse the entry file and its transitive imports.
pub fn resolve_and_parse_modules(
    entry_path: &Path,
    import_roots: &[PathBuf],
) -> Result<Vec<Module>> {
    let root_dir = entry_path
        .parent()
        .ok_or_else(|| anyhow!("entry path has no parent"))?
        .to_path_buf();

    // Build the effective search roots: entry's dir + user-provided roots.
    let mut roots = Vec::new();
    roots.push(root_dir);
    roots.extend(import_roots.iter().cloned());

    // Parse the entry file as the "root" (empty module path).
    let entry_src = fs::read_to_string(entry_path)
        .with_context(|| format!("failed to read {}", entry_path.display()))?;
    let entry_file = parse_file(&entry_src)
        .with_context(|| format!("failed to parse {}", entry_path.display()))?;

    let mut out = Vec::new();
    let mut visited = HashSet::<Vec<String>>::new(); // avoid re-parsing same module path
    let mut file_cache = HashMap::<PathBuf, File>::new(); // optional disk cache

    // Push the entry module with empty path.
    out.push(Module {
        // path: vec![],
        file: entry_file,
    });

    // Worklist: (module_path, file_ast)
    let mut idx = 0;
    while idx < out.len() {
        let file = out[idx].file.clone();

        // Scan imports in this file and resolve them.
        for it in &file.items {
            if let crate::ast::Item::Import { path, .. } = it {
                let import_path = path.clone(); // ["a","b","c"]
                if !visited.insert(import_path.clone()) {
                    continue; // already loaded
                }
                // Map import a::b::c -> roots/a/b/c.cz
                let import_file_path =
                    resolve_import_to_path(&roots, &import_path).with_context(|| {
                        format!(
                            "cannot resolve import {:?} to a file under roots",
                            import_path
                        )
                    })?;

                // Read + parse (use cache if wanted)
                let parsed = if let Some(f) = file_cache.get(&import_file_path) {
                    f.clone()
                } else {
                    let src = fs::read_to_string(&import_file_path).with_context(|| {
                        format!("failed to read {}", import_file_path.display())
                    })?;
                    let f = parse_file(&src).with_context(|| {
                        format!("failed to parse {}", import_file_path.display())
                    })?;
                    file_cache.insert(import_file_path.clone(), f.clone());
                    f
                };

                out.push(Module {
                    // path: import_path,
                    file: parsed,
                });
            }
        }
        idx += 1;
    }

    Ok(out)
}

/// Convert ["a","b","c"] into <root>/a/b/c.cz by searching roots in order.
/// Returns the first match.
fn resolve_import_to_path(roots: &[PathBuf], segs: &[String]) -> Result<PathBuf> {
    for r in roots {
        let mut p = r.clone();
        for s in segs {
            p.push(s);
        }
        p.set_extension("cz");
        if p.exists() {
            return Ok(p);
        }
    }
    Err(anyhow!("not found under any root"))
}
