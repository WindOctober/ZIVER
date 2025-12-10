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
    /// Filesystem path of this module.
    pub path: PathBuf,
    // pub path: Vec<String>, // e.g., ["foo","bar"] for import foo::bar;
    pub file: File,
}

/// A grouped collection of modules for VM-style verification.
#[derive(Clone, Debug, Default)]
pub struct VmWorkspace {
    /// All parsed modules in this workspace (deduped by path).
    pub modules: Vec<Module>,
    /// Index of the compute entry module in `modules`, if found.
    pub compute_entry: Option<usize>,
    /// Index of the constraint entry module in `modules`, if found.
    pub constraint_entry: Option<usize>,
    /// Indices of shared input modules in `modules` (e.g., input.cz).
    pub input_modules: Vec<usize>,
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
        path: entry_path.to_path_buf(),
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
                    path: import_file_path.clone(),
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

/// Resolve and parse every `.cz` file under `root_dir`, deduping by path, and
/// pick out conventional entry points (compute.cz, constraint.cz, input.cz).
pub fn resolve_vm_workspace(root_dir: &Path, import_roots: &[PathBuf]) -> Result<VmWorkspace> {
    if !root_dir.is_dir() {
        return Err(anyhow!(
            "VM workspace root `{}` is not a directory",
            root_dir.display()
        ));
    }

    let mut cz_files = Vec::<PathBuf>::new();
    let mut stack = vec![root_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir).with_context(|| format!("reading {}", dir.display()))? {
            let entry = entry?;
            let path = entry.path();
            let file_type = entry.file_type()?;
            if file_type.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().map(|e| e == "cz").unwrap_or(false) {
                cz_files.push(path);
            }
        }
    }

    // Conventional entry names.
    let mut compute_entry_path: Option<PathBuf> = None;
    let mut constraint_entry_path: Option<PathBuf> = None;
    let mut input_paths: Vec<PathBuf> = Vec::new();
    for p in &cz_files {
        if let Some(stem) = p.file_stem().and_then(|s| s.to_str()) {
            match stem {
                "compute" => {
                    if compute_entry_path.is_none() {
                        compute_entry_path = Some(p.clone());
                    }
                }
                "constraint" => {
                    if constraint_entry_path.is_none() {
                        constraint_entry_path = Some(p.clone());
                    }
                }
                "input" => input_paths.push(p.clone()),
                _ => {}
            }
        }
    }

    // Reuse a cache to avoid parsing the same file repeatedly.
    let mut seen = HashMap::<PathBuf, usize>::new();
    let mut modules = Vec::<Module>::new();

    let mut extra_roots = Vec::new();
    extra_roots.push(root_dir.to_path_buf());
    extra_roots.extend_from_slice(import_roots);

    let add_modules =
        |mods: Vec<Module>, modules: &mut Vec<Module>, seen: &mut HashMap<PathBuf, usize>| {
            for m in mods {
                let key = fs::canonicalize(&m.path).unwrap_or_else(|_| m.path.clone());
                if seen.contains_key(&key) {
                    continue;
                }
                let idx = modules.len();
                seen.insert(key.clone(), idx);
                modules.push(Module {
                    path: key,
                    file: m.file,
                });
            }
        };

    // Parse every cz file we found so imports are resolved transitively.
    for cz in &cz_files {
        let mods = resolve_and_parse_modules(cz, &extra_roots)?;
        add_modules(mods, &mut modules, &mut seen);
    }

    // Map entry paths into module indices.
    let lookup_idx = |p: Option<PathBuf>, seen: &HashMap<PathBuf, usize>| -> Option<usize> {
        p.and_then(|raw| {
            let key = fs::canonicalize(&raw).unwrap_or(raw);
            seen.get(&key).copied()
        })
    };

    let compute_entry = lookup_idx(compute_entry_path, &seen);
    let constraint_entry = lookup_idx(constraint_entry_path, &seen);
    let input_modules = input_paths
        .into_iter()
        .filter_map(|p| lookup_idx(Some(p), &seen))
        .collect::<Vec<_>>();

    Ok(VmWorkspace {
        modules,
        compute_entry,
        constraint_entry,
        input_modules,
    })
}
