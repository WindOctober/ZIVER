pub(crate) mod solver;
pub(crate) mod symbolic;
mod vm;
pub use vm::check_vm_workspace;

use std::{collections::HashMap, rc::Rc, time::Instant};

use crate::{
    ast::{Expr, File, Func, IOType, Item, Type},
    checker::{
        solver::{SmtBackend, backend_from_config, check_with_solver},
        symbolic::{
            context::{Context, PathKind},
            execute::SymbolicExecutor,
            expr::{BoolExpr, SymExpr},
            state::{StoreNode, SymState},
        },
    },
    utils::SetConfig,
};

/// Build a map from field id to IOType for the given struct id.
fn build_field_roles(file: &File, struct_id: i64) -> Result<HashMap<i64, IOType>, String> {
    for item in &file.items {
        if let Item::Struct { id, fields, .. } = item {
            if id.map_or(false, |sid| sid == struct_id) {
                let mut map = HashMap::new();
                for f in fields {
                    let fid =
                        f.id.ok_or_else(|| "field id must be assigned during resolve".to_string())?;
                    map.insert(fid, f.io.clone());
                }
                return Ok(map);
            }
        }
    }
    Err(format!(
        "no Struct with id {} found when building field roles",
        struct_id
    ))
}

/// Per-component query checking environment.
struct QueryCheck<'a> {
    file: &'a File,
    ctx: Rc<Context>,
    comp_name: &'a str,
    lhs_func: &'a Func,
    rhs_func: &'a Func,
    lhs_paths: &'a [Vec<String>],
    rhs_paths: &'a [Vec<String>],
    lhs_roots: Vec<Expr>,
    rhs_roots: Vec<Expr>,
}

impl<'a> QueryCheck<'a> {
    /// Construct the environment from a component-level Query.
    fn new(
        file: &'a File,
        ctx: Rc<Context>,
        comp_name: &'a str,
        lhs_func: &'a Func,
        rhs_func: &'a Func,
        lhs_paths: &'a [Vec<String>],
        rhs_paths: &'a [Vec<String>],
    ) -> Result<Self, String> {
        if lhs_paths.len() != rhs_paths.len() {
            return Err(format!(
                "Component `{}`: Query LHS and RHS must have the same number of entries",
                comp_name
            ));
        }
        if lhs_paths.len() < 2 {
            return Err(format!(
                "Component `{}`: Query must at least specify a function and one root on each side",
                comp_name
            ));
        }

        // Index 0 is the function name; roots start at index 1.
        let lhs_roots = lhs_func.query_root_exprs(&lhs_paths[1..])?;
        let rhs_roots = rhs_func.query_root_exprs(&rhs_paths[1..])?;

        Ok(Self {
            file,
            ctx,
            comp_name,
            lhs_func,
            rhs_func,
            lhs_paths,
            rhs_paths,
            lhs_roots,
            rhs_roots,
        })
    }

    /// Collect scalar input/output pairs contributed by the k-th root pair.
    fn collect_root_pairs(
        &self,
        k: usize,
        lhs_final: &SymState,
        rhs_final: &SymState,
        li: usize,
        rj: usize,
        input_pairs: &mut Vec<(SymExpr, SymExpr)>,
        output_pairs: &mut Vec<(SymExpr, SymExpr)>,
    ) -> Result<(), String> {
        let lhs_path = &self.lhs_paths[k + 1];
        let rhs_path = &self.rhs_paths[k + 1];
        let lhs_expr = &self.lhs_roots[k];
        let rhs_expr = &self.rhs_roots[k];

        let lhs_ty = self
            .ctx
            .infer_expr_type_static(lhs_expr)
            .ok_or_else(|| format!("failed to infer type for LHS root `{:?}`", lhs_path))?;

        let rhs_ty = self
            .ctx
            .infer_expr_type_static(rhs_expr)
            .ok_or_else(|| format!("failed to infer type for RHS root `{:?}`", rhs_path))?;

        // Struct roots (e.g. `self`, `cols`) are handled by field-level IO roles.
        if let (Type::Path { .. }, Type::Path { .. }) = (&lhs_ty, &rhs_ty) {
            if let (Ok(PathKind::Struct(lsid)), Ok(PathKind::Struct(rsid))) = (
                self.ctx.classify_type(&lhs_ty),
                self.ctx.classify_type(&rhs_ty),
            ) {
                if lsid != rsid {
                    return Err(format!(
                        "Component `{}`: root struct types differ (lhs {}, rhs {}, paths {}, {})",
                        self.comp_name, lsid, rsid, li, rj
                    ));
                }

                let field_roles = build_field_roles(self.file, lsid)?;

                let lhs_node = lhs_final.query_expr_node(lhs_expr).ok_or_else(|| {
                    format!(
                        "Component `{}`: LHS root `{:?}` not found (path {})",
                        self.comp_name, lhs_path, li
                    )
                })?;

                let rhs_node = rhs_final.query_expr_node(rhs_expr).ok_or_else(|| {
                    format!(
                        "Component `{}`: RHS root `{:?}` not found (path {})",
                        self.comp_name, rhs_path, rj
                    )
                })?;

                let (lhs_fields, rhs_fields) = match (lhs_node, rhs_node) {
                    (StoreNode::Struct { fields: lf }, StoreNode::Struct { fields: rf }) => {
                        (lf, rf)
                    }
                    _ => {
                        return Err(format!(
                            "Component `{}`: struct root expected (paths {}, {})",
                            self.comp_name, li, rj
                        ));
                    }
                };

                if lhs_fields.len() != rhs_fields.len() {
                    return Err(format!(
                        "Component `{}`: struct shape mismatch (lhs {}, rhs {}, paths {}, {})",
                        self.comp_name,
                        lhs_fields.len(),
                        rhs_fields.len(),
                        li,
                        rj
                    ));
                }

                let mut keys: Vec<i64> = lhs_fields.keys().cloned().collect();
                keys.sort_unstable();

                for fid in keys {
                    let io = field_roles.get(&fid).ok_or_else(|| {
                        format!(
                            "Component `{}`: missing IO role for field {}",
                            self.comp_name, fid
                        )
                    })?;

                    let lnode = lhs_fields
                        .get(&fid)
                        .ok_or_else(|| format!("lhs missing field {} on path {}", fid, li))?;
                    let rnode = rhs_fields
                        .get(&fid)
                        .ok_or_else(|| format!("rhs missing field {} on path {}", fid, rj))?;
                    let mut pairs = Vec::new();
                    lnode.collect_scalar_pairs_with(rnode, &mut pairs)?;

                    match io {
                        IOType::Input => input_pairs.extend(pairs),
                        IOType::Output => output_pairs.extend(pairs),
                    }
                }

                return Ok(());
            }
        }

        // Non-struct roots (scalars, arrays, nested composites) use parameter-level IO roles.
        let io_lhs = self
            .lhs_func
            .param_io_for_query_path(lhs_path)
            .ok_or_else(|| {
                format!(
                    "Component `{}`: missing IO role for LHS param `{:?}`",
                    self.comp_name, lhs_path
                )
            })?;

        let io_rhs = self
            .rhs_func
            .param_io_for_query_path(rhs_path)
            .ok_or_else(|| {
                format!(
                    "Component `{}`: missing IO role for RHS param `{:?}`",
                    self.comp_name, rhs_path
                )
            })?;

        if io_lhs != io_rhs {
            return Err(format!(
                "Component `{}`: mismatched IO roles for `{:?}` vs `{:?}`",
                self.comp_name, lhs_path, rhs_path
            ));
        }

        let lhs_node = lhs_final.query_expr_node(lhs_expr).ok_or_else(|| {
            format!(
                "Component `{}`: LHS root `{:?}` not found (path {})",
                self.comp_name, lhs_path, li
            )
        })?;

        let rhs_node = rhs_final.query_expr_node(rhs_expr).ok_or_else(|| {
            format!(
                "Component `{}`: RHS root `{:?}` not found (path {})",
                self.comp_name, rhs_path, rj
            )
        })?;

        let mut pairs = Vec::new();
        lhs_node.collect_scalar_pairs_with(rhs_node, &mut pairs)?;
        match io_lhs {
            IOType::Input => input_pairs.extend(pairs),
            IOType::Output => output_pairs.extend(pairs),
        }
        Ok(())
    }
}

/// Equivalence checking under a Query specification.
///
/// A Query has the general shape:
///   Query(f, r1, r2, ...; g, r1', r2', ...)
///
/// Entry 0 on each side is the member name (`f`, `g`); remaining entries are
/// roots (either struct-typed or scalar-typed parameters).
pub fn check_equivalence(file: &File, ctx: Rc<Context>, config: SetConfig) -> Result<(), String> {
    let trace = std::env::var("CZC_TRACE").is_ok();
    let backend = backend_from_config(&config);

    for (_, comp_name, members, query_opt) in file.components() {
        let query = match query_opt {
            Some(q) => q,
            None => {
                return Err(format!(
                    "Component `{}` is missing a `Query` clause",
                    comp_name
                ));
            }
        };

        // Resolve members for the function names.
        let lhs_head = query.lhs[0]
            .last()
            .expect("LHS of Query must contain at least one segment");
        let rhs_head = query.rhs[0]
            .last()
            .expect("RHS of Query must contain at least one segment");

        let find_member = |target: &str| members.iter().find(|m| m.name() == target);

        let lhs_member = find_member(lhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found on the LHS of Query",
                comp_name, lhs_head
            )
        })?;
        let rhs_member = find_member(rhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found on the RHS of Query",
                comp_name, rhs_head
            )
        })?;

        let lhs_func = lhs_member.as_func();
        let rhs_func = rhs_member.as_func();

        // Per-component environment capturing shared data.
        let env = QueryCheck::new(
            file,
            Rc::clone(&ctx),
            comp_name,
            lhs_func,
            rhs_func,
            &query.lhs,
            &query.rhs,
        )?;

        // Initialize parameters; materialize `self` if method.
        let fid: i64 = lhs_func.id.expect("function id must be set");
        let self_struct_id = ctx.method_owner(fid);

        // Execute LHS.
        let mut lhs_init = SymState::new(Rc::clone(&ctx));

        lhs_init.init_params_for_func(&lhs_func, self_struct_id);

        let lhs_exec_start = Instant::now();
        let lhs_terms = lhs_func.clone().execute(lhs_init);
        let lhs_exec_time = lhs_exec_start.elapsed();
        if lhs_terms.is_empty() {
            return Err(format!(
                "Component `{}`: no terminal paths produced on LHS",
                comp_name
            ));
        }

        // Avoid name clashes: RHS uses a fresh index starting after all LHS symbols.
        let max_fresh_lhs = lhs_terms
            .iter()
            .map(|(_, st)| st.fresh_index())
            .max()
            .unwrap_or(0);

        let mut rhs_init = SymState::new(Rc::clone(&ctx)).with_fresh_start(max_fresh_lhs);
        rhs_init.init_params_for_func(&rhs_func, self_struct_id);

        let rhs_exec_start = Instant::now();
        let rhs_terms = rhs_func.clone().execute(rhs_init);
        let rhs_exec_time = rhs_exec_start.elapsed();
        if rhs_terms.is_empty() {
            return Err(format!(
                "Component `{}`: no terminal paths produced on RHS",
                comp_name
            ));
        }

        if trace {
            eprintln!(
                "Component `{}`: built {} lhs paths in {:?}, {} rhs paths in {:?}; backend {:?}",
                comp_name,
                lhs_terms.len(),
                lhs_exec_time,
                rhs_terms.len(),
                rhs_exec_time,
                backend
            );
        }

        // Check all path pairs.
        let num_roots = query.lhs.len() - 1;
        for (li, (_lhs_ret, lhs_final)) in lhs_terms.iter().enumerate() {
            for (rj, (_rhs_ret, rhs_final)) in rhs_terms.iter().enumerate() {
                let mut input_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();
                let mut output_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();

                for k in 0..num_roots {
                    env.collect_root_pairs(
                        k,
                        lhs_final,
                        rhs_final,
                        li,
                        rj,
                        &mut input_pairs,
                        &mut output_pairs,
                    )?;
                }

                // Memory traces must also match.
                let lhs_events = lhs_final.memory_trace();
                let rhs_events = rhs_final.memory_trace();
                if lhs_events.len() != rhs_events.len() {
                    return Err(format!(
                        "Component `{}`: memory trace length mismatch (lhs path {}, rhs path {}): {} vs {}",
                        comp_name,
                        li,
                        rj,
                        lhs_events.len(),
                        rhs_events.len()
                    ));
                }

                for (idx, (le, re)) in lhs_events.iter().zip(rhs_events.iter()).enumerate() {
                    if le.kind != re.kind {
                        return Err(format!(
                            "Component `{}`: memory event kind mismatch at index {} between lhs path {} and rhs path {}",
                            comp_name, idx, li, rj
                        ));
                    }
                    output_pairs.push((le.clk.clone(), re.clk.clone()));
                    output_pairs.push((le.addr.clone(), re.addr.clone()));
                    output_pairs.push((le.value.clone(), re.value.clone()));
                }

                if output_pairs.is_empty() {
                    return Err(format!(
                        "Component `{}`: no output fields or parameters were found under the Query roots (paths {}, {})",
                        comp_name, li, rj
                    ));
                }

                let eq_inputs = if input_pairs.is_empty() {
                    BoolExpr::Bool(true)
                } else {
                    let atoms: Vec<BoolExpr> = input_pairs
                        .into_iter()
                        .map(|(a, b)| BoolExpr::Eq(a, b))
                        .collect();
                    BoolExpr::and(atoms)
                };

                let outputs_diff = BoolExpr::or(
                    output_pairs
                        .into_iter()
                        .map(|(a, b)| BoolExpr::Ne(a, b))
                        .collect(),
                );

                let pc_lhs = lhs_final.pc();
                let pc_rhs = rhs_final.pc();

                let phi = BoolExpr::and(vec![pc_lhs, pc_rhs, eq_inputs, outputs_diff]);
                // println!(
                //     "Component `{}` (lhs path {}, rhs path {}): generated SMT formula for equivalence checking:\n{}",
                //     comp_name, li, rj, phi
                // );

                if trace {
                    eprintln!(
                        "Component `{}`: solving path pair ({}, {})",
                        comp_name, li, rj
                    );
                }
                let solve_start = Instant::now();
                let sat = check_with_solver(&phi, backend.clone())?;
                let solve_time = solve_start.elapsed();
                if sat {
                    return Err(format!(
                        "Component `{}`: equivalence check failed; SMT found a model with equal inputs but differing outputs (lhs path {}, rhs path {})",
                        comp_name, li, rj
                    ));
                }
                if trace {
                    eprintln!(
                        "Component `{}`: path pair ({}, {}) proven equivalent in {:?}",
                        comp_name, li, rj, solve_time
                    );
                }
            }
        }

        println!(
            "Component `{}`: equivalence holds (no model with equal inputs and differing outputs across all path pairs)",
            comp_name
        );
    }

    Ok(())
}
