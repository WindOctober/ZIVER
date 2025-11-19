pub(crate) mod solver;
pub(crate) mod symbolic;

use std::rc::Rc;

use crate::{
    ast::{File, helpers::build_param_expr_map},
    checker::{
        solver::check_with_z3,
        symbolic::{
            context::Context,
            execute::SymbolicExecutor,
            expr::{BoolExpr, SymExpr},
            state::SymState,
        },
    },
    utils::SetConfig,
};

/// Checks the semantic equivalence between `populate` and `eval`
/// functions within each component of the parsed file.
pub fn check_equivalence(file: &File, ctx: Rc<Context>, _config: SetConfig) -> Result<(), String> {
    // Iterate over all components and their associated queries.
    for (_, comp_name, members, query_opt) in file.components() {
        let query = match query_opt {
            Some(q) => q,
            None => {
                return Err(format!(
                    "Component `{}` is missing a `Query` clause, which is required for equivalence checking",
                    comp_name
                ));
            }
        };

        if query.lhs.is_empty() || query.rhs.is_empty() {
            return Err(format!(
                "Component `{}`: both sides of `Query` must be non-empty",
                comp_name
            ));
        }

        // The first path on each side identifies the member (function) to compare.
        let lhs_head = query.lhs[0]
            .last()
            .expect("left-hand side of Query must contain at least one segment");
        let rhs_head = query.rhs[0]
            .last()
            .expect("right-hand side of Query must contain at least one segment");

        // Resolve member names to concrete component members.
        let find_member = |target: &str| members.iter().find(|m| m.name() == target);

        let lhs_member = find_member(lhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found for the left-hand side of Query",
                comp_name, lhs_head
            )
        })?;
        let rhs_member = find_member(rhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found for the right-hand side of Query",
                comp_name, rhs_head
            )
        })?;

        // Use the new member method to access the underlying functions.
        let lhs_func = lhs_member.as_func();
        let rhs_func = rhs_member.as_func();

        // For now, we assume queries of the canonical form:
        //   Query(populate,self; eval,cols)
        if query.lhs.len() != 2 || query.rhs.len() != 2 {
            return Err(format!(
                "Component `{}`: currently only queries of the form `Query(f,self; g,cols)` are supported",
                comp_name
            ));
        }

        let lhs_root_path = &query.lhs[1];
        let rhs_root_path = &query.rhs[1];

        // Use the method on `Func` to translate query roots into parameter-bound expressions.
        let lhs_root_expr = lhs_func.query_path_to_param_expr(lhs_root_path)?;
        let rhs_root_expr = rhs_func.query_path_to_param_expr(rhs_root_path)?;

        // Initialize symbolic states for the two executions.
        let lhs_init = SymState::new(Rc::clone(&ctx));
        let rhs_init = SymState::new(Rc::clone(&ctx));

        // Execute both functions symbolically (single-path only for now).
        let lhs_terms = lhs_func.clone().execute(lhs_init);
        let rhs_terms = rhs_func.clone().execute(rhs_init);

        if lhs_terms.len() != 1 || rhs_terms.len() != 1 {
            return Err(format!(
                "Component `{}`: branching executions are not yet supported (lhs states = {}, rhs states = {})",
                comp_name,
                lhs_terms.len(),
                rhs_terms.len(),
            ));
        }

        let (_lhs_ret, lhs_final) = lhs_terms[0].clone();
        let (_rhs_ret, rhs_final) = rhs_terms[0].clone();

        // Locate the query-specified roots (e.g., `self` and `cols`) in the final stores.
        let lhs_root_node = lhs_final.query_expr_node(&lhs_root_expr).ok_or_else(|| {
            format!(
                "Component `{}`: failed to locate the left root `{:?}` in the final store",
                comp_name, lhs_root_path
            )
        })?;

        let rhs_root_node = rhs_final.query_expr_node(&rhs_root_expr).ok_or_else(|| {
            format!(
                "Component `{}`: failed to locate the right root `{:?}` in the final store",
                comp_name, rhs_root_path
            )
        })?;

        // Recursively extract all leaf-level scalar pairs from the two roots.
        let mut out_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();
        lhs_root_node.collect_scalar_pairs_with(rhs_root_node, &mut out_pairs)?;

        if out_pairs.is_empty() {
            return Err(format!(
                "Component `{}`: no scalar outputs were discovered under the queried roots",
                comp_name
            ));
        }

        let lhs_params = build_param_expr_map(lhs_func);
        let rhs_params = build_param_expr_map(rhs_func);

        let lhs_root_name = lhs_root_path
            .first()
            .expect("lhs root path must contain at least one segment");
        let rhs_root_name = rhs_root_path
            .first()
            .expect("rhs root path must contain at least one segment");

        // Collect scalar pairs for matched non-root input parameters.
        let mut input_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();

        // Left-to-right: every non-root lhs parameter must either:
        //   - have a counterpart with the same name on the rhs, or
        //   - be exactly the rhs root parameter (which we skip).
        for (name, lhs_param_expr) in lhs_params.iter() {
            // Skip the query root parameter on lhs (e.g., `self`).
            if name == lhs_root_name {
                continue;
            }

            // Try to find a parameter with the same name on rhs.
            if let Some(rhs_param_expr) = rhs_params.get(name) {
                let lhs_node = lhs_final
                    .query_expr_node(lhs_param_expr)
                    .ok_or_else(|| {
                        format!(
                            "Component `{}`: failed to locate lhs input parameter `{}` in the final store",
                            comp_name, name
                        )
                    })?;
                let rhs_node = rhs_final
                    .query_expr_node(rhs_param_expr)
                    .ok_or_else(|| {
                        format!(
                            "Component `{}`: failed to locate rhs input parameter `{}` in the final store",
                            comp_name, name
                        )
                    })?;

                lhs_node.collect_scalar_pairs_with(rhs_node, &mut input_pairs)?;
            } else if name != rhs_root_name {
                // A non-root parameter exists only on lhs but not on rhs: structural mismatch.
                return Err(format!(
                    "Component `{}`: parameter `{}` present in `{}` but missing in `{}`",
                    comp_name, name, lhs_func.name, rhs_func.name
                ));
            }
        }

        // Right-to-left: check rhs for extra non-root parameters not present on lhs.
        for (name, _) in rhs_params.iter() {
            if name == rhs_root_name {
                continue; // skip rhs query root (e.g., `cols`)
            }
            if !lhs_params.contains_key(name) && name != lhs_root_name {
                return Err(format!(
                    "Component `{}`: parameter `{}` present in `{}` but missing in `{}`",
                    comp_name, name, rhs_func.name, lhs_func.name
                ));
            }
        }

        // Turn all collected input scalar pairs into equality atoms and conjoin them.
        let eq_inputs = if input_pairs.is_empty() {
            // No shared inputs beyond query roots; treat as trivially equal.
            BoolExpr::Bool(true)
        } else {
            let mut atoms = Vec::with_capacity(input_pairs.len());
            for (a, b) in input_pairs {
                atoms.push(BoolExpr::Eq(a, b));
            }
            BoolExpr::and(atoms)
        };

        // --------------------------------------------------------------------
        // Path conditions + output difference as before.
        // --------------------------------------------------------------------

        // Construct the overall path conditions for the two executions.
        let pc_lhs = lhs_final.pc();
        let pc_rhs = rhs_final.pc();

        // Encode the disjunction that at least one output scalar pair differs.
        let mut diff_atoms = Vec::new();
        for (a, b) in out_pairs {
            // Disequality on scalar outputs becomes a Boolean atom.
            diff_atoms.push(BoolExpr::Ne(a, b));
        }
        let outputs_diff = BoolExpr::or(diff_atoms);

        // Final formula: both path conditions hold, all shared inputs coincide,
        // and at least one observed output scalar differs.
        //
        // If this formula is satisfiable, then there exists a concrete model
        // witnessing a behavioral difference between the two functions.
        // If it is unsatisfiable, the two functions are equivalent under the
        // current single-path symbolic semantics.
        let phi = BoolExpr::and(vec![pc_lhs, pc_rhs, eq_inputs, outputs_diff]);

        match check_with_z3(&phi) {
            Ok(false) => {
                // UNSAT: no counterexample exists for this component.
                println!(
                    "Component `{}`: SMT check reports UNSAT; equivalence holds under the encoded semantics.",
                    comp_name
                );
            }
            Ok(true) => {
                // SAT: a counterexample exists, so equivalence fails.
                return Err(format!(
                    "Component `{}`: SMT check reports SAT; a counterexample to equivalence exists.",
                    comp_name
                ));
            }
            Err(e) => {
                // Unknown or failure is treated as a hard error for now.
                return Err(format!(
                    "Component `{}`: SMT solver failed or returned `unknown`: {}",
                    comp_name, e
                ));
            }
        }
    }

    Ok(())
}
