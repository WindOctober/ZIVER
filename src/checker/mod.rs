pub(crate) mod solver;
pub(crate) mod symbolic;

use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{File, IOType, Item},
    checker::{
        solver::check_with_z3,
        symbolic::{
            context::Context,
            execute::SymbolicExecutor,
            expr::{BoolExpr, SymExpr},
            state::{StoreNode, SymState},
        },
    },
    utils::SetConfig,
};
/// Equivalence checking under a Query specification.
/// The Query selects two struct-typed roots (for example `self` and `cols`).
/// Input fields of these roots are constrained to be equal; output
/// fields are required to coincide under all such inputs.
pub fn check_equivalence(file: &File, ctx: Rc<Context>, _config: SetConfig) -> Result<(), String> {
    /// Builds a map from field id to IOType for the given struct id by
    /// looking up the corresponding `Struct` declaration in the file.
    fn build_field_roles(file: &File, struct_id: i64) -> Result<HashMap<i64, IOType>, String> {
        for item in &file.items {
            if let Item::Struct { id, fields, .. } = item {
                if id.map_or(false, |sid| sid == struct_id) {
                    let mut map = HashMap::new();
                    for f in fields {
                        let fid = f.id.ok_or_else(|| {
                            "field id must be assigned during resolve".to_string()
                        })?;
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

    // Iterate over all components and check the associated Query, if any.
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

        // Currently only support queries of the form: Query(f,self; g,cols)
        if query.lhs.len() != 2 || query.rhs.len() != 2 {
            return Err(format!(
                "Component `{}`: only `Query(f,self; g,cols)`-style queries are supported",
                comp_name
            ));
        }

        // Resolve the two functions referenced in the Query.
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

        // Resolve root parameters on both sides (for example `self` and `cols`).
        let lhs_root_path = &query.lhs[1];
        let rhs_root_path = &query.rhs[1];

        let lhs_root_expr = lhs_func.query_path_to_param_expr(lhs_root_path)?;
        let rhs_root_expr = rhs_func.query_path_to_param_expr(rhs_root_path)?;

        // Both roots are expected to be instances of the same component struct.
        let struct_id = ctx
            .struct_id_by_name(comp_name.as_str())
            .ok_or_else(|| format!("no struct index recorded for `{}`", comp_name))?;

        let field_roles = build_field_roles(file, struct_id)?;

        // Execute both sides under single-path semantics.
        let lhs_terms = lhs_func.clone().execute(SymState::new(Rc::clone(&ctx)));
        let rhs_terms = rhs_func.clone().execute(SymState::new(Rc::clone(&ctx)));

        if lhs_terms.is_empty() || rhs_terms.is_empty() {
            return Err(format!(
                "Component `{}`: no terminal paths produced on LHS ({}) or RHS ({})",
                comp_name,
                lhs_terms.len(),
                rhs_terms.len()
            ));
        }

        // For every pair of terminal paths (lhs_i, rhs_j), we check that
        // there is no model with equal inputs and differing outputs
        // under the conjunction of their path conditions.
        for (li, (_lhs_ret, lhs_final)) in lhs_terms.iter().enumerate() {
            for (rj, (_rhs_ret, rhs_final)) in rhs_terms.iter().enumerate() {
                // Locate the two root struct instances in the final stores.
                let lhs_root_node = lhs_final.query_expr_node(&lhs_root_expr).ok_or_else(|| {
                    format!(
                        "Component `{}`: LHS root `{:?}` not found in final store for path {}",
                        comp_name, lhs_root_path, li
                    )
                })?;
                let rhs_root_node = rhs_final.query_expr_node(&rhs_root_expr).ok_or_else(|| {
                    format!(
                        "Component `{}`: RHS root `{:?}` not found in final store for path {}",
                        comp_name, rhs_root_path, rj
                    )
                })?;

                let (lhs_fields, rhs_fields) = match (lhs_root_node, rhs_root_node) {
                    (StoreNode::Struct { fields: lf }, StoreNode::Struct { fields: rf }) => {
                        (lf, rf)
                    }
                    _ => {
                        return Err(format!(
                            "Component `{}`: Query roots are expected to be struct values (lhs path {}, rhs path {})",
                            comp_name, li, rj
                        ));
                    }
                };

                // Enforce identical struct shape at the root.
                if lhs_fields.len() != rhs_fields.len() {
                    return Err(format!(
                        "Component `{}`: root struct shape mismatch (lhs has {}, rhs has {}) on paths ({}, {})",
                        comp_name,
                        lhs_fields.len(),
                        rhs_fields.len(),
                        li,
                        rj
                    ));
                }

                // Split scalar pairs into input fields and output fields.
                let mut input_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();
                let mut output_pairs: Vec<(SymExpr, SymExpr)> = Vec::new();

                let mut keys: Vec<i64> = lhs_fields.keys().cloned().collect();
                keys.sort_unstable();

                for fid in keys {
                    let role = field_roles.get(&fid).ok_or_else(|| {
                        format!(
                            "Component `{}`: no IO role recorded for field id {}",
                            comp_name, fid
                        )
                    })?;

                    let lnode = lhs_fields.get(&fid).ok_or_else(|| {
                        format!("lhs missing field id {} in root struct on path {}", fid, li)
                    })?;
                    let rnode = rhs_fields.get(&fid).ok_or_else(|| {
                        format!("rhs missing field id {} in root struct on path {}", fid, rj)
                    })?;

                    let (lv, rv) = match (lnode, rnode) {
                        (StoreNode::Scalar(a), StoreNode::Scalar(b)) => (a.clone(), b.clone()),
                        _ => {
                            return Err(format!(
                                "Component `{}`: non-scalar field id {} under Query root (paths {}, {})",
                                comp_name, fid, li, rj
                            ));
                        }
                    };

                    match role {
                        IOType::Input => input_pairs.push((lv, rv)),
                        IOType::Output => output_pairs.push((lv, rv)),
                    }
                }

                if output_pairs.is_empty() {
                    return Err(format!(
                        "Component `{}`: no output fields were found under the Query roots (paths {}, {})",
                        comp_name, li, rj
                    ));
                }

                // Constrain all input fields of the two roots to be equal.
                let eq_inputs = if input_pairs.is_empty() {
                    BoolExpr::Bool(true)
                } else {
                    let atoms: Vec<BoolExpr> = input_pairs
                        .into_iter()
                        .map(|(a, b)| BoolExpr::Eq(a, b))
                        .collect();
                    BoolExpr::and(atoms)
                };

                // Require at least one output field to differ in a counterexample.
                let outputs_diff = BoolExpr::or(
                    output_pairs
                        .into_iter()
                        .map(|(a, b)| BoolExpr::Ne(a, b))
                        .collect(),
                );

                let pc_lhs = lhs_final.pc();
                let pc_rhs = rhs_final.pc();

                // φ is satisfiable iff there exists a model with equal inputs and
                // differing outputs under both implementations along this path pair.
                let phi = BoolExpr::and(vec![pc_lhs, pc_rhs, eq_inputs, outputs_diff]);

                println!(
                    "Component `{}` (lhs path {}, rhs path {}): generated SMT formula for equivalence checking:\n{}",
                    comp_name, li, rj, phi
                );

                let sat = check_with_z3(&phi)?;
                if sat {
                    return Err(format!(
                        "Component `{}`: equivalence check failed; SMT found a model with equal inputs but differing outputs (lhs path {}, rhs path {})",
                        comp_name, li, rj
                    ));
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
