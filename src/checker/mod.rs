pub(crate) mod solver;
pub(crate) mod symbolic;

use std::rc::Rc;

use crate::{ast::File, checker::symbolic::context::Context, utils::SetConfig};

pub fn derive_context(_file: &File) -> Context {
    unimplemented!()
}

/// Checks the semantic equivalence between `populate` and `eval`
/// functions within each component of the parsed file.
pub fn check_equivalence(file: &File, ctx: Rc<Context>, config: SetConfig) -> Result<(), String> {
    for (_, name, members, query_opt) in file.components() {
        // Anonymous closure to find a function by name.
        let query = match query_opt {
            Some(q) => q,
            None => return Err(format!("Component `{}` missing `Query` clause", name)),
        };

        if query.lhs.is_empty() || query.rhs.is_empty() {
            return Err(format!(
                "Component `{}`: `Query` sides must be non-empty",
                name
            ));
        }

        // First path on each side selects the member to check.
        let lhs_head = query.lhs[0].last().expect("non-empty path");
        let rhs_head = query.rhs[0].last().expect("non-empty path");

        let find_fn = |target: &str| members.iter().find(|m| m.name() == target);

        let lhs_member = find_fn(lhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found for LHS of Query",
                name, lhs_head
            )
        })?;
        let rhs_member = find_fn(rhs_head.as_str()).ok_or_else(|| {
            format!(
                "Component `{}`: member `{}` not found for RHS of Query",
                name, rhs_head
            )
        })?;

        // Remaining paths must align 1:1; record them for later processing.
        let lhs_tail = &query.lhs[1..];
        let rhs_tail = &query.rhs[1..];

        if lhs_tail.len() != rhs_tail.len() {
            return Err(format!(
                "Component `{}`: `Query` sides have different arity (LHS {}, RHS {})",
                name,
                lhs_tail.len(),
                rhs_tail.len()
            ));
        }

        // Keep the pairs for future checks (placeholders for now).
        let _member_pair = (lhs_member, rhs_member);
        let _arg_pairs: Vec<(&Vec<String>, &Vec<String>)> =
            lhs_tail.iter().zip(rhs_tail.iter()).collect();
    }

    Ok(())
}
