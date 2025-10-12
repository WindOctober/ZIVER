pub(crate) mod solver;
pub(crate) mod symbolic;
use crate::ast::File;

/// Checks the semantic equivalence between `populate` and `eval`
/// functions within each component of the parsed file.
pub fn check_equivalence(file: &File) -> Result<(), String> {
    for (name, members) in file.components() {
        // Anonymous closure to find a function by name.
        let find_fn = |target: &str| members.iter().find(|m| m.name() == target);

        let populate_fn = find_fn("populate");
        let eval_fn = find_fn("eval");

        match (populate_fn, eval_fn) {
            (Some(pop), Some(eval)) => {}
            (None, Some(_)) => return Err(format!("Component `{}` missing `populate`", name)),
            (Some(_), None) => return Err(format!("Component `{}` missing `eval`", name)),
            (None, None) => {
                return Err(format!(
                    "Component `{}` has neither `populate` nor `eval`",
                    name
                ));
            }
        }
    }

    Ok(())
}
