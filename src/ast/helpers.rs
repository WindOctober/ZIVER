use std::collections::HashMap;

use crate::checker::symbolic::context::{Context, PathKind};

use super::*;

/// Build a name → parameter-binding expression map for a function.
/// Each entry is an `Expr::Path` that refers to the parameter binding inside `func`
/// (with a resolved `ref_id`).
pub fn build_param_expr_map(func: &Func) -> HashMap<String, Expr> {
    let mut map = HashMap::new();
    for p in &func.params {
        match p {
            Param::SelfParam { id } => {
                let vid = id.expect("self parameter id must be assigned during resolve");
                map.insert(
                    "self".to_string(),
                    Expr::Path {
                        segments: vec!["self".to_string()],
                        ref_id: Some(vid),
                    },
                );
            }
            Param::Typed { id, name, .. } => {
                let vid = id.expect("parameter id must be assigned during resolve");
                map.insert(
                    name.clone(),
                    Expr::Path {
                        segments: vec![name.clone()],
                        ref_id: Some(vid),
                    },
                );
            }
        }
    }
    map
}

impl File {
    /// Iterate all `Component`s with their (optional) IDs.
    /// Returns `(id, &name, &members)`.
    pub fn components(
        &self,
    ) -> impl Iterator<Item = (Option<i64>, &String, &Vec<Member>, &Option<Query>)> {
        self.items.iter().filter_map(|item| match item {
            Item::Component {
                id,
                name,
                members,
                query,
            } => Some((*id, name, members, query)),
            _ => None,
        })
    }
}

/// Provides basic accessors for AST nodes.
impl Member {
    /// Returns the identifier name of the function contained in this member.
    pub fn name(&self) -> &str {
        match self {
            Member::Computation(f) | Member::Constraint(f) => &f.name,
        }
    }

    /// Return the underlying function definition, abstracting over
    /// computation and constraint members.
    pub fn as_func(&self) -> &Func {
        match self {
            Member::Computation(f) | Member::Constraint(f) => f,
        }
    }
}

impl Type {
    /// Ensures this type is not array or function.
    /// Panics with a descriptive message if disallowed.
    pub fn assert_not_composite(&self, ctx: &str) {
        match self {
            Type::Array(_, _) => {
                panic!("array type is not supported in {ctx}: requires allocation semantics");
            }
            Type::Function { .. } => {
                panic!("function type is not first-class in {ctx}");
            }
            Type::Path { .. } => {} // allowed
        }
    }

    /// Rejects function-typed variables in declarations.
    pub fn assert_not_function(&self, ctx: &str) {
        if matches!(self, Type::Function { .. }) {
            panic!("function type not allowed in {ctx}");
        }
    }

    /// Checks whether the type is a builtin scalar type.
    pub fn is_scalar(&self, ctx: &Context) -> bool {
        match self {
            Type::Path { .. } => {
                matches!(ctx.classify_type(self), Ok(PathKind::Builtin))
            }
            _ => false,
        }
    }
}

impl Func {
    /// Translate a query-side path (e.g., ["self"] or ["cols"]) into an
    /// expression that references the corresponding parameter binding
    /// inside this function. Currently, only single-segment paths are
    /// supported/
    pub fn query_path_to_param_expr(&self, path: &[String]) -> Result<Expr, String> {
        if path.len() != 1 {
            return Err(format!(
                "nested query path `{:?}` is not supported; only single-segment paths are allowed",
                path
            ));
        }

        let head = &path[0];

        // Special-case handling for the implicit `self` parameter.
        if head == "self" {
            for p in &self.params {
                if let Param::SelfParam { id: Some(vid) } = p {
                    return Ok(Expr::Path {
                        segments: vec![head.clone()],
                        ref_id: Some(*vid),
                    });
                }
            }
            return Err(format!(
                "query path {:?} refers to `self`, but function `{}` has no self parameter",
                path, self.name
            ));
        }

        // Otherwise, resolve the path head against explicitly named parameters.
        for p in &self.params {
            if let Param::Typed {
                id: Some(vid),
                name,
                ..
            } = p
            {
                if name == head {
                    return Ok(Expr::Path {
                        segments: vec![head.clone()],
                        ref_id: Some(*vid),
                    });
                }
            }
        }

        Err(format!(
            "query path {:?} does not match any parameter of function `{}`",
            path, self.name
        ))
    }
}
