use crate::checker::symbolic::context::{Context, PathKind};

use super::*;

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
            Type::Map { .. } => {
                panic!("map type is not supported in {ctx}: requires allocation semantics");
            }
            Type::Tuple(_) => {
                panic!("tuple type is not supported in {ctx}: requires allocation semantics");
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
                matches!(
                    ctx.classify_type(self),
                    Ok(PathKind::Builtin) | Ok(PathKind::Enum(_))
                )
            }
            Type::Map { .. } => false,
            _ => false,
        }
    }
}

impl Func {
    /// Batch-resolve all query root paths to parameter expressions.
    pub fn query_root_exprs(&self, paths: &[Vec<String>]) -> Result<Vec<Expr>, String> {
        paths
            .iter()
            .map(|p| self.query_path_to_param_expr(p))
            .collect()
    }

    /// Return the IO role for a scalar parameter referenced by a query path.
    /// `self` is handled via struct field IO and returns `None`.
    pub fn param_io_for_query_path(&self, path: &[String]) -> Option<IOType> {
        let head = path.first()?;
        for p in &self.params {
            match p {
                Param::SelfParam { .. } => {
                    if head == "self" {
                        return None;
                    }
                }
                Param::Typed { name, io, .. } if name == head => {
                    return Some(io.clone());
                }
                _ => {}
            }
        }
        None
    }

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
                && name == head {
                    return Ok(Expr::Path {
                        segments: vec![head.clone()],
                        ref_id: Some(*vid),
                    });
                }
        }

        Err(format!(
            "query path {:?} does not match any parameter of function `{}`",
            path, self.name
        ))
    }
}
