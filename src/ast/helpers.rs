use super::*;

impl File {
    /// Iterate all `Component`s with their (optional) IDs.
    /// Returns `(id, &name, &members)`.
    pub fn components(&self) -> impl Iterator<Item = (Option<i64>, &String, &Vec<Member>)> {
        self.items.iter().filter_map(|item| match item {
            Item::Component { id, name, members } => Some((*id, name, members)),
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
}
