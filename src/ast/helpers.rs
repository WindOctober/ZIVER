use super::*;

/// Returns an iterator over all `Component` declarations in the file.
impl File {
    pub fn components(&self) -> impl Iterator<Item = (&String, &Vec<Member>)> {
        self.items.iter().filter_map(|item| match item {
            Item::Component { name, members } => Some((name, members)),
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
