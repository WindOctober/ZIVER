use crate::Args;

pub mod dump;

pub struct SetConfig {
    pub type_refine: bool,
}

/// Derive the runtime configuration from CLI arguments.
///
/// Currently maps the `--no-type-opt` switch (default: enabled) to `SetConfig::type_refine`.
pub fn derive_config(args: Args) -> SetConfig {
    SetConfig {
        // `type_opt` is `true` by default; `--no-type-opt` flips it to `false`.
        type_refine: args.type_opt,
    }
}
