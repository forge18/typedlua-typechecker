pub mod config;
pub mod diagnostics;
pub mod errors;
pub mod fs;
mod generics;
mod helpers;
pub mod module_resolver;
mod narrowing_integration;
mod state;
mod stdlib;
mod symbol_table;
mod type_checker;
mod type_compat;
mod type_environment;
mod utility_types;
mod visitors;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod symbol_table_tests;

pub use generics::{
    build_substitutions, check_type_constraints, infer_type_arguments,
    instantiate_function_declaration, instantiate_type,
};
pub use visitors::{narrow_type_from_condition, NarrowingContext};
pub use state::TypeCheckerState;
pub use symbol_table::{
    Scope, SerializableSymbol, SerializableSymbolTable, Symbol, SymbolKind, SymbolTable,
};
pub use type_checker::TypeChecker;
pub use type_compat::TypeCompatibility;
pub use type_environment::TypeEnvironment;
pub use utility_types::{
    apply_utility_type, evaluate_conditional_type, evaluate_keyof, evaluate_mapped_type,
    evaluate_template_literal_type,
};

use typedlua_parser::span::Span;

/// Type checker error
#[derive(Debug, Clone)]
pub struct TypeCheckError {
    pub message: String,
    pub span: Span,
}

impl TypeCheckError {
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

impl std::fmt::Display for TypeCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {}:{}",
            self.message, self.span.line, self.span.column
        )
    }
}

impl std::error::Error for TypeCheckError {}
