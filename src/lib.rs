pub mod cli;
pub mod core;
pub mod di;
pub mod helpers;
pub mod incremental;
pub mod module_resolver;
pub mod phases;
pub mod state;
pub mod stdlib;
pub mod test_utils;
pub mod type_relations;
pub mod types;
pub mod utils;
pub mod visitors;

pub use core::type_checker::TypeChecker;
pub use core::type_compat::TypeCompatibility;
pub use core::type_environment::TypeEnvironment;
pub use di::{DiContainer, ServiceLifetime};
pub use incremental::{
    CompilationCache, DeclarationId, DependencyGraph, IncrementalChecker, InvalidationResult,
};
pub use state::TypeCheckerState;
pub use types::generics::{
    build_substitutions, check_type_constraints, infer_type_arguments,
    instantiate_function_declaration, instantiate_type,
};
pub use types::utility_types::{
    apply_utility_type, evaluate_conditional_type, evaluate_keyof, evaluate_mapped_type,
    evaluate_template_literal_type,
};
pub use utils::symbol_table::{
    Scope, SerializableSymbol, SerializableSymbolTable, Symbol, SymbolKind, SymbolTable,
};
pub use visitors::{narrow_type_from_condition, NarrowingContext};

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
