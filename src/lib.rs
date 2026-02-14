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
    CompilationCache, DeclarationHash, DeclarationId, DependencyGraph, IncrementalChecker,
    InvalidationResult,
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

use luanext_parser::span::Span;

/// Type checker error
#[derive(Debug, Clone)]
pub struct TypeCheckError {
    pub message: String,
    pub span: Span,
    pub suggestion: Option<String>,
}

impl TypeCheckError {
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
            suggestion: None,
        }
    }

    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }
}

impl std::fmt::Display for TypeCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {}:{}",
            self.message, self.span.line, self.span.column
        )?;
        if let Some(suggestion) = &self.suggestion {
            write!(f, ". Did you mean '{}'?", suggestion)?;
        }
        Ok(())
    }
}

impl std::error::Error for TypeCheckError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_check_error_display() {
        let error = TypeCheckError::new("test error", Span::new(0, 10, 1, 2));
        assert_eq!(format!("{}", error), "test error at 1:2");
    }

    #[test]
    fn test_type_check_error_with_suggestion() {
        let error = TypeCheckError::new("Undefined variable 'userNme'", Span::new(0, 10, 1, 2))
            .with_suggestion("userName");
        assert_eq!(
            format!("{}", error),
            "Undefined variable 'userNme' at 1:2. Did you mean 'userName'?"
        );
    }
}
