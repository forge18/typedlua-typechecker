//! Dependency Injection module for TypedLua type checker
//!
//! This module provides a lightweight dependency injection container
//! for managing service lifetimes and dependencies throughout the
//! type checking pipeline.

pub mod container;
pub mod error;

pub use container::{DiContainer, ServiceLifetime};
pub use error::DiError;

#[cfg(test)]
mod tests;

/// Create a default DI container with common services registered
pub fn create_default_container() -> DiContainer {
    use crate::cli::config::CompilerOptions;
    use crate::cli::diagnostics::CollectingDiagnosticHandler;
    use std::sync::Arc;

    let mut container = DiContainer::new();

    // Register core services
    container.register(
        |_| {
            Arc::new(CollectingDiagnosticHandler::new())
                as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        ServiceLifetime::Singleton,
    );

    container.register(|_| CompilerOptions::default(), ServiceLifetime::Singleton);

    container
}
