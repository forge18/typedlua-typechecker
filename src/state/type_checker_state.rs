//! Type checker state module
//!
//! This module contains the shared state structure for the type checker,
//! extracted from the monolithic TypeChecker to enable better modularity
//! and testability.

use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use typedlua_parser::ast::statement::TypeParameter;
use typedlua_parser::string_interner::{CommonIdentifiers, StringInterner};

use crate::cli::config::CompilerOptions;
use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_environment::TypeEnvironment;
use crate::module_resolver::{ModuleId, ModuleRegistry, ModuleResolver};
use crate::utils::symbol_table::SymbolTable;
use crate::visitors::{AccessControl, TypeNarrower};
use typedlua_parser::ast::types::Type;

/// Shared state for the type checker
///
/// This struct contains all the mutable state that was previously embedded
/// directly in TypeChecker. Extracting it enables:
/// - Better testability (state can be created independently)
/// - Phase-based decomposition (different phases can share state)
/// - Reduced cognitive load (state is separated from logic)
pub struct TypeCheckerState<'a> {
    /// Symbol table for tracking variable and type declarations
    pub symbol_table: SymbolTable,
    /// Type environment for type checking and inference
    pub type_env: TypeEnvironment,
    /// Current function's return type (for return statement validation)
    pub current_function_return_type: Option<Type>,
    /// Type narrowing state for control flow analysis
    pub narrowing: TypeNarrower,
    /// Access control for class inheritance and visibility
    pub access_control: AccessControl,
    /// Compiler options (target version, optimization level, etc.)
    pub options: CompilerOptions,
    /// Diagnostic handler for reporting errors and warnings
    pub diagnostic_handler: Arc<dyn DiagnosticHandler>,
    /// String interner for efficient string handling
    pub interner: &'a StringInterner,
    /// Common identifiers (keywords, built-in types, etc.)
    pub common: &'a CommonIdentifiers,
    /// Module registry for multi-module compilation
    pub module_registry: Option<Arc<ModuleRegistry>>,
    /// Current module ID
    pub current_module_id: Option<ModuleId>,
    /// Module resolver for import path resolution
    pub module_resolver: Option<Arc<ModuleResolver>>,
    /// Track module dependencies for cache invalidation
    pub module_dependencies: Vec<PathBuf>,
    /// Stack tracking whether we're inside a catch block (for rethrow validation)
    pub in_catch_block: Vec<bool>,
    /// Current namespace path for this module
    pub current_namespace: Option<Vec<String>>,
    /// Type parameters for each generic class (needed for override checking)
    pub class_type_params: FxHashMap<String, Vec<TypeParameter>>,
    /// Track class inheritance for circular dependency detection
    pub class_parents: FxHashMap<String, String>,
    /// Track exported names to detect duplicates
    pub exported_names: HashSet<String>,
}

impl<'a> TypeCheckerState<'a> {
    /// Create a new type checker state with default values
    pub fn new(
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
        interner: &'a StringInterner,
        common: &'a CommonIdentifiers,
    ) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            type_env: TypeEnvironment::new(),
            current_function_return_type: None,
            narrowing: TypeNarrower::new(),
            access_control: AccessControl::new(),
            options: CompilerOptions::default(),
            diagnostic_handler,
            interner,
            common,
            module_registry: None,
            current_module_id: None,
            module_resolver: None,
            module_dependencies: Vec::new(),
            in_catch_block: Vec::new(),
            current_namespace: None,
            class_type_params: FxHashMap::default(),
            class_parents: FxHashMap::default(),
            exported_names: HashSet::new(),
        }
    }

    /// Create a new type checker state with module support
    pub fn new_with_module_support(
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
        interner: &'a StringInterner,
        common: &'a CommonIdentifiers,
        module_registry: Arc<ModuleRegistry>,
        current_module_id: ModuleId,
        module_resolver: Arc<ModuleResolver>,
    ) -> Self {
        let mut state = Self::new(diagnostic_handler, interner, common);
        state.module_registry = Some(module_registry);
        state.current_module_id = Some(current_module_id);
        state.module_resolver = Some(module_resolver);
        state
    }

    /// Create a new type checker state using dependency injection container
    ///
    /// # Arguments
    ///
    /// * `container` - The dependency injection container
    /// * `interner` - String interner for efficient string handling
    /// * `common` - Common identifiers (keywords, built-in types, etc.)
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let container = DiContainer::new();
    /// let state = TypeCheckerState::new_with_di(&container, &interner, &common);
    /// ```
    pub fn new_with_di(
        container: &mut crate::DiContainer,
        interner: &'a StringInterner,
        common: &'a CommonIdentifiers,
    ) -> Self {
        let diagnostic_handler = container
            .resolve::<Arc<dyn DiagnosticHandler>>()
            .expect("DiagnosticHandler must be registered in DI container");
        let options = container.resolve::<CompilerOptions>().unwrap_or_default();

        Self {
            symbol_table: SymbolTable::new(),
            type_env: TypeEnvironment::new(),
            current_function_return_type: None,
            narrowing: TypeNarrower::new(),
            access_control: AccessControl::new(),
            options,
            diagnostic_handler,
            interner,
            common,
            module_registry: None,
            current_module_id: None,
            module_resolver: None,
            module_dependencies: Vec::new(),
            in_catch_block: Vec::new(),
            current_namespace: None,
            class_type_params: FxHashMap::default(),
            class_parents: FxHashMap::default(),
            exported_names: HashSet::new(),
        }
    }

    /// Create a new type checker state with module support using DI
    pub fn new_with_module_support_di(
        container: &mut crate::DiContainer,
        interner: &'a StringInterner,
        common: &'a CommonIdentifiers,
        module_registry: Arc<ModuleRegistry>,
        current_module_id: ModuleId,
        module_resolver: Arc<ModuleResolver>,
    ) -> Self {
        let mut state = Self::new_with_di(container, interner, common);
        state.module_registry = Some(module_registry);
        state.current_module_id = Some(current_module_id);
        state.module_resolver = Some(module_resolver);
        state
    }

    /// Get the current module ID as a string reference
    pub fn current_module_id_str(&self) -> Option<&str> {
        self.current_module_id.as_ref().map(|id| id.as_str())
    }

    /// Check if we're currently inside a catch block
    pub fn is_in_catch_block(&self) -> bool {
        self.in_catch_block.last().copied().unwrap_or(false)
    }

    /// Push a new catch block context
    pub fn push_catch_block(&mut self, in_catch: bool) {
        self.in_catch_block.push(in_catch);
    }

    /// Pop the current catch block context
    pub fn pop_catch_block(&mut self) {
        self.in_catch_block.pop();
    }

    /// Get the full namespace path as a string
    pub fn namespace_path(&self) -> String {
        match &self.current_namespace {
            Some(parts) => parts.join("."),
            None => String::new(),
        }
    }

    /// Check if a class is already registered
    pub fn has_class(&self, name: &str) -> bool {
        self.class_parents.contains_key(name) || self.class_type_params.contains_key(name)
    }

    /// Get the parent class for a given class
    pub fn get_parent_class(&self, class_name: &str) -> Option<&str> {
        self.class_parents.get(class_name).map(|s| s.as_str())
    }

    /// Register a class with its parent
    pub fn register_class(&mut self, name: String, parent: Option<String>) {
        if let Some(parent_name) = parent {
            self.class_parents.insert(name, parent_name);
        }
    }

    /// Check if a name is already exported
    pub fn is_exported(&self, name: &str) -> bool {
        self.exported_names.contains(name)
    }

    /// Mark a name as exported
    pub fn mark_exported(&mut self, name: String) -> bool {
        self.exported_names.insert(name)
    }

    /// Add a module dependency
    pub fn add_dependency(&mut self, path: PathBuf) {
        if !self.module_dependencies.contains(&path) {
            self.module_dependencies.push(path);
        }
    }

    /// Get all module dependencies
    pub fn get_dependencies(&self) -> &[PathBuf] {
        &self.module_dependencies
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::diagnostics::CollectingDiagnosticHandler;
    use std::sync::Arc;
    use typedlua_parser::string_interner::StringInterner;

    fn create_test_state() -> TypeCheckerState<'static> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let (interner, common) = StringInterner::new_with_common_identifiers();
        // Leak the interner to get a 'static reference for tests
        let interner = Box::leak(Box::new(interner));
        let common = Box::leak(Box::new(common));
        TypeCheckerState::new(handler, interner, common)
    }

    #[test]
    fn test_state_creation() {
        let state = create_test_state();
        assert!(state.current_function_return_type.is_none());
        assert!(state.module_registry.is_none());
        assert!(state.current_module_id.is_none());
    }

    #[test]
    fn test_catch_block_tracking() {
        let mut state = create_test_state();
        assert!(!state.is_in_catch_block());

        state.push_catch_block(true);
        assert!(state.is_in_catch_block());

        state.push_catch_block(false);
        assert!(!state.is_in_catch_block());

        state.pop_catch_block();
        assert!(state.is_in_catch_block());

        state.pop_catch_block();
        assert!(!state.is_in_catch_block());
    }

    #[test]
    fn test_class_registration() {
        let mut state = create_test_state();
        assert!(!state.has_class("MyClass"));

        state.register_class("MyClass".to_string(), Some("ParentClass".to_string()));
        assert!(state.has_class("MyClass"));
        assert_eq!(state.get_parent_class("MyClass"), Some("ParentClass"));
    }

    #[test]
    fn test_export_tracking() {
        let mut state = create_test_state();
        assert!(!state.is_exported("foo"));

        assert!(state.mark_exported("foo".to_string()));
        assert!(state.is_exported("foo"));

        // Second insert should return false (already exists)
        assert!(!state.mark_exported("foo".to_string()));
    }

    #[test]
    fn test_dependencies() {
        let mut state = create_test_state();
        assert!(state.get_dependencies().is_empty());

        state.add_dependency(PathBuf::from("/path/to/module.lua"));
        assert_eq!(state.get_dependencies().len(), 1);

        // Duplicate should not be added
        state.add_dependency(PathBuf::from("/path/to/module.lua"));
        assert_eq!(state.get_dependencies().len(), 1);
    }
}
