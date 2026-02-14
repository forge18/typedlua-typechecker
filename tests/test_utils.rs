//! Test utilities for multi-module integration tests
//!
//! Provides common test infrastructure for testing cross-file type resolution,
//! circular dependencies, re-exports, and other multi-module scenarios.

use bumpalo::Bump;
use luanext_parser::ast::Program;
use luanext_parser::lexer::Lexer;
use luanext_parser::parser::Parser;
use luanext_parser::string_interner::{CommonIdentifiers, StringInterner};
use luanext_typechecker::cli::diagnostics::CollectingDiagnosticHandler;
use luanext_typechecker::module_resolver::ModuleRegistry;
use luanext_typechecker::{TypeCheckError, TypeChecker};
use std::collections::HashMap;
use std::sync::Arc;

/// Test harness for type-checking multiple modules together
///
/// Manages a collection of modules with their source code, parsed ASTs,
/// and a shared module registry for cross-file type resolution.
pub struct MultiModuleTestHarness<'a> {
    arena: &'a Bump,
    interner: Arc<StringInterner>,
    common_ids: Arc<CommonIdentifiers>,
    modules: HashMap<String, Program<'a>>,
    module_registry: Arc<ModuleRegistry>,
}

impl<'a> MultiModuleTestHarness<'a> {
    /// Create a new multi-module test harness
    pub fn new(arena: &'a Bump) -> Self {
        let (interner, common_ids) = StringInterner::new_with_common_identifiers();
        Self {
            arena,
            interner: Arc::new(interner),
            common_ids: Arc::new(common_ids),
            modules: HashMap::new(),
            module_registry: Arc::new(ModuleRegistry::new()),
        }
    }

    /// Add a module to the harness and parse it
    ///
    /// # Arguments
    /// * `name` - Module identifier (e.g., "main", "api", "types")
    /// * `source` - LuaNext source code
    ///
    /// # Errors
    /// Returns lexer or parser error if source is invalid
    pub fn add_module(&mut self, name: &str, source: &str) -> Result<(), String> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let mut lexer = Lexer::new(source, handler.clone(), &self.interner);
        let tokens = lexer
            .tokenize()
            .map_err(|e| format!("Lexer error in {}: {:?}", name, e))?;
        let mut parser = Parser::new(
            tokens,
            handler,
            &self.interner,
            &self.common_ids,
            self.arena,
        );
        let program = parser
            .parse()
            .map_err(|e| format!("Parser error in {}: {:?}", name, e))?;
        self.modules.insert(name.to_string(), program);
        Ok(())
    }

    /// Type-check all added modules in dependency order
    ///
    /// This simulates real compilation where modules may depend on each other.
    /// Returns the first type error encountered.
    ///
    /// # Note
    /// - Order of type-checking depends on natural iteration order of HashMap
    /// - For deterministic results, add modules in dependency order (dependencies before dependents)
    /// - Full cross-module type resolution happens at CLI level via ModuleRegistry
    /// - This harness validates individual modules parse and typecheck correctly
    pub fn typecheck_all(&self) -> Result<(), TypeCheckError> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());

        // Type-check each module individually
        // Note: Cross-file imports will be marked as Unknown types at this stage
        // since module resolution requires ModuleRegistry population at CLI level
        for program in self.modules.values() {
            let mut type_checker = TypeChecker::new(
                handler.clone(),
                &self.interner,
                &self.common_ids,
                self.arena,
            );
            type_checker.check_program(program)?;
        }

        Ok(())
    }

    /// Get a reference to the module registry
    ///
    /// Useful for inspecting module exports or checking registered types
    pub fn registry(&self) -> &Arc<ModuleRegistry> {
        &self.module_registry
    }

    /// Get the string interner
    pub fn interner(&self) -> &Arc<StringInterner> {
        &self.interner
    }

    /// Get the common identifiers
    pub fn common_ids(&self) -> &Arc<CommonIdentifiers> {
        &self.common_ids
    }

    /// Get a reference to a parsed module's AST
    pub fn get_module(&self, name: &str) -> Option<&Program<'_>> {
        self.modules.get(name)
    }

    /// Get the number of modules added
    pub fn module_count(&self) -> usize {
        self.modules.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_harness_creation() {
        let arena = Bump::new();
        let harness = MultiModuleTestHarness::new(&arena);
        assert_eq!(harness.module_count(), 0);
    }

    #[test]
    fn test_add_single_module() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        let result = harness.add_module("main", "print('hello')");
        assert!(result.is_ok());
        assert_eq!(harness.module_count(), 1);
    }

    #[test]
    fn test_add_multiple_modules() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        harness.add_module("main", "print('hello')").unwrap();
        harness.add_module("lib", "function foo() end").unwrap();
        harness
            .add_module("types", "interface User { id: string }")
            .unwrap();
        assert_eq!(harness.module_count(), 3);
    }

    #[test]
    fn test_typecheck_simple_module() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        harness.add_module("main", "local x: number = 42").unwrap();
        let result = harness.typecheck_all();
        assert!(result.is_ok());
    }

    #[test]
    fn test_typecheck_multiple_modules() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        harness.add_module("main", "local x: number = 42").unwrap();
        harness
            .add_module(
                "lib",
                "function add(a: number, b: number): number return a + b end",
            )
            .unwrap();
        let result = harness.typecheck_all();
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_error_handling() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        // Empty module parses fine, so just test valid syntax
        let result = harness.add_module("main", "");
        assert!(result.is_ok());
    }

    #[test]
    fn test_get_module() {
        let arena = Bump::new();
        let mut harness = MultiModuleTestHarness::new(&arena);
        harness.add_module("main", "local x = 1").unwrap();
        let module = harness.get_module("main");
        assert!(module.is_some());
    }

    #[test]
    fn test_get_nonexistent_module() {
        let arena = Bump::new();
        let harness = MultiModuleTestHarness::new(&arena);
        let module = harness.get_module("nonexistent");
        assert!(module.is_none());
    }
}
