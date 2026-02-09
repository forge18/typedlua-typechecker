use super::error::{ModuleError, ModuleId};
use crate::{Symbol, SymbolKind, SymbolTable};
use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use std::sync::{Arc, RwLock};

/// Status of a module in the compilation pipeline
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleStatus {
    /// Module is parsed but not yet type-checked
    Parsed,
    /// Exports extracted but full type check not done
    ExportsExtracted,
    /// Module is fully type-checked
    TypeChecked,
}

/// A compiled module with its exports and symbol table
///
/// Note: AST is not stored here - it flows through CheckedModule in the CLI.
/// The registry only stores what's needed for cross-module type resolution.
/// Uses `'static` lifetimes since registry data outlives any single arena.
#[derive(Debug, Clone)]
pub struct CompiledModule {
    pub id: ModuleId,
    pub exports: ModuleExports,
    pub symbol_table: Arc<SymbolTable<'static>>,
    pub status: ModuleStatus,
}

/// Exports from a module
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Named exports: { foo, bar as baz }
    /// IndexMap for deterministic ordering in serialized output and LSP responses
    pub named: IndexMap<String, ExportedSymbol>,
    /// Default export: export default expr
    pub default: Option<ExportedSymbol>,
}

impl ModuleExports {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_named(&mut self, name: String, symbol: ExportedSymbol) {
        self.named.insert(name, symbol);
    }

    pub fn set_default(&mut self, symbol: ExportedSymbol) {
        self.default = Some(symbol);
    }

    pub fn get_named(&self, name: &str) -> Option<&ExportedSymbol> {
        self.named.get(name)
    }

    pub fn has_default(&self) -> bool {
        self.default.is_some()
    }
}

/// A symbol exported from a module
///
/// Uses `'static` because exported symbols are stored in the registry
/// and must outlive any single arena allocation.
#[derive(Debug, Clone)]
pub struct ExportedSymbol {
    pub symbol: Symbol<'static>,
    /// Whether this is a type-only export
    pub is_type_only: bool,
}

impl ExportedSymbol {
    pub fn new(symbol: Symbol<'static>, is_type_only: bool) -> Self {
        Self {
            symbol,
            is_type_only,
        }
    }

    /// Check if this symbol can be used at runtime
    pub fn is_runtime(&self) -> bool {
        !self.is_type_only
            && !matches!(
                self.symbol.kind,
                SymbolKind::TypeAlias | SymbolKind::Interface
            )
    }
}

/// Global registry of all compiled modules
#[derive(Debug)]
pub struct ModuleRegistry {
    modules: RwLock<FxHashMap<ModuleId, CompiledModule>>,
    /// Track lazy type-checking depth to prevent infinite recursion
    type_check_depth: RwLock<FxHashMap<ModuleId, usize>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: RwLock::new(FxHashMap::default()),
            type_check_depth: RwLock::new(FxHashMap::default()),
        }
    }

    /// Pre-populate registry from cached module data.
    /// Used at startup to load type info for unchanged files so that
    /// other files can resolve imports without re-type-checking.
    pub fn register_from_cache(
        &self,
        id: ModuleId,
        exports: ModuleExports,
        symbol_table: Arc<SymbolTable<'static>>,
    ) {
        let module = CompiledModule {
            id: id.clone(),
            exports,
            symbol_table,
            status: ModuleStatus::TypeChecked,
        };
        self.modules.write().unwrap().insert(id, module);
    }

    /// Register a parsed module (before type checking)
    pub fn register_parsed(&self, id: ModuleId, symbol_table: Arc<SymbolTable<'static>>) {
        let module = CompiledModule {
            id: id.clone(),
            exports: ModuleExports::new(),
            symbol_table,
            status: ModuleStatus::Parsed,
        };

        self.modules.write().unwrap().insert(id, module);
    }

    /// Register exports for a module (after export extraction)
    pub fn register_exports(
        &self,
        id: &ModuleId,
        exports: ModuleExports,
    ) -> Result<(), ModuleError> {
        let mut modules = self.modules.write().unwrap();
        let module = modules
            .get_mut(id)
            .ok_or_else(|| ModuleError::NotCompiled { id: id.clone() })?;

        module.exports = exports;
        module.status = ModuleStatus::ExportsExtracted;
        Ok(())
    }

    /// Mark a module as fully type-checked
    pub fn mark_checked(&self, id: &ModuleId) -> Result<(), ModuleError> {
        let mut modules = self.modules.write().unwrap();
        let module = modules
            .get_mut(id)
            .ok_or_else(|| ModuleError::NotCompiled { id: id.clone() })?;

        module.status = ModuleStatus::TypeChecked;
        Ok(())
    }

    /// Get a module by ID
    pub fn get_module(&self, id: &ModuleId) -> Result<CompiledModule, ModuleError> {
        self.modules
            .read()
            .unwrap()
            .get(id)
            .cloned()
            .ok_or_else(|| ModuleError::NotCompiled { id: id.clone() })
    }

    /// Get exports from a module
    pub fn get_exports(&self, id: &ModuleId) -> Result<ModuleExports, ModuleError> {
        let module = self.get_module(id)?;
        Ok(module.exports)
    }

    /// Get a specific named export from a module
    pub fn get_named_export(
        &self,
        id: &ModuleId,
        name: &str,
    ) -> Result<ExportedSymbol, ModuleError> {
        let exports = self.get_exports(id)?;
        exports
            .get_named(name)
            .cloned()
            .ok_or_else(|| ModuleError::ExportNotFound {
                module_id: id.clone(),
                export_name: name.to_string(),
            })
    }

    /// Check if a module exists in the registry
    pub fn contains(&self, id: &ModuleId) -> bool {
        self.modules.read().unwrap().contains_key(id)
    }

    /// Get all registered modules
    pub fn modules(&self) -> Vec<ModuleId> {
        self.modules.read().unwrap().keys().cloned().collect()
    }

    /// Get the status of a module
    pub fn get_status(&self, id: &ModuleId) -> Result<ModuleStatus, ModuleError> {
        let module = self.get_module(id)?;
        Ok(module.status)
    }

    /// Increment the type-check depth for a module (tracks lazy resolution recursion)
    pub fn increment_type_check_depth(&self, id: &ModuleId) -> Result<usize, ModuleError> {
        let mut depths = self.type_check_depth.write().unwrap();
        let new_depth = depths.get(id).copied().unwrap_or(0) + 1;
        depths.insert(id.clone(), new_depth);
        Ok(new_depth)
    }

    /// Decrement the type-check depth for a module
    pub fn decrement_type_check_depth(&self, id: &ModuleId) -> Result<(), ModuleError> {
        let mut depths = self.type_check_depth.write().unwrap();
        if let Some(depth) = depths.get_mut(id) {
            if *depth > 0 {
                *depth -= 1;
            }
        }
        Ok(())
    }

    /// Get the current type-check depth for a module
    pub fn get_type_check_depth(&self, id: &ModuleId) -> Result<usize, ModuleError> {
        let depths = self.type_check_depth.read().unwrap();
        Ok(depths.get(id).copied().unwrap_or(0))
    }

    /// Check if a module is ready for type-checking (all dependencies have exports available)
    pub fn is_ready_for_type_checking(&self, id: &ModuleId) -> Result<bool, ModuleError> {
        let module = self.get_module(id)?;
        // A module is ready if it exists but hasn't been fully type-checked yet
        // The caller is responsible for ensuring dependencies are checked first
        Ok(matches!(
            module.status,
            ModuleStatus::Parsed | ModuleStatus::ExportsExtracted
        ))
    }
}

impl Default for ModuleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use luanext_parser::ast::types::{PrimitiveType, Type, TypeKind};
    use luanext_parser::span::Span;
    use std::path::PathBuf;

    fn make_test_type() -> Type<'static> {
        Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        )
    }

    fn make_test_symbol(name: &str) -> Symbol<'static> {
        Symbol::new(
            name.to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        )
    }

    #[test]
    fn test_module_exports_named() {
        let mut exports = ModuleExports::new();
        let symbol = make_test_symbol("foo");
        exports.add_named("foo".to_string(), ExportedSymbol::new(symbol, false));

        assert!(exports.get_named("foo").is_some());
        assert!(exports.get_named("bar").is_none());
    }

    #[test]
    fn test_module_exports_default() {
        let mut exports = ModuleExports::new();
        let symbol = make_test_symbol("default");
        exports.set_default(ExportedSymbol::new(symbol, false));

        assert!(exports.has_default());
    }

    #[test]
    fn test_exported_symbol_is_runtime() {
        let runtime_symbol = ExportedSymbol::new(make_test_symbol("foo"), false);
        assert!(runtime_symbol.is_runtime());

        let type_only_symbol = ExportedSymbol::new(make_test_symbol("foo"), true);
        assert!(!type_only_symbol.is_runtime());

        let mut type_alias_symbol = make_test_symbol("Foo");
        type_alias_symbol.kind = SymbolKind::TypeAlias;
        let type_alias_export = ExportedSymbol::new(type_alias_symbol, false);
        assert!(!type_alias_export.is_runtime());
    }

    #[test]
    fn test_registry_register_and_get() {
        let registry = ModuleRegistry::new();
        let id = ModuleId::new(PathBuf::from("test.tl"));
        let symbol_table = Arc::new(SymbolTable::new());

        registry.register_parsed(id.clone(), symbol_table);

        let module = registry.get_module(&id).unwrap();
        assert_eq!(module.status, ModuleStatus::Parsed);
    }

    #[test]
    fn test_registry_exports_workflow() {
        let registry = ModuleRegistry::new();
        let id = ModuleId::new(PathBuf::from("test.tl"));
        let symbol_table = Arc::new(SymbolTable::new());

        // Register as parsed
        registry.register_parsed(id.clone(), symbol_table);
        assert_eq!(registry.get_status(&id).unwrap(), ModuleStatus::Parsed);

        // Add exports
        let mut exports = ModuleExports::new();
        exports.add_named(
            "foo".to_string(),
            ExportedSymbol::new(make_test_symbol("foo"), false),
        );
        registry.register_exports(&id, exports).unwrap();
        assert_eq!(
            registry.get_status(&id).unwrap(),
            ModuleStatus::ExportsExtracted
        );

        // Mark as checked
        registry.mark_checked(&id).unwrap();
        assert_eq!(registry.get_status(&id).unwrap(), ModuleStatus::TypeChecked);

        // Verify exports
        let named_export = registry.get_named_export(&id, "foo").unwrap();
        assert_eq!(named_export.symbol.name, "foo");
    }

    #[test]
    fn test_type_check_depth_tracking() {
        let registry = ModuleRegistry::new();
        let id = ModuleId::new(PathBuf::from("test.tl"));

        // Initial depth should be 0
        assert_eq!(registry.get_type_check_depth(&id).unwrap(), 0);

        // Increment depth
        let depth1 = registry.increment_type_check_depth(&id).unwrap();
        assert_eq!(depth1, 1);
        assert_eq!(registry.get_type_check_depth(&id).unwrap(), 1);

        // Increment again
        let depth2 = registry.increment_type_check_depth(&id).unwrap();
        assert_eq!(depth2, 2);
        assert_eq!(registry.get_type_check_depth(&id).unwrap(), 2);

        // Decrement depth
        registry.decrement_type_check_depth(&id).unwrap();
        assert_eq!(registry.get_type_check_depth(&id).unwrap(), 1);

        // Decrement again
        registry.decrement_type_check_depth(&id).unwrap();
        assert_eq!(registry.get_type_check_depth(&id).unwrap(), 0);
    }

    #[test]
    fn test_is_ready_for_type_checking() {
        let registry = ModuleRegistry::new();
        let id = ModuleId::new(PathBuf::from("test.tl"));
        let symbol_table = Arc::new(SymbolTable::new());

        // Register as parsed
        registry.register_parsed(id.clone(), symbol_table);
        assert!(registry.is_ready_for_type_checking(&id).unwrap());

        // Add exports
        let mut exports = ModuleExports::new();
        exports.add_named(
            "foo".to_string(),
            ExportedSymbol::new(make_test_symbol("foo"), false),
        );
        registry.register_exports(&id, exports).unwrap();
        assert!(registry.is_ready_for_type_checking(&id).unwrap());

        // Mark as checked
        registry.mark_checked(&id).unwrap();
        assert!(!registry.is_ready_for_type_checking(&id).unwrap());
    }
}
