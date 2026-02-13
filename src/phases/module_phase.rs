//! Module phase: Import/export resolution and module dependency tracking
//!
//! This phase handles:
//! - Extracting exports from a program (export declarations, export specifiers)
//! - Resolving import statements and registering imported symbols
//! - Tracking module dependencies for multi-module compilation
//!
//! **Design Pattern**: Stateless phase functions that take explicit context parameters
//! rather than encapsulating state. This allows flexibility in how the type checker
//! orchestrates phase execution.

use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_environment::TypeEnvironment;
use crate::module_resolver::{
    EdgeKind, ExportedSymbol, ModuleError, ModuleExports, ModuleId, ModuleRegistry, ModuleResolver,
    TypedDependency,
};
use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::visitors::{AccessControl, AccessControlVisitor, ClassMemberInfo, ClassMemberKind};
use crate::TypeCheckError;
use luanext_parser::ast::pattern::Pattern;
use luanext_parser::ast::statement::{ExportKind, ImportClause, ImportDeclaration, Statement};
use luanext_parser::ast::types::{ObjectTypeMember, PrimitiveType, Type, TypeKind};
use luanext_parser::ast::Program;
use luanext_parser::prelude::AccessModifier;
use luanext_parser::span::Span;
use luanext_parser::string_interner::StringInterner;
use std::sync::Arc;

/// Callback trait for lazy type-checking of dependencies during import resolution
///
/// When an import references a module that hasn't been type-checked yet,
/// the resolver can invoke this callback to trigger type-checking of that dependency
/// before attempting to resolve the import again.
pub trait LazyTypeCheckCallback: Send + Sync {
    /// Trigger type-checking of a dependency module
    fn type_check_dependency(&self, module_id: &ModuleId) -> Result<(), ModuleError>;
}

/// Convert a `Symbol<'arena>` to `Symbol<'static>` for cross-module storage.
///
/// # Safety
/// This is safe because:
/// 1. The arena that backs these types lives for the entire compilation session
/// 2. ModuleRegistry only reads these symbols, never writes back to them
/// 3. This is the standard pattern used by arena-based compilers (rustc uses a similar approach)
fn symbol_to_static<'arena>(symbol: Symbol<'arena>) -> Symbol<'static> {
    // SAFETY: The arena outlives the registry. Symbol layout is identical
    // regardless of lifetime parameter - the lifetime only constrains
    // the internal Type references which point into arena memory.
    unsafe { std::mem::transmute(symbol) }
}

/// Extract all exported symbols from a program.
///
/// This function analyzes export statements in the AST and builds a `ModuleExports`
/// structure containing all named and default exports. It handles:
///
/// - `export { foo, bar }` - Named exports of existing symbols
/// - `export const x = 1` - Inline export declarations
/// - `export default expr` - Default exports
/// - `export { foo } from './other'` - Re-exports from other modules
///
/// # Parameters
///
/// - `program`: The AST program to extract exports from
/// - `symbol_table`: Symbol table for looking up exported symbols
/// - `interner`: String interner for resolving identifier names
/// - `module_registry`: Optional registry for resolving re-exports (None if not using modules)
/// - `module_resolver`: Optional resolver for finding source modules (None if not using modules)
/// - `current_module_id`: Optional ID of the current module (None if not using modules)
/// - `lazy_callback`: Optional callback for lazy type-checking of dependencies
/// - `diagnostic_handler`: Handler for reporting errors
///
/// # Returns
///
/// A `ModuleExports` structure containing all exports found in the program.
#[allow(clippy::too_many_arguments)]
pub fn extract_exports<'arena>(
    program: &Program<'arena>,
    symbol_table: &SymbolTable<'arena>,
    interner: &StringInterner,
    module_registry: Option<&std::sync::Arc<crate::module_resolver::ModuleRegistry>>,
    module_resolver: Option<&std::sync::Arc<crate::module_resolver::ModuleResolver>>,
    current_module_id: Option<&crate::module_resolver::ModuleId>,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
) -> ModuleExports {
    let mut exports = ModuleExports::new();

    for stmt in program.statements.iter() {
        if let Statement::Export(export_decl) = stmt {
            match &export_decl.kind {
                ExportKind::Declaration(decl) => {
                    extract_declaration_export(decl, symbol_table, interner, &mut exports);
                }
                ExportKind::Named {
                    specifiers,
                    source,
                    is_type_only: export_is_type_only,
                } => {
                    for spec in specifiers.iter() {
                        let local_name = interner.resolve(spec.local.node);
                        let export_name = spec
                            .exported
                            .as_ref()
                            .map(|e| interner.resolve(e.node))
                            .unwrap_or_else(|| local_name.clone());

                        // Check if this is a re-export from another module
                        if let Some(source_path) = source {
                            let result = handle_reexport(
                                &local_name,
                                &export_name,
                                source_path,
                                *export_is_type_only,
                                export_decl.span,
                                module_registry,
                                module_resolver,
                                current_module_id,
                                lazy_callback,
                                diagnostic_handler,
                                &mut exports,
                            );

                            if let Err(e) = result {
                                diagnostic_handler.error(export_decl.span, &e.to_string());
                            }
                        } else {
                            // Local export - look up in symbol table
                            if let Some(symbol) = symbol_table.lookup(&local_name) {
                                // For local exports, the type-only flag from the export declaration
                                // takes precedence over the symbol kind
                                let is_type_only = if *export_is_type_only {
                                    true
                                } else {
                                    matches!(
                                        symbol.kind,
                                        SymbolKind::TypeAlias | SymbolKind::Interface
                                    )
                                };
                                exports.add_named(
                                    export_name,
                                    ExportedSymbol::new(
                                        symbol_to_static(symbol.clone()),
                                        is_type_only,
                                    ),
                                );
                            }
                        }
                    }
                }
                ExportKind::All {
                    source,
                    is_type_only,
                } => {
                    // export * from './module' - copy all exports from source module
                    let result = handle_export_all(
                        source,
                        *is_type_only,
                        current_module_id,
                        module_registry,
                        module_resolver,
                        export_decl.span,
                        lazy_callback,
                        diagnostic_handler,
                    );

                    match result {
                        Ok(source_exports) => {
                            // Add all exports from source module to our exports
                            for (export_name, exported_sym) in source_exports.named.iter() {
                                // Skip non-type exports if this is export type *
                                if *is_type_only && !exported_sym.is_type_only {
                                    continue;
                                }
                                exports.add_named(export_name.clone(), exported_sym.clone());
                            }
                        }
                        Err(e) => {
                            diagnostic_handler.error(export_decl.span, &e.to_string());
                        }
                    }
                }
                ExportKind::Default(_expr) => {
                    // For default exports, create a synthetic symbol
                    // Future: infer the type of the expression
                    let default_symbol = Symbol {
                        name: "default".to_string(),
                        typ: Type::new(
                            TypeKind::Primitive(PrimitiveType::Unknown),
                            export_decl.span,
                        ),
                        kind: SymbolKind::Variable,
                        span: export_decl.span,
                        is_exported: true,
                        references: Vec::new(),
                    };
                    exports
                        .set_default(ExportedSymbol::new(symbol_to_static(default_symbol), false));
                }
            }
        }
    }

    exports
}

/// Helper: Extract exports from an inline export declaration
fn extract_declaration_export<'arena>(
    decl: &Statement<'arena>,
    symbol_table: &SymbolTable<'arena>,
    interner: &StringInterner,
    exports: &mut ModuleExports,
) {
    match decl {
        Statement::Variable(var_decl) => {
            if let Pattern::Identifier(ident) = &var_decl.pattern {
                let ident_name = interner.resolve(ident.node);
                if let Some(symbol) = symbol_table.lookup(&ident_name) {
                    exports.add_named(
                        ident_name,
                        ExportedSymbol::new(symbol_to_static(symbol.clone()), false),
                    );
                }
            }
        }
        Statement::Function(func_decl) => {
            let func_name = interner.resolve(func_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&func_name) {
                exports.add_named(
                    func_name,
                    ExportedSymbol::new(symbol_to_static(symbol.clone()), false),
                );
            }
        }
        Statement::Class(class_decl) => {
            let class_name = interner.resolve(class_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&class_name) {
                exports.add_named(
                    class_name,
                    ExportedSymbol::new(symbol_to_static(symbol.clone()), false),
                );
            }
        }
        Statement::TypeAlias(type_alias) => {
            let alias_name = interner.resolve(type_alias.name.node);
            if let Some(symbol) = symbol_table.lookup(&alias_name) {
                exports.add_named(
                    alias_name,
                    ExportedSymbol::new(symbol_to_static(symbol.clone()), true),
                );
            }
        }
        Statement::Interface(interface_decl) => {
            let interface_name = interner.resolve(interface_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&interface_name) {
                exports.add_named(
                    interface_name,
                    ExportedSymbol::new(symbol_to_static(symbol.clone()), true),
                );
            }
        }
        Statement::Enum(enum_decl) => {
            let enum_name = interner.resolve(enum_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&enum_name) {
                exports.add_named(
                    enum_name,
                    ExportedSymbol::new(symbol_to_static(symbol.clone()), false),
                );
            }
        }
        _ => {}
    }
}

/// Helper: Handle re-exports from another module
///
/// Resolves a re-exported symbol and adds it to the module's exports.
/// Uses `resolve_re_export()` for robust chain resolution with error handling.
#[allow(clippy::too_many_arguments)]
fn handle_reexport(
    local_name: &str,
    export_name: &str,
    source_path: &str,
    is_type_only_export: bool,
    span: Span,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    current_module_id: Option<&ModuleId>,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
    exports: &mut ModuleExports,
) -> Result<(), ModuleError> {
    if let (Some(registry), Some(resolver), Some(current_id)) =
        (module_registry, module_resolver, current_module_id)
    {
        let mut visited = std::collections::HashSet::new();
        let exported_sym = resolve_re_export(
            source_path,
            local_name,
            span,
            registry,
            resolver,
            current_id,
            lazy_callback,
            is_type_only_export,
            diagnostic_handler,
            &mut visited,
        )?;

        exports.add_named(export_name.to_string(), exported_sym);
        Ok(())
    } else {
        // Module resolution not configured - can't resolve re-export
        Err(ModuleError::NotFound {
            source: source_path.to_string(),
            searched_paths: Vec::new(),
        })
    }
}

/// Helper: Handle export all from another module
///
/// Resolves all exports from a source module and returns them.
/// Used for `export * from './module'` and `export type * from './module'`.
#[allow(clippy::too_many_arguments)]
fn handle_export_all(
    source_path: &str,
    is_type_only_export: bool,
    current_module_id: Option<&ModuleId>,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    _span: Span,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    _diagnostic_handler: &Arc<dyn DiagnosticHandler>,
) -> Result<ModuleExports, ModuleError> {
    if let (Some(registry), Some(resolver), Some(current_id)) =
        (module_registry, module_resolver, current_module_id)
    {
        // Resolve source module path to module ID
        let source_module_id = resolver.resolve(source_path, current_id.path())?;

        // Get or lazily type-check source module
        let source_exports = match registry.get_exports(&source_module_id) {
            Ok(exports) => exports.clone(),
            Err(_) => {
                if let Some(callback) = lazy_callback {
                    callback.type_check_dependency(&source_module_id)?;
                    registry.get_exports(&source_module_id)?.clone()
                } else {
                    return Err(ModuleError::NotCompiled {
                        id: source_module_id,
                    });
                }
            }
        };

        // Filter exports based on type-only flag
        let mut result = ModuleExports::new();
        for (name, exported_sym) in source_exports.named.iter() {
            // Skip non-type exports if this is export type *
            if is_type_only_export && !exported_sym.is_type_only {
                continue;
            }
            result.add_named(name.clone(), exported_sym.clone());
        }

        Ok(result)
    } else {
        // Module resolution not configured - can't resolve export all
        Err(ModuleError::NotFound {
            source: source_path.to_string(),
            searched_paths: Vec::new(),
        })
    }
}

/// Process an import statement and register imported symbols.
///
/// This function handles all import clause types:
/// - Default imports: `import foo from './module'`
/// - Named imports: `import { foo, bar } from './module'`
/// - Type-only imports: `import type { Foo } from './module'`
/// - Namespace imports: `import * as foo from './module'`
/// - Mixed imports: `import foo, { bar } from './module'`
///
/// For type-only imports, symbols are registered in both the symbol table and type environment,
/// and if the imported type is an interface/object, its members are registered in access control.
///
/// # Parameters
///
/// - `import`: The import declaration AST node
/// - `symbol_table`: Mutable symbol table for declaring imported symbols
/// - `type_env`: Mutable type environment for type-only imports
/// - `access_control`: Mutable access control for interface/object member registration
/// - `interner`: String interner for resolving names
/// - `module_dependencies`: Vector to track import dependencies
/// - `module_registry`, `module_resolver`, `current_module_id`: Optional module resolution components
/// - `lazy_callback`: Optional callback for lazy type-checking of uncompiled dependencies
/// - `diagnostic_handler`: For reporting import resolution errors
#[allow(clippy::too_many_arguments)]
pub fn check_import_statement<'arena>(
    import: &ImportDeclaration<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    access_control: &mut AccessControl,
    interner: &StringInterner,
    module_dependencies: &mut Vec<TypedDependency>,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    current_module_id: Option<&ModuleId>,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
) -> Result<(), TypeCheckError> {
    match &import.clause {
        ImportClause::Default(name) => {
            let name_str = interner.resolve(name.node);
            let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
            let symbol = Symbol::new(
                name_str.to_string(),
                SymbolKind::Variable,
                any_type,
                import.span,
            );
            symbol_table
                .declare(symbol)
                .map_err(|e| TypeCheckError::new(e, import.span))?;
        }
        ImportClause::Named(specifiers) => {
            for spec in specifiers.iter() {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
                    lazy_callback,
                    false, // Not a type-only import
                    diagnostic_handler,
                )?;

                let symbol = Symbol::new(
                    name_str.to_string(),
                    SymbolKind::Variable,
                    import_type,
                    spec.span,
                );
                symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, spec.span))?;
            }
        }
        ImportClause::TypeOnly(specifiers) => {
            for spec in specifiers.iter() {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
                    lazy_callback,
                    true, // This is a type-only import
                    diagnostic_handler,
                )?;

                // Register in symbol table
                let symbol = Symbol::new(
                    name_str.to_string(),
                    SymbolKind::TypeAlias,
                    import_type.clone(),
                    spec.span,
                );
                symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, spec.span))?;

                // Also register in type_env
                type_env
                    .register_type_alias(name_str.to_string(), import_type.clone())
                    .map_err(|e| TypeCheckError::new(e, spec.span))?;

                // Register in access control if it's an object type
                if let TypeKind::Object(obj_type) = &import_type.kind {
                    access_control.register_class(&name_str, None);
                    for member in obj_type.members.iter() {
                        let member_info = match member {
                            ObjectTypeMember::Property(prop) => ClassMemberInfo {
                                name: interner.resolve(prop.name.node).to_string(),
                                access: AccessModifier::Public,
                                _is_static: false,
                                kind: ClassMemberKind::Property {
                                    type_annotation: prop.type_annotation.clone(),
                                },
                                is_final: prop.is_readonly,
                            },
                            ObjectTypeMember::Method(method) => ClassMemberInfo {
                                name: interner.resolve(method.name.node).to_string(),
                                access: AccessModifier::Public,
                                _is_static: false,
                                kind: ClassMemberKind::Method {
                                    parameters: method.parameters.to_vec(),
                                    return_type: Some(method.return_type.clone()),
                                    is_abstract: false,
                                },
                                is_final: false,
                            },
                            ObjectTypeMember::Index(_) => continue,
                        };
                        access_control.register_member(&name_str, member_info);
                    }
                }
            }
        }
        ImportClause::Namespace(name) => {
            let name_str = interner.resolve(name.node);
            let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
            let symbol = Symbol::new(
                name_str.to_string(),
                SymbolKind::Variable,
                any_type,
                import.span,
            );
            symbol_table
                .declare(symbol)
                .map_err(|e| TypeCheckError::new(e, import.span))?;
        }
        ImportClause::Mixed { default, named } => {
            // Handle default import
            let default_name_str = interner.resolve(default.node);
            let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
            let default_symbol = Symbol::new(
                default_name_str.to_string(),
                SymbolKind::Variable,
                any_type,
                default.span,
            );
            symbol_table
                .declare(default_symbol)
                .map_err(|e| TypeCheckError::new(e, default.span))?;

            // Handle named imports
            for spec in named.iter() {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
                    lazy_callback,
                    false, // Not a type-only import
                    diagnostic_handler,
                )?;

                let symbol = Symbol::new(
                    name_str.to_string(),
                    SymbolKind::Variable,
                    import_type,
                    spec.span,
                );
                symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, spec.span))?;
            }
        }
    }
    Ok(())
}

/// Maximum recursion depth for lazy type-checking (prevents infinite loops)
const MAX_LAZY_DEPTH: usize = 10;

/// Resolve the type of an imported symbol from a source module.
///
/// This function attempts to resolve the type of a symbol being imported from another module.
/// If module resolution is configured and the source module is found, it looks up the symbol
/// in the module's exports and returns its type.
///
/// If the module hasn't been type-checked yet but exports are available, returns those.
/// If exports are not available and a lazy callback is provided, attempts lazy type-checking
/// before failing with a proper error.
///
/// Module dependencies are tracked by adding the resolved source module path to the dependencies vector.
#[allow(clippy::too_many_arguments)]
fn resolve_import_type<'arena>(
    source: &str,
    symbol_name: &str,
    span: Span,
    module_dependencies: &mut Vec<TypedDependency>,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    current_module_id: Option<&ModuleId>,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    is_type_only_import: bool,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
) -> Result<Type<'arena>, TypeCheckError> {
    if let (Some(registry), Some(resolver), Some(current_id)) =
        (module_registry, module_resolver, current_module_id)
    {
        match resolver.resolve(source, current_id.path()) {
            Ok(source_module_id) => {
                // Track dependency with edge kind
                let edge_kind = if is_type_only_import {
                    EdgeKind::TypeOnly
                } else {
                    EdgeKind::Value
                };
                module_dependencies.push(TypedDependency::new(
                    source_module_id.path().to_path_buf(),
                    edge_kind,
                ));

                // Try to get exports
                match registry.get_exports(&source_module_id) {
                    Ok(source_exports) => {
                        if let Some(exported_sym) = source_exports.get_named(symbol_name) {
                            // Validation: ensure runtime imports don't use type-only exports
                            validate_import_export_compatibility(
                                exported_sym,
                                is_type_only_import,
                                symbol_name,
                                &source_module_id,
                                span,
                            )?;
                            Ok(exported_sym.symbol.typ.clone())
                        } else {
                            // Export doesn't exist
                            let error = ModuleError::ExportNotFound {
                                module_id: source_module_id.clone(),
                                export_name: symbol_name.to_string(),
                            };
                            Err(TypeCheckError::new(error.to_string(), span))
                        }
                    }
                    Err(ModuleError::NotCompiled { id }) => {
                        // Module exists but not compiled yet - attempt lazy type-checking
                        if let Some(callback) = lazy_callback {
                            // Check recursion depth to prevent infinite loops
                            let current_depth = registry.get_type_check_depth(&id).unwrap_or(0);
                            if current_depth > MAX_LAZY_DEPTH {
                                let error = ModuleError::TypeCheckInProgress {
                                    module: id.clone(),
                                    depth: current_depth,
                                    max_depth: MAX_LAZY_DEPTH,
                                };
                                Err(TypeCheckError::new(error.to_string(), span))?;
                            }

                            // Increment depth for this module
                            let _ = registry.increment_type_check_depth(&id);

                            // Trigger type-checking via callback
                            let check_result = callback.type_check_dependency(&id);

                            // Decrement depth
                            let _ = registry.decrement_type_check_depth(&id);

                            // If type-checking failed, propagate error
                            check_result.map_err(|e| TypeCheckError::new(e.to_string(), span))?;

                            // Retry export lookup after type-checking
                            match registry.get_exports(&source_module_id) {
                                Ok(source_exports) => {
                                    if let Some(exported_sym) =
                                        source_exports.get_named(symbol_name)
                                    {
                                        // Validation: ensure runtime imports don't use type-only exports
                                        validate_import_export_compatibility(
                                            exported_sym,
                                            is_type_only_import,
                                            symbol_name,
                                            &source_module_id,
                                            span,
                                        )?;
                                        Ok(exported_sym.symbol.typ.clone())
                                    } else {
                                        let error = ModuleError::ExportNotFound {
                                            module_id: source_module_id.clone(),
                                            export_name: symbol_name.to_string(),
                                        };
                                        Err(TypeCheckError::new(error.to_string(), span))
                                    }
                                }
                                Err(e) => Err(TypeCheckError::new(e.to_string(), span)),
                            }
                        } else if is_type_only_import {
                            // Type-only import of uncompiled module: this happens in circular
                            // type-only dependency cycles. Since type-only imports have no runtime
                            // effect, we return Unknown to allow compilation to proceed.
                            // The imported type will be treated as opaque.
                            Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
                        } else {
                            // No callback provided - fail with proper error
                            let error = ModuleError::NotCompiled { id };
                            Err(TypeCheckError::new(error.to_string(), span))
                        }
                    }
                    Err(e) => {
                        // Other errors
                        Err(TypeCheckError::new(e.to_string(), span))
                    }
                }
            }
            Err(e) => {
                diagnostic_handler.error(
                    span,
                    &format!("Failed to resolve module '{}': {}", source, e),
                );
                let error = ModuleError::InvalidPath {
                    source: source.to_string(),
                    reason: e.to_string(),
                };
                Err(TypeCheckError::new(error.to_string(), span))
            }
        }
    } else {
        diagnostic_handler.error(
            span,
            &format!(
                "Module '{}' not found (module resolution not configured)",
                source
            ),
        );
        let error = ModuleError::NotFound {
            source: source.to_string(),
            searched_paths: Vec::new(),
        };
        Err(TypeCheckError::new(error.to_string(), span))
    }
}

/// Resolve a re-exported symbol through potentially multiple re-export chains.
///
/// Returns the original `ExportedSymbol` after following the chain to its source.
/// This function handles:
/// - Resolving re-export source modules
/// - Detecting circular re-export chains
/// - Enforcing maximum depth limits for performance
/// - Validating type-only export consistency
/// - Lazy type-checking of uncompiled dependencies
///
/// # Parameters
///
/// - `source_path`: The module path being re-exported from
/// - `symbol_name`: The name of the symbol in the source module
/// - `span`: Source location for error reporting
/// - `module_registry`: Registry of compiled modules
/// - `module_resolver`: Module path resolver
/// - `current_module_id`: The module doing the re-export
/// - `lazy_callback`: Optional callback for lazy type-checking
/// - `is_type_only_export`: Whether this is a type-only re-export
/// - `diagnostic_handler`: For error reporting
/// - `visited`: Set of visited modules for cycle detection
///
/// # Returns
///
/// The `ExportedSymbol` from the original definition, or error if resolution fails
#[allow(clippy::too_many_arguments)]
fn resolve_re_export(
    source_path: &str,
    symbol_name: &str,
    _span: Span,
    module_registry: &Arc<ModuleRegistry>,
    module_resolver: &Arc<ModuleResolver>,
    current_module_id: &ModuleId,
    lazy_callback: Option<&dyn LazyTypeCheckCallback>,
    is_type_only_export: bool,
    _diagnostic_handler: &Arc<dyn DiagnosticHandler>,
    visited: &mut std::collections::HashSet<ModuleId>,
) -> Result<ExportedSymbol, ModuleError> {
    const MAX_REEXPORT_DEPTH: usize = 10;

    // 1. Resolve source module path
    let source_module_id = module_resolver.resolve(source_path, current_module_id.path())?;

    // 2. Check for circular re-exports
    if visited.len() >= MAX_REEXPORT_DEPTH {
        return Err(ModuleError::ReExportChainTooDeep {
            symbol_name: symbol_name.to_string(),
            depth: visited.len(),
            max_depth: MAX_REEXPORT_DEPTH,
        });
    }

    if !visited.insert(source_module_id.clone()) {
        // We've already visited this module - circular dependency
        let mut chain: Vec<_> = visited.iter().cloned().collect();
        chain.push(source_module_id.clone());
        return Err(ModuleError::CircularReExport {
            chain,
            symbol_name: symbol_name.to_string(),
        });
    }

    // 3. Try to get exports, with lazy resolution if needed
    let source_exports = match module_registry.get_exports(&source_module_id) {
        Ok(exports) => exports,
        Err(ModuleError::NotCompiled { id }) => {
            // Module exists but not compiled yet - attempt lazy type-checking
            if let Some(callback) = lazy_callback {
                let current_depth = module_registry.get_type_check_depth(&id).unwrap_or(0);
                if current_depth > MAX_LAZY_DEPTH {
                    return Err(ModuleError::TypeCheckInProgress {
                        module: id.clone(),
                        depth: current_depth,
                        max_depth: MAX_LAZY_DEPTH,
                    });
                }

                let _ = module_registry.increment_type_check_depth(&id);
                let check_result = callback.type_check_dependency(&id);
                let _ = module_registry.decrement_type_check_depth(&id);

                check_result?;

                // Retry export lookup after type-checking
                module_registry.get_exports(&source_module_id)?
            } else if is_type_only_export {
                // Type-only re-export of uncompiled module: create a synthetic
                // type-only export with Unknown type for circular type deps
                let synthetic_symbol = Symbol {
                    name: symbol_name.to_string(),
                    typ: Type::new(
                        TypeKind::Primitive(PrimitiveType::Unknown),
                        Span::new(0, 0, 0, 0),
                    ),
                    kind: SymbolKind::TypeAlias,
                    span: Span::new(0, 0, 0, 0),
                    is_exported: true,
                    references: Vec::new(),
                };
                return Ok(ExportedSymbol::new(
                    symbol_to_static(synthetic_symbol),
                    true,
                ));
            } else {
                return Err(ModuleError::NotCompiled { id });
            }
        }
        Err(e) => return Err(e),
    };

    // 4. Look up the symbol in exports
    match source_exports.get_named(symbol_name) {
        Some(exported_sym) => {
            // 5. Preserve type-only nature: if the source is type-only, the
            // re-export is also type-only regardless of the export syntax.
            // This allows `export { User } from './types'` to work when User
            // is an interface (type-only). The re-exported symbol inherits
            // the type-only flag from the original.
            let mut result_sym = exported_sym.clone();
            if is_type_only_export {
                result_sym.is_type_only = true;
            }

            Ok(result_sym)
        }
        None => Err(ModuleError::ExportNotFound {
            module_id: source_module_id.clone(),
            export_name: symbol_name.to_string(),
        }),
    }
}

/// Validate import/export compatibility before returning the type.
///
/// Performs the following checks:
/// 1. Runtime imports cannot reference type-only exports
/// 2. Type-only imports can reference any export
///
/// # Parameters
///
/// - `exported_sym`: The symbol being exported
/// - `is_type_only_import`: Whether this is a `import type` (type-only) or regular import
/// - `symbol_name`: Name of the symbol for error reporting
/// - `module_id`: ID of the source module for error reporting
/// - `span`: Source span for error reporting
///
/// # Returns
///
/// Ok(()) if validation passes, Err(TypeCheckError) if validation fails
fn validate_import_export_compatibility(
    exported_sym: &ExportedSymbol,
    is_type_only_import: bool,
    symbol_name: &str,
    module_id: &ModuleId,
    span: Span,
) -> Result<(), TypeCheckError> {
    // Runtime imports cannot reference type-only exports
    if !is_type_only_import && exported_sym.is_type_only {
        let error = ModuleError::RuntimeImportOfTypeOnly {
            module_id: module_id.clone(),
            export_name: symbol_name.to_string(),
        };
        Err(TypeCheckError::new(error.to_string(), span))
    } else {
        Ok(())
    }
}

/// Apply type arguments to an imported generic type.
///
/// When importing a generic type with type arguments (e.g., `import { List<string> } from './mod'`),
/// this function instantiates the generic type with the provided arguments.
///
/// # Parameters
///
/// - `arena`: Arena allocator for creating new types
/// - `base_type`: The type of the imported symbol
/// - `type_arguments`: Optional type arguments from the import statement
/// - `symbol_name`: Name of the symbol for error reporting
/// - `span`: Source span for error reporting
///
/// # Returns
///
/// The instantiated type with type arguments applied, or base_type if no arguments provided
#[allow(dead_code)] // Placeholder for future full generic support across modules
fn apply_type_arguments<'arena>(
    _arena: &'arena bumpalo::Bump,
    base_type: &Type<'arena>,
    type_arguments: Option<&[Type<'arena>]>,
    symbol_name: &str,
    span: Span,
) -> Result<Type<'arena>, TypeCheckError> {
    match type_arguments {
        None => Ok(base_type.clone()),
        Some(args) => {
            // For now, we don't have the type parameters from the exported symbol,
            // so we can only validate that the type supports generics.
            // Full generic instantiation would require tracking TypeParameter info
            // in the exported symbols, which is a future enhancement.

            if args.is_empty() {
                Ok(base_type.clone())
            } else {
                // Generic types are not yet fully supported across module boundaries
                // This is a placeholder for future implementation
                Err(TypeCheckError::new(
                    format!("Generic type arguments on cross-module imports are not yet supported for '{}'", symbol_name),
                    span,
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::diagnostics::CollectingDiagnosticHandler;
    use std::sync::Arc;

    #[test]
    fn test_extract_exports_empty() {
        let program = luanext_parser::ast::Program {
            statements: &[],
            span: Span::new(0, 0, 0, 0),
            statement_ranges: None,
        };
        let interner = luanext_parser::string_interner::StringInterner::new();
        let symbol_table = crate::utils::symbol_table::SymbolTable::new();
        let handler: Arc<dyn DiagnosticHandler> =
            Arc::new(crate::cli::diagnostics::CollectingDiagnosticHandler::new());
        let result = extract_exports(
            &program,
            &symbol_table,
            &interner,
            None,
            None,
            None,
            None,
            &handler,
        );
        assert!(result.named.is_empty());
        assert!(result.default.is_none());
    }

    #[test]
    fn test_extract_exports_with_variable() {
        let span = Span::new(0, 10, 0, 10);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let mut symbol_table = crate::utils::symbol_table::SymbolTable::new();

        let name_id = interner.intern("myVar");
        let symbol = crate::utils::symbol_table::Symbol::new(
            "myVar".to_string(),
            crate::utils::symbol_table::SymbolKind::Variable,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
            span,
        );
        symbol_table.declare(symbol).unwrap();

        let program = luanext_parser::ast::Program {
            statements: &[],
            span,
            statement_ranges: None,
        };

        let handler: Arc<dyn DiagnosticHandler> =
            Arc::new(crate::cli::diagnostics::CollectingDiagnosticHandler::new());
        let result = extract_exports(
            &program,
            &symbol_table,
            &interner,
            None,
            None,
            None,
            None,
            &handler,
        );
        assert!(result.named.is_empty());
    }

    #[test]
    fn test_check_import_statement_default() {
        let span = Span::new(0, 10, 0, 10);
        let handler: Arc<dyn DiagnosticHandler> = Arc::new(CollectingDiagnosticHandler::new());
        let mut symbol_table = crate::utils::symbol_table::SymbolTable::new();
        let mut type_env = crate::core::type_environment::TypeEnvironment::new();
        let mut access_control = crate::visitors::AccessControl::new();
        let interner = luanext_parser::string_interner::StringInterner::new();
        let mut module_dependencies: Vec<TypedDependency> = Vec::new();

        let name_id = interner.intern("MyModule");
        let import = luanext_parser::ast::statement::ImportDeclaration {
            clause: luanext_parser::ast::statement::ImportClause::Default(
                luanext_parser::ast::Spanned::new(name_id, span),
            ),
            source: "./my_module.lua".to_string(),
            span,
        };

        let result = check_import_statement(
            &import,
            &mut symbol_table,
            &mut type_env,
            &mut access_control,
            &interner,
            &mut module_dependencies,
            None,
            None,
            None,
            None,
            &handler,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_resolve_import_type_no_resolver() {
        let span = Span::new(0, 10, 0, 10);
        let handler: Arc<dyn DiagnosticHandler> = Arc::new(CollectingDiagnosticHandler::new());
        let mut module_dependencies: Vec<TypedDependency> = Vec::new();

        let result = resolve_import_type(
            "./unknown.lua",
            "SomeType",
            span,
            &mut module_dependencies,
            None,
            None,
            None,
            None,
            false, // Not a type-only import
            &handler,
        );
        // Should return error when no resolver configured
        assert!(result.is_err());
    }

    #[test]
    fn test_check_import_statement_named() {
        let arena = bumpalo::Bump::new();
        let span = Span::new(0, 10, 0, 10);
        let handler: Arc<dyn DiagnosticHandler> = Arc::new(CollectingDiagnosticHandler::new());
        let mut symbol_table = crate::utils::symbol_table::SymbolTable::new();
        let mut type_env = crate::core::type_environment::TypeEnvironment::new();
        let mut access_control = crate::visitors::AccessControl::new();
        let interner = luanext_parser::string_interner::StringInterner::new();
        let mut module_dependencies: Vec<TypedDependency> = Vec::new();

        let import = luanext_parser::ast::statement::ImportDeclaration {
            clause: luanext_parser::ast::statement::ImportClause::Named(
                arena.alloc_slice_fill_iter([luanext_parser::ast::statement::ImportSpecifier {
                    imported: luanext_parser::ast::Spanned::new(interner.intern("foo"), span),
                    local: Some(luanext_parser::ast::Spanned::new(
                        interner.intern("foo"),
                        span,
                    )),
                    span,
                }]),
            ),
            source: "./my_module.lua".to_string(),
            span,
        };

        let result = check_import_statement(
            &import,
            &mut symbol_table,
            &mut type_env,
            &mut access_control,
            &interner,
            &mut module_dependencies,
            None,
            None,
            None,
            None,
            &handler,
        );
        // Should fail because no module registry/resolver and no lazy callback
        assert!(result.is_err());
    }

    #[test]
    fn test_check_import_statement_namespace() {
        let span = Span::new(0, 10, 0, 10);
        let handler: Arc<dyn DiagnosticHandler> = Arc::new(CollectingDiagnosticHandler::new());
        let mut symbol_table = crate::utils::symbol_table::SymbolTable::new();
        let mut type_env = crate::core::type_environment::TypeEnvironment::new();
        let mut access_control = crate::visitors::AccessControl::new();
        let interner = luanext_parser::string_interner::StringInterner::new();
        let mut module_dependencies: Vec<TypedDependency> = Vec::new();

        let import = luanext_parser::ast::statement::ImportDeclaration {
            clause: luanext_parser::ast::statement::ImportClause::Namespace(
                luanext_parser::ast::Spanned::new(interner.intern("mylib"), span),
            ),
            source: "./my_module.lua".to_string(),
            span,
        };

        let result = check_import_statement(
            &import,
            &mut symbol_table,
            &mut type_env,
            &mut access_control,
            &interner,
            &mut module_dependencies,
            None,
            None,
            None,
            None,
            &handler,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_extract_declaration_export_function() {
        let span = Span::new(0, 10, 0, 10);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let mut symbol_table = crate::utils::symbol_table::SymbolTable::new();

        let func_name_id = interner.intern("myFunc");
        let symbol = crate::utils::symbol_table::Symbol::new(
            "myFunc".to_string(),
            crate::utils::symbol_table::SymbolKind::Function,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
            span,
        );
        symbol_table.declare(symbol).unwrap();

        let program = luanext_parser::ast::Program {
            statements: &[],
            span,
            statement_ranges: None,
        };

        let handler: Arc<dyn DiagnosticHandler> =
            Arc::new(crate::cli::diagnostics::CollectingDiagnosticHandler::new());
        let result = extract_exports(
            &program,
            &symbol_table,
            &interner,
            None,
            None,
            None,
            None,
            &handler,
        );
        assert!(result.named.is_empty());
    }

    #[test]
    fn test_validate_type_only_export_runtime_import() {
        let span = Span::new(0, 10, 0, 10);
        let module_id =
            crate::module_resolver::ModuleId::new(std::path::PathBuf::from("module.tl"));

        // Create a type-only export
        let type_only_symbol = crate::utils::symbol_table::Symbol::new(
            "MyType".to_string(),
            crate::utils::symbol_table::SymbolKind::TypeAlias,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
            span,
        );
        let exported_sym = ExportedSymbol::new(type_only_symbol, true); // is_type_only=true

        // Try to import as runtime (is_type_only_import=false) - should fail
        let result = validate_import_export_compatibility(
            &exported_sym,
            false, // Runtime import
            "MyType",
            &module_id,
            span,
        );
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Cannot import type-only"));
    }

    #[test]
    fn test_validate_type_only_export_type_import() {
        let span = Span::new(0, 10, 0, 10);
        let module_id =
            crate::module_resolver::ModuleId::new(std::path::PathBuf::from("module.tl"));

        // Create a type-only export
        let type_only_symbol = crate::utils::symbol_table::Symbol::new(
            "MyType".to_string(),
            crate::utils::symbol_table::SymbolKind::TypeAlias,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
            span,
        );
        let exported_sym = ExportedSymbol::new(type_only_symbol, true); // is_type_only=true

        // Import as type-only (is_type_only_import=true) - should pass
        let result = validate_import_export_compatibility(
            &exported_sym,
            true, // Type-only import
            "MyType",
            &module_id,
            span,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_runtime_export_runtime_import() {
        let span = Span::new(0, 10, 0, 10);
        let module_id =
            crate::module_resolver::ModuleId::new(std::path::PathBuf::from("module.tl"));

        // Create a runtime export (not type-only)
        let runtime_symbol = crate::utils::symbol_table::Symbol::new(
            "myVar".to_string(),
            crate::utils::symbol_table::SymbolKind::Variable,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
            span,
        );
        let exported_sym = ExportedSymbol::new(runtime_symbol, false); // is_type_only=false

        // Import as runtime - should pass
        let result = validate_import_export_compatibility(
            &exported_sym,
            false, // Runtime import
            "myVar",
            &module_id,
            span,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_apply_type_arguments_no_args() {
        let arena = bumpalo::Bump::new();
        let span = Span::new(0, 10, 0, 10);
        let base_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Apply no type arguments - should return base type unchanged
        let result = apply_type_arguments(&arena, &base_type, None, "MyType", span);
        assert!(result.is_ok());
        assert!(matches!(
            result.unwrap().kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_apply_type_arguments_empty_args() {
        let arena = bumpalo::Bump::new();
        let span = Span::new(0, 10, 0, 10);
        let base_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Apply empty type arguments slice - should return base type unchanged
        let result = apply_type_arguments(&arena, &base_type, Some(&[]), "MyType", span);
        assert!(result.is_ok());
        assert!(matches!(
            result.unwrap().kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_apply_type_arguments_with_args_not_supported() {
        let arena = bumpalo::Bump::new();
        let span = Span::new(0, 10, 0, 10);
        let base_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let arg_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        // Apply type arguments to generic - should fail (not yet supported)
        let result = apply_type_arguments(&arena, &base_type, Some(&[arg_type]), "List", span);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("not yet supported"));
    }
}
