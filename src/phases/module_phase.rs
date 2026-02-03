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

use crate::diagnostics::DiagnosticHandler;
use crate::module_resolver::{ExportedSymbol, ModuleExports, ModuleId, ModuleRegistry, ModuleResolver};
use crate::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::type_environment::TypeEnvironment;
use crate::visitors::{AccessControl, AccessControlVisitor, ClassMemberInfo, ClassMemberKind};
use crate::TypeCheckError;
use std::path::PathBuf;
use std::sync::Arc;
use typedlua_parser::ast::pattern::Pattern;
use typedlua_parser::ast::statement::{ExportKind, ImportClause, ImportDeclaration, Statement};
use typedlua_parser::ast::types::{ObjectTypeMember, PrimitiveType, Type, TypeKind};
use typedlua_parser::ast::Program;
use typedlua_parser::prelude::AccessModifier;
use typedlua_parser::span::Span;
use typedlua_parser::string_interner::StringInterner;

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
///
/// # Returns
///
/// A `ModuleExports` structure containing all exports found in the program.
pub fn extract_exports(
    program: &Program,
    symbol_table: &SymbolTable,
    interner: &StringInterner,
    module_registry: Option<&std::sync::Arc<crate::module_resolver::ModuleRegistry>>,
    module_resolver: Option<&std::sync::Arc<crate::module_resolver::ModuleResolver>>,
    current_module_id: Option<&crate::module_resolver::ModuleId>,
) -> ModuleExports {
    let mut exports = ModuleExports::new();

    for stmt in program.statements.iter() {
        if let Statement::Export(export_decl) = stmt {
            match &export_decl.kind {
                ExportKind::Declaration(decl) => {
                    extract_declaration_export(
                        &**decl,
                        symbol_table,
                        interner,
                        &mut exports,
                    );
                }
                ExportKind::Named { specifiers, source } => {
                    for spec in specifiers {
                        let local_name = interner.resolve(spec.local.node);
                        let export_name = spec
                            .exported
                            .as_ref()
                            .map(|e| interner.resolve(e.node))
                            .unwrap_or_else(|| local_name.clone());

                        // Check if this is a re-export from another module
                        if let Some(source_path) = source {
                            handle_reexport(
                                &local_name,
                                &export_name,
                                source_path,
                                module_registry,
                                module_resolver,
                                current_module_id,
                                &mut exports,
                            );
                        } else {
                            // Local export - look up in symbol table
                            if let Some(symbol) = symbol_table.lookup(&local_name) {
                                let is_type_only = matches!(
                                    symbol.kind,
                                    SymbolKind::TypeAlias | SymbolKind::Interface
                                );
                                exports.add_named(
                                    export_name,
                                    ExportedSymbol::new(symbol.clone(), is_type_only),
                                );
                            }
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
                    exports.set_default(ExportedSymbol::new(default_symbol, false));
                }
            }
        }
    }

    exports
}

/// Helper: Extract exports from an inline export declaration
fn extract_declaration_export(
    decl: &Statement,
    symbol_table: &SymbolTable,
    interner: &StringInterner,
    exports: &mut ModuleExports,
) {
    match decl {
        Statement::Variable(var_decl) => {
            if let Pattern::Identifier(ident) = &var_decl.pattern {
                let ident_name = interner.resolve(ident.node);
                if let Some(symbol) = symbol_table.lookup(&ident_name) {
                    exports.add_named(ident_name, ExportedSymbol::new(symbol.clone(), false));
                }
            }
        }
        Statement::Function(func_decl) => {
            let func_name = interner.resolve(func_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&func_name) {
                exports.add_named(func_name, ExportedSymbol::new(symbol.clone(), false));
            }
        }
        Statement::Class(class_decl) => {
            let class_name = interner.resolve(class_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&class_name) {
                exports.add_named(class_name, ExportedSymbol::new(symbol.clone(), false));
            }
        }
        Statement::TypeAlias(type_alias) => {
            let alias_name = interner.resolve(type_alias.name.node);
            if let Some(symbol) = symbol_table.lookup(&alias_name) {
                exports.add_named(alias_name, ExportedSymbol::new(symbol.clone(), true));
            }
        }
        Statement::Interface(interface_decl) => {
            let interface_name = interner.resolve(interface_decl.name.node);
            if let Some(symbol) = symbol_table.lookup(&interface_name) {
                exports.add_named(interface_name, ExportedSymbol::new(symbol.clone(), true));
            }
        }
        _ => {}
    }
}

/// Helper: Handle re-exports from another module
#[allow(clippy::too_many_arguments)]
fn handle_reexport(
    local_name: &str,
    export_name: &str,
    source_path: &str,
    module_registry: Option<&std::sync::Arc<crate::module_resolver::ModuleRegistry>>,
    module_resolver: Option<&std::sync::Arc<crate::module_resolver::ModuleResolver>>,
    current_module_id: Option<&crate::module_resolver::ModuleId>,
    exports: &mut ModuleExports,
) {
    if let (Some(registry), Some(resolver), Some(current_id)) =
        (module_registry, module_resolver, current_module_id)
    {
        if let Ok(source_module_id) = resolver.resolve(source_path, current_id.path()) {
            if let Ok(source_exports) = registry.get_exports(&source_module_id) {
                if let Some(exported_sym) = source_exports.get_named(local_name) {
                    exports.add_named(export_name.to_string(), exported_sym.clone());
                }
            }
        }
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
/// - `diagnostic_handler`: For reporting import resolution errors
#[allow(clippy::too_many_arguments)]
pub fn check_import_statement(
    import: &ImportDeclaration,
    symbol_table: &mut SymbolTable,
    type_env: &mut TypeEnvironment,
    access_control: &mut AccessControl,
    interner: &StringInterner,
    module_dependencies: &mut Vec<PathBuf>,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    current_module_id: Option<&ModuleId>,
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
            for spec in specifiers {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
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
            for spec in specifiers {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
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
                    for member in &obj_type.members {
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
                                    parameters: method.parameters.clone(),
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
            for spec in named {
                let name_str = interner.resolve(spec.imported.node);
                let import_type = resolve_import_type(
                    &import.source,
                    &name_str,
                    import.span,
                    module_dependencies,
                    module_registry,
                    module_resolver,
                    current_module_id,
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

/// Resolve the type of an imported symbol from a source module.
///
/// This function attempts to resolve the type of a symbol being imported from another module.
/// If module resolution is configured and the source module is found, it looks up the symbol
/// in the module's exports and returns its type. If resolution fails, it reports an error
/// via the diagnostic handler and returns an Unknown type as a fallback.
///
/// Module dependencies are tracked by adding the resolved source module path to the dependencies vector.
#[allow(clippy::too_many_arguments)]
fn resolve_import_type(
    source: &str,
    symbol_name: &str,
    span: Span,
    module_dependencies: &mut Vec<PathBuf>,
    module_registry: Option<&Arc<ModuleRegistry>>,
    module_resolver: Option<&Arc<ModuleResolver>>,
    current_module_id: Option<&ModuleId>,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
) -> Result<Type, TypeCheckError> {
    if let (Some(registry), Some(resolver), Some(current_id)) =
        (module_registry, module_resolver, current_module_id)
    {
        match resolver.resolve(source, current_id.path()) {
            Ok(source_module_id) => {
                // Track dependency
                module_dependencies.push(source_module_id.path().to_path_buf());

                match registry.get_exports(&source_module_id) {
                    Ok(source_exports) => {
                        if let Some(exported_sym) = source_exports.get_named(symbol_name) {
                            return Ok(exported_sym.symbol.typ.clone());
                        }
                    }
                    Err(_) => {
                        // Module exists but exports not available yet
                    }
                }
            }
            Err(e) => {
                diagnostic_handler.error(
                    span,
                    &format!("Failed to resolve module '{}': {}", source, e),
                );
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
    }

    // Fallback: return Unknown type
    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
}
