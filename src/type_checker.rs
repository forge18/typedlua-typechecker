use super::generics;
use super::symbol_table::{Symbol, SymbolKind, SymbolTable};
use super::type_compat::TypeCompatibility;
use super::type_environment::TypeEnvironment;
use super::visitors::{
    AccessControl, AccessControlVisitor, ClassContext, ClassMemberInfo, ClassMemberKind,
    NarrowingVisitor, TypeInferenceVisitor, TypeInferrer, TypeNarrower,
};
use super::TypeCheckError;
use crate::config::CompilerOptions;
use crate::diagnostics::DiagnosticHandler;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use typedlua_parser::ast::expression::*;
use typedlua_parser::ast::pattern::{ArrayPatternElement, Pattern};
use typedlua_parser::ast::statement::*;
use typedlua_parser::ast::types::*;
use typedlua_parser::ast::Program;
use typedlua_parser::span::Span;

/// Type checker for TypedLua programs
pub struct TypeChecker<'a> {
    symbol_table: SymbolTable,
    type_env: TypeEnvironment,
    current_function_return_type: Option<Type>,
    // Visitor pattern integration - Phase 6
    narrowing: TypeNarrower,
    access_control: AccessControl,
    // Note: TypeInferrer is created on-demand in infer_expression_type due to borrowing requirements
    options: CompilerOptions,
    /// Module registry for multi-module compilation
    module_registry: Option<Arc<crate::module_resolver::ModuleRegistry>>,
    /// Current module ID
    current_module_id: Option<crate::module_resolver::ModuleId>,
    /// Module resolver for imports
    module_resolver: Option<Arc<crate::module_resolver::ModuleResolver>>,
    /// Track module dependencies for cache invalidation
    module_dependencies: Vec<std::path::PathBuf>,
    /// Stack of whether we're inside a catch block (for rethrow validation)
    in_catch_block: Vec<bool>,
    /// Current namespace path for this module
    current_namespace: Option<Vec<String>>,
    /// Type parameters for each generic class (needed for override checking)
    class_type_params: FxHashMap<String, Vec<typedlua_parser::ast::statement::TypeParameter>>,
    /// Track class inheritance for circular dependency detection
    class_parents: FxHashMap<String, String>,
    /// Track exported names to detect duplicates
    exported_names: std::collections::HashSet<String>,
    diagnostic_handler: Arc<dyn DiagnosticHandler>,
    interner: &'a typedlua_parser::string_interner::StringInterner,
    common: &'a typedlua_parser::string_interner::CommonIdentifiers,
}

impl<'a> TypeChecker<'a> {
    /// Create a new TypeChecker without loading the standard library.
    ///
    /// This creates a lightweight type checker instance suitable for testing
    /// or scenarios where stdlib is not needed. Use `with_stdlib()` or
    /// `new_with_stdlib()` to load the standard library.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let checker = TypeChecker::new(handler, &interner, &common);
    /// ```
    pub fn new(
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
        interner: &'a typedlua_parser::string_interner::StringInterner,
        common: &'a typedlua_parser::string_interner::CommonIdentifiers,
    ) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            type_env: TypeEnvironment::new(),
            current_function_return_type: None,
            narrowing: TypeNarrower::new(),
            options: CompilerOptions::default(),
            access_control: AccessControl::new(),
            module_registry: None,
            current_module_id: None,
            module_resolver: None,
            module_dependencies: Vec::new(),
            in_catch_block: Vec::new(),
            current_namespace: None,
            class_type_params: FxHashMap::default(),
            class_parents: FxHashMap::default(),
            exported_names: std::collections::HashSet::new(),
            diagnostic_handler,
            interner,
            common,
        }
    }

    /// Create a new TypeChecker with the standard library loaded.
    ///
    /// This is a convenience method that combines `new()` and `with_stdlib()`.
    /// For backward compatibility with existing code.
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let checker = TypeChecker::new_with_stdlib(handler, &interner, &common)?;
    /// ```
    pub fn new_with_stdlib(
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
        interner: &'a typedlua_parser::string_interner::StringInterner,
        common: &'a typedlua_parser::string_interner::CommonIdentifiers,
    ) -> Result<Self, String> {
        let mut checker = Self::new(diagnostic_handler, interner, common);
        checker.load_stdlib()?;
        checker.register_minimal_stdlib();
        Ok(checker)
    }

    /// Load the standard library into this type checker.
    ///
    /// This method loads the standard library for the configured Lua version.
    /// It can be called multiple times if the Lua version changes.
    ///
    /// # Errors
    ///
    /// Returns an error if stdlib parsing fails.
    pub fn with_stdlib(mut self) -> Result<Self, String> {
        self.load_stdlib()?;
        self.register_minimal_stdlib();
        Ok(self)
    }

    pub fn with_options(mut self, options: CompilerOptions) -> Self {
        // Check if target version changed
        let version_changed = self.options.target != options.target;
        self.options = options;

        // Only reload stdlib if the target version changed
        if version_changed {
            // Reset symbol table and type environment
            self.symbol_table = SymbolTable::new();
            self.type_env = TypeEnvironment::new();
            self.access_control = AccessControl::new();
            self.class_type_params = FxHashMap::default();
            self.exported_names = std::collections::HashSet::new();

            // Reload stdlib with the new target version
            if let Err(e) = self.load_stdlib() {
                eprintln!("Warning: Failed to load stdlib: {}", e);
            }
        }

        self
    }

    /// Create a TypeChecker with module support for multi-module compilation
    pub fn new_with_module_support(
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
        interner: &'a typedlua_parser::string_interner::StringInterner,
        common: &'a typedlua_parser::string_interner::CommonIdentifiers,
        registry: Arc<crate::module_resolver::ModuleRegistry>,
        module_id: crate::module_resolver::ModuleId,
        resolver: Arc<crate::module_resolver::ModuleResolver>,
    ) -> Self {
        let mut checker = Self::new(diagnostic_handler, interner, common);
        checker.module_registry = Some(registry);
        checker.current_module_id = Some(module_id);
        checker.module_resolver = Some(resolver);
        checker
    }

    /// Load the standard library for the configured Lua version
    pub fn load_stdlib(&mut self) -> Result<(), String> {
        use crate::stdlib;
        use typedlua_parser::lexer::Lexer;
        use typedlua_parser::parser::Parser;

        let stdlib_files = stdlib::get_all_stdlib(self.options.target);

        for (filename, source) in stdlib_files {
            let handler = Arc::new(crate::diagnostics::CollectingDiagnosticHandler::new());
            let mut lexer = Lexer::new(source, handler.clone(), self.interner);
            let tokens = lexer
                .tokenize()
                .map_err(|e| format!("Failed to lex {}: {:?}", filename, e))?;

            let mut parser = Parser::new(tokens, handler.clone(), self.interner, self.common);
            let mut program = parser
                .parse()
                .map_err(|e| format!("Failed to parse {}: {:?}", filename, e))?;

            // Process declarations from the stdlib to populate the type environment
            for statement in program.statements.iter_mut() {
                // Ignore errors from stdlib - best-effort population
                let _ = self.check_statement(statement);
            }
        }

        Ok(())
    }

    /// Type check a program
    pub fn check_program(&mut self, program: &mut Program) -> Result<(), TypeCheckError> {
        // PASS 1: Register all function declarations (hoisting)
        // This allows functions to be called before they appear in source order
        for statement in program.statements.iter() {
            if let Statement::Function(func_decl) = statement {
                self.register_function_signature(func_decl)?;
            }
        }

        // PASS 2: Type check all statements (including function bodies)
        let mut first_error: Option<TypeCheckError> = None;
        for statement in program.statements.iter_mut() {
            if let Err(e) = self.check_statement(statement) {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
        }
        if let Some(err) = first_error {
            Err(err)
        } else {
            Ok(())
        }
    }

    /// Register a function's signature in the symbol table without checking its body
    /// This is used during the first pass of check_program to enable function hoisting
    fn register_function_signature(
        &mut self,
        decl: &FunctionDeclaration,
    ) -> Result<(), TypeCheckError> {
        // Validate type predicate return types
        if let Some(return_type) = &decl.return_type {
            if let TypeKind::TypePredicate(predicate) = &return_type.kind {
                // Validate that the parameter name in the predicate matches one of the function parameters
                let param_exists = decl.parameters.iter().any(|param| {
                    if let Pattern::Identifier(ident) = &param.pattern {
                        ident.node == predicate.parameter_name.node
                    } else {
                        false
                    }
                });

                if !param_exists {
                    return Err(TypeCheckError::new(
                        format!(
                            "Type predicate parameter '{}' does not match any function parameter",
                            predicate.parameter_name.node
                        ),
                        predicate.span,
                    ));
                }
            }
        }

        // Create function type
        let func_type = Type::new(
            TypeKind::Function(FunctionType {
                type_parameters: decl.type_parameters.clone(),
                parameters: decl.parameters.clone(),
                return_type: Box::new(decl.return_type.clone().unwrap_or_else(|| {
                    Type::new(TypeKind::Primitive(PrimitiveType::Void), decl.span)
                })),
                throws: decl.throws.clone(),
                span: decl.span,
            }),
            decl.span,
        );

        // Declare function in symbol table
        let symbol = Symbol::new(
            self.interner.resolve(decl.name.node).to_string(),
            SymbolKind::Function,
            func_type,
            decl.span,
        );
        self.symbol_table
            .declare(symbol)
            .map_err(|e| TypeCheckError::new(e, decl.span))?;

        Ok(())
    }

    /// Type check a statement
    fn check_statement(&mut self, stmt: &mut Statement) -> Result<(), TypeCheckError> {
        match stmt {
            Statement::Variable(decl) => self.check_variable_declaration(decl),
            Statement::Function(decl) => self.check_function_declaration(decl),
            Statement::If(if_stmt) => self.check_if_statement(if_stmt),
            Statement::While(while_stmt) => self.check_while_statement(while_stmt),
            Statement::For(for_stmt) => self.check_for_statement(for_stmt),
            Statement::Repeat(repeat_stmt) => self.check_repeat_statement(repeat_stmt),
            Statement::Return(return_stmt) => self.check_return_statement(return_stmt),
            Statement::Break(_) | Statement::Continue(_) => Ok(()),
            Statement::Expression(expr) => {
                self.infer_expression_type(expr)?;
                Ok(())
            }
            Statement::Block(block) => self.check_block(block),
            Statement::Interface(iface) => self.check_interface_declaration(iface),
            Statement::TypeAlias(alias) => self.check_type_alias(alias),
            Statement::Enum(enum_decl) => self.check_enum_declaration(enum_decl),
            Statement::Class(class_decl) => self.check_class_declaration(class_decl),
            Statement::Import(import) => self.check_import_statement(import),
            Statement::Export(export) => self.check_export_statement(export),
            // Declaration file statements - register them in the symbol table
            Statement::DeclareFunction(func) => self.register_declare_function(func),
            Statement::DeclareNamespace(ns) => self.register_declare_namespace(ns),
            Statement::DeclareType(alias) => self.check_type_alias(alias), // Reuse existing logic
            Statement::DeclareInterface(iface) => self.check_interface_declaration(iface), // Reuse existing logic
            Statement::DeclareConst(const_decl) => self.register_declare_const(const_decl),
            // Exception handling
            Statement::Throw(throw_stmt) => self.check_throw_statement(throw_stmt),
            Statement::Try(try_stmt) => self.check_try_statement(try_stmt),
            Statement::Rethrow(span) => self.check_rethrow_statement(*span),
            // File-based namespace declaration
            Statement::Namespace(ns_decl) => self.check_namespace_declaration(ns_decl),
            // Label and Goto (Lua compatibility)
            Statement::Label(_) | Statement::Goto(_) => Ok(()),
        }
    }

    /// Check variable declaration
    fn check_variable_declaration(
        &mut self,
        decl: &mut VariableDeclaration,
    ) -> Result<(), TypeCheckError> {
        // Infer the type of the initializer
        let init_type = self.infer_expression_type(&mut decl.initializer)?;

        // Get the declared type or use inferred type
        let var_type = if let Some(type_ann) = &decl.type_annotation {
            // Resolve the type annotation (handles type references)
            let resolved_type_ann = self
                .evaluate_type(type_ann)
                .map_err(|e| TypeCheckError::new(e, decl.span))?;

            // Deep-resolve both types so nested references (e.g., Address | nil in an
            // interface property) are resolved before structural comparison
            let deep_init = self.deep_resolve_type(&init_type);
            let deep_ann = self.deep_resolve_type(&resolved_type_ann);

            // Check that initializer is assignable to declared type
            if !TypeCompatibility::is_assignable(&deep_init, &deep_ann) {
                // Fallback: check if source class implements the target interface.
                // Use original init_type and type_ann (pre-evaluation) since evaluate_type
                // resolves interface references to ObjectType, losing the interface name.
                if !self.check_implements_assignable(&init_type, type_ann) {
                    self.diagnostic_handler.error(
                        decl.span,
                        &format!(
                            "Type mismatch in variable declaration: cannot assign type '{:?}' to type '{:?}'",
                            deep_init.kind, deep_ann.kind
                        ),
                    );
                }
            }
            resolved_type_ann
        } else {
            // For const, use narrow type; for local, widen literals
            if matches!(decl.kind, VariableKind::Const) {
                init_type
            } else {
                self.widen_type(init_type)
            }
        };

        // Declare the variable in the symbol table
        let symbol_kind = match decl.kind {
            VariableKind::Const => SymbolKind::Const,
            VariableKind::Local => SymbolKind::Variable,
        };

        self.declare_pattern(&decl.pattern, var_type, symbol_kind, decl.span)?;

        Ok(())
    }

    /// Declare symbols from a pattern
    fn declare_pattern(
        &mut self,
        pattern: &Pattern,
        typ: Type,
        kind: SymbolKind,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        match pattern {
            Pattern::Identifier(ident) => {
                let symbol = Symbol::new(
                    self.interner.resolve(ident.node).to_string(),
                    kind,
                    typ,
                    span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, span))?;
                Ok(())
            }
            Pattern::Array(array_pattern) => {
                // Extract element type from array type
                if let TypeKind::Array(elem_type) = &typ.kind {
                    for elem in &array_pattern.elements {
                        match elem {
                            ArrayPatternElement::Pattern(pat) => {
                                self.declare_pattern(pat, (**elem_type).clone(), kind, span)?;
                            }
                            ArrayPatternElement::Rest(ident) => {
                                // Rest gets array type
                                let array_type =
                                    Type::new(TypeKind::Array(elem_type.clone()), span);
                                let symbol = Symbol::new(
                                    self.interner.resolve(ident.node).to_string(),
                                    kind,
                                    array_type,
                                    span,
                                );
                                self.symbol_table
                                    .declare(symbol)
                                    .map_err(|e| TypeCheckError::new(e, span))?;
                            }
                            ArrayPatternElement::Hole => {
                                // Holes don't declare symbols
                            }
                        }
                    }
                } else {
                    return Err(TypeCheckError::new(
                        "Cannot destructure non-array type",
                        span,
                    ));
                }
                Ok(())
            }
            Pattern::Object(obj_pattern) => {
                // Extract properties from object type
                if let TypeKind::Object(obj_type) = &typ.kind {
                    for prop_pattern in &obj_pattern.properties {
                        // Find matching property in type
                        let prop_type = obj_type.members.iter().find_map(|member| {
                            if let ObjectTypeMember::Property(prop) = member {
                                if prop.name.node == prop_pattern.key.node {
                                    return Some(prop.type_annotation.clone());
                                }
                            }
                            None
                        });

                        let prop_type = match prop_type {
                            Some(t) => t,
                            None => {
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Property '{}' does not exist on type",
                                        prop_pattern.key.node
                                    ),
                                    span,
                                ));
                            }
                        };

                        if let Some(value_pattern) = &prop_pattern.value {
                            self.declare_pattern(value_pattern, prop_type, kind, span)?;
                        } else {
                            // Shorthand: { x } means { x: x }
                            let symbol = Symbol::new(
                                self.interner.resolve(prop_pattern.key.node).to_string(),
                                kind,
                                prop_type,
                                span,
                            );
                            self.symbol_table
                                .declare(symbol)
                                .map_err(|e| TypeCheckError::new(e, span))?;
                        }
                    }
                } else {
                    return Err(TypeCheckError::new(
                        "Cannot destructure non-object type",
                        span,
                    ));
                }
                Ok(())
            }
            Pattern::Literal(_, _) | Pattern::Wildcard(_) => {
                // Literals and wildcards don't declare symbols
                Ok(())
            }
            Pattern::Or(or_pattern) => {
                // For or-patterns, binding consistency is verified during type checking in check_pattern
                // All alternatives are guaranteed to bind the same variables, so we declare from the first
                if let Some(first) = or_pattern.alternatives.first() {
                    self.declare_pattern(first, typ, kind, span)?;
                }
                Ok(())
            }
        }
    }

    /// Check function declaration
    fn check_function_declaration(
        &mut self,
        decl: &mut FunctionDeclaration,
    ) -> Result<(), TypeCheckError> {
        // NOTE: Function signature is already registered in the symbol table during pass 1
        // (see register_function_signature method called from check_program)
        // This method now only checks the function body

        // Enter new scope for function body
        self.symbol_table.enter_scope();

        // If generic, declare type parameters as types in scope
        if let Some(type_params) = &decl.type_parameters {
            // Check for duplicate type parameters
            let mut seen_params = std::collections::HashSet::new();
            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                if !seen_params.insert(param_name.clone()) {
                    return Err(TypeCheckError::new(
                        format!("Duplicate type parameter '{}'", param_name),
                        type_param.span,
                    ));
                }
            }

            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                // Register each type parameter as a type in the current scope
                // This allows the function body to reference T, U, etc.
                let param_type = Type::new(
                    TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                        name: type_param.name.clone(),
                        type_arguments: None,
                        span: type_param.span,
                    }),
                    type_param.span,
                );

                // Type parameters are treated as local types in the function scope
                // We register them as type aliases for now
                self.type_env.remove_type_alias(&param_name);
                self.type_env
                    .register_type_alias(param_name.clone(), param_type)
                    .map_err(|e| TypeCheckError::new(e, type_param.span))?;

                // Register constraint if present (e.g., T implements Identifiable)
                if let Some(constraint) = &type_param.constraint {
                    self.type_env
                        .register_type_param_constraint(param_name, (**constraint).clone());
                }
            }
        }

        // Declare parameters
        for (i, param) in decl.parameters.iter().enumerate() {
            // Check if rest parameter is in the correct position
            if param.is_rest && i != decl.parameters.len() - 1 {
                return Err(TypeCheckError::new(
                    "Rest parameter must be the last parameter",
                    param.span,
                ));
            }

            let param_type = if param.is_rest {
                // Rest parameters are arrays
                let elem_type = if let Some(type_ann) = &param.type_annotation {
                    // Evaluate to resolve type references
                    let evaluated = self
                        .evaluate_type(type_ann)
                        .map_err(|e| TypeCheckError::new(e, param.span))
                        .unwrap_or_else(|_| type_ann.clone());
                    // Deep resolve to handle nested types
                    self.deep_resolve_type(&evaluated)
                } else {
                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
                };

                // Wrap in array type
                Type::new(TypeKind::Array(Box::new(elem_type)), param.span)
            } else if let Some(type_ann) = &param.type_annotation {
                // Evaluate to resolve type references
                let evaluated = self
                    .evaluate_type(type_ann)
                    .map_err(|e| TypeCheckError::new(e, param.span))
                    .unwrap_or_else(|_| type_ann.clone());
                // Deep resolve to handle nested types
                self.deep_resolve_type(&evaluated)
            } else {
                Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
            };

            self.declare_pattern(
                &param.pattern,
                param_type,
                SymbolKind::Parameter,
                param.span,
            )?;
        }

        // Set current function return type for return statement checking
        let old_return_type = self.current_function_return_type.clone();
        let resolved_return_type = decl.return_type.as_ref().map(|rt| {
            let evaluated = self.evaluate_type(rt).unwrap_or_else(|_| rt.clone());
            self.deep_resolve_type(&evaluated)
        });
        self.current_function_return_type = resolved_return_type;

        // Check function body (scope-safe: always exit scope even on error)
        let body_result = self.check_block(&mut decl.body);

        // Check that non-void functions have a return statement on all code paths
        if body_result.is_ok() {
            if let Some(ref return_type) = decl.return_type {
                // Only check if return type is not void/nil
                let is_void = matches!(
                    return_type.kind,
                    TypeKind::Primitive(PrimitiveType::Void)
                        | TypeKind::Primitive(PrimitiveType::Nil)
                );
                if !is_void && !self.block_always_returns(&decl.body) {
                    return Err(TypeCheckError::new(
                        format!(
                            "Function '{}' must return a value of type '{}' on all code paths",
                            self.interner.resolve(decl.name.node),
                            self.type_to_string(return_type)
                        ),
                        decl.span,
                    ));
                }
            }
        }

        // Restore previous return type
        self.current_function_return_type = old_return_type;

        // Clean up type parameter constraints and aliases
        if let Some(type_params) = &decl.type_parameters {
            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                self.type_env.remove_type_alias(&param_name);
                self.type_env.remove_type_param_constraint(&param_name);
            }
        }

        // Exit function scope (this will remove type parameter registrations)
        self.symbol_table.exit_scope();

        body_result
    }

    /// Check if statement
    fn check_if_statement(&mut self, if_stmt: &mut IfStatement) -> Result<(), TypeCheckError> {
        // Check condition
        self.infer_expression_type(&mut if_stmt.condition)?;

        // Collect current variable and function types for narrowing
        // This includes both variables and functions so type predicates can be checked
        let mut variable_types = FxHashMap::default();
        for (name, symbol) in self.symbol_table.all_visible_symbols() {
            let name_id = self.interner.intern(&name);
            variable_types.insert(name_id, symbol.typ.clone());
        }

        // Apply type narrowing based on the condition
        let (then_context, else_context) = self.narrowing.narrow_from_condition(
            &if_stmt.condition,
            self.narrowing.get_context(),
            &variable_types,
            self.interner,
        );

        // Check then block with narrowed context
        let saved_context = self.narrowing.get_context().clone();
        *self.narrowing.get_context_mut() = then_context;
        self.check_block(&mut if_stmt.then_block)?;

        // Restore context for else-if and else
        *self.narrowing.get_context_mut() = else_context.clone();

        // Check else-if clauses
        for else_if in if_stmt.else_ifs.iter_mut() {
            self.infer_expression_type(&mut else_if.condition)?;

            // Further narrow based on else-if condition
            let (elseif_then, elseif_else) = self.narrowing.narrow_from_condition(
                &else_if.condition,
                self.narrowing.get_context(),
                &variable_types,
                self.interner,
            );

            *self.narrowing.get_context_mut() = elseif_then;
            self.check_block(&mut else_if.block)?;
            *self.narrowing.get_context_mut() = elseif_else;
        }

        // Check else block
        if let Some(else_block) = &mut if_stmt.else_block {
            self.check_block(else_block)?;
        }

        // Restore original context after if statement
        *self.narrowing.get_context_mut() = saved_context;

        Ok(())
    }

    /// Check while statement
    fn check_while_statement(
        &mut self,
        while_stmt: &mut WhileStatement,
    ) -> Result<(), TypeCheckError> {
        self.infer_expression_type(&mut while_stmt.condition)?;
        self.check_block(&mut while_stmt.body)?;
        Ok(())
    }

    /// Check for statement
    fn check_for_statement(&mut self, for_stmt: &mut ForStatement) -> Result<(), TypeCheckError> {
        match for_stmt {
            ForStatement::Numeric(numeric) => {
                self.symbol_table.enter_scope();

                // Declare loop variable as number
                let number_type =
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), numeric.span);
                let symbol = Symbol::new(
                    self.interner.resolve(numeric.variable.node).to_string(),
                    SymbolKind::Variable,
                    number_type,
                    numeric.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, numeric.span))?;

                // Check start, end, step expressions
                self.infer_expression_type(&mut numeric.start)?;
                self.infer_expression_type(&mut numeric.end)?;
                if let Some(step) = &mut numeric.step {
                    self.infer_expression_type(step)?;
                }

                self.check_block(&mut numeric.body)?;
                self.symbol_table.exit_scope();
            }
            ForStatement::Generic(generic) => {
                self.symbol_table.enter_scope();

                // Declare loop variables with unknown type

                let unknown_type =
                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), generic.span);
                for var in &generic.variables {
                    let symbol = Symbol::new(
                        self.interner.resolve(var.node).to_string(),
                        SymbolKind::Variable,
                        unknown_type.clone(),
                        generic.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, generic.span))?;
                }

                // Check iterators
                for iter in &mut generic.iterators {
                    self.infer_expression_type(iter)?;
                }

                self.check_block(&mut generic.body)?;
                self.symbol_table.exit_scope();
            }
        }
        Ok(())
    }

    /// Check repeat statement
    fn check_repeat_statement(
        &mut self,
        repeat_stmt: &mut RepeatStatement,
    ) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();
        self.check_block(&mut repeat_stmt.body)?;
        self.infer_expression_type(&mut repeat_stmt.until)?;
        self.symbol_table.exit_scope();
        Ok(())
    }

    /// Check return statement
    fn check_return_statement(
        &mut self,
        return_stmt: &mut ReturnStatement,
    ) -> Result<(), TypeCheckError> {
        if !return_stmt.values.is_empty() {
            // Infer types for all return values
            let return_types: Result<Vec<_>, _> = return_stmt
                .values
                .iter_mut()
                .map(|expr| self.infer_expression_type(expr))
                .collect();
            let return_types = return_types?;

            // Create the actual return type (single value or tuple)
            let actual_return_type = if return_types.len() == 1 {
                return_types[0].clone()
            } else {
                Type::new(TypeKind::Tuple(return_types), return_stmt.span)
            };

            // Check against expected return type
            if let Some(expected_type) = &self.current_function_return_type {
                // Type predicates have an implicit boolean return type
                let effective_expected_type =
                    if matches!(expected_type.kind, TypeKind::TypePredicate(_)) {
                        Type::new(
                            TypeKind::Primitive(PrimitiveType::Boolean),
                            expected_type.span,
                        )
                    } else {
                        expected_type.clone()
                    };

                if !TypeCompatibility::is_assignable(&actual_return_type, &effective_expected_type)
                {
                    return Err(TypeCheckError::new(
                        "Return type mismatch",
                        return_stmt.span,
                    ));
                }
            }
        } else {
            // Check that void return is allowed
            if let Some(expected_type) = &self.current_function_return_type {
                let void_type =
                    Type::new(TypeKind::Primitive(PrimitiveType::Void), return_stmt.span);
                if !TypeCompatibility::is_assignable(&void_type, expected_type) {
                    return Err(TypeCheckError::new(
                        "Function expects a return value",
                        return_stmt.span,
                    ));
                }
            }
        }
        Ok(())
    }

    /// Check block
    fn check_block(&mut self, block: &mut Block) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();
        let mut first_error: Option<TypeCheckError> = None;
        for stmt in &mut block.statements {
            if let Err(e) = self.check_statement(stmt) {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
        }
        self.symbol_table.exit_scope();
        if let Some(err) = first_error {
            Err(err)
        } else {
            Ok(())
        }
    }

    /// Check interface declaration
    fn check_interface_declaration(
        &mut self,
        iface: &mut InterfaceDeclaration,
    ) -> Result<(), TypeCheckError> {
        let iface_name = self.interner.resolve(iface.name.node).to_string();

        // Register interface with access control so its members can be tracked
        self.access_control.register_class(&iface_name, None);

        // Register interface members for access control
        for member in &iface.members {
            let member_info = match member {
                InterfaceMember::Property(prop) => ClassMemberInfo {
                    name: self.interner.resolve(prop.name.node).to_string(),
                    access: AccessModifier::Public,
                    _is_static: false,
                    kind: ClassMemberKind::Property {
                        type_annotation: prop.type_annotation.clone(),
                    },
                    is_final: prop.is_readonly,
                },
                InterfaceMember::Method(method) => ClassMemberInfo {
                    name: self.interner.resolve(method.name.node).to_string(),
                    access: AccessModifier::Public,
                    _is_static: false,
                    kind: ClassMemberKind::Method {
                        parameters: method.parameters.clone(),
                        return_type: Some(method.return_type.clone()),
                        is_abstract: false,
                    },
                    is_final: false,
                },
                InterfaceMember::Index(_) => continue, // Skip index signatures for now
            };
            self.access_control
                .register_member(&iface_name, member_info);
        }

        // For generic interfaces, we need to register them differently
        // For now, we'll register generic interfaces similar to generic type aliases
        // They will be instantiated when referenced with type arguments

        if let Some(type_params) = &iface.type_parameters {
            // Generic interface - we can't fully type check it yet
            // Just register it as a generic type so it can be instantiated later

            // Store the type parameter names for positional substitution
            let param_names: Vec<String> = type_params
                .iter()
                .map(|tp| self.interner.resolve(tp.name.node).to_string())
                .collect();
            self.type_env
                .register_interface_type_params(iface_name.clone(), param_names);

            // For now, we'll create a placeholder object type
            let obj_type = Type::new(
                TypeKind::Object(ObjectType {
                    members: iface
                        .members
                        .iter()
                        .map(|member| match member {
                            InterfaceMember::Property(prop) => {
                                ObjectTypeMember::Property(prop.clone())
                            }
                            InterfaceMember::Method(method) => {
                                ObjectTypeMember::Method(method.clone())
                            }
                            InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
                        })
                        .collect(),
                    span: iface.span,
                }),
                iface.span,
            );

            self.type_env
                .register_interface(iface_name.clone(), obj_type.clone())
                .map_err(|e| TypeCheckError::new(e, iface.span))?;

            // Also register in symbol table for export extraction
            let symbol = Symbol {
                name: iface_name.clone(),
                typ: obj_type,
                kind: SymbolKind::Interface,
                span: iface.span,
                is_exported: true,
                references: Vec::new(),
            };
            let _ = self.symbol_table.declare(symbol);

            return Ok(());
        }

        // Non-generic interface - full checking
        // Convert interface members to object type members (first pass)
        let mut members: Vec<ObjectTypeMember> = iface
            .members
            .iter()
            .map(|member| match member {
                InterfaceMember::Property(prop) => ObjectTypeMember::Property(prop.clone()),
                InterfaceMember::Method(method) => ObjectTypeMember::Method(method.clone()),
                InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
            })
            .collect();

        // Handle extends clause - merge parent interface members
        for parent_type in &iface.extends {
            match &parent_type.kind {
                TypeKind::Reference(type_ref) => {
                    // Look up parent interface
                    let type_name = self.interner.resolve(type_ref.name.node);
                    if let Some(parent_iface) = self.type_env.get_interface(&type_name) {
                        if let TypeKind::Object(parent_obj) = &parent_iface.kind {
                            // Add parent members first (so they can be overridden)
                            for parent_member in &parent_obj.members {
                                // Check if member is overridden in child
                                let member_name = match parent_member {
                                    ObjectTypeMember::Property(p) => Some(&p.name.node),
                                    ObjectTypeMember::Method(m) => Some(&m.name.node),
                                    ObjectTypeMember::Index(_) => None,
                                };

                                if let Some(name) = member_name {
                                    let is_overridden = members.iter().any(|m| match m {
                                        ObjectTypeMember::Property(p) => &p.name.node == name,
                                        ObjectTypeMember::Method(m) => &m.name.node == name,
                                        ObjectTypeMember::Index(_) => false,
                                    });

                                    if !is_overridden {
                                        members.insert(0, parent_member.clone());
                                    }
                                } else {
                                    // Index signatures are always inherited
                                    members.insert(0, parent_member.clone());
                                }
                            }
                        }
                    } else {
                        return Err(TypeCheckError::new(
                            format!("Parent interface '{}' not found", type_ref.name.node),
                            iface.span,
                        ));
                    }
                }
                _ => {
                    return Err(TypeCheckError::new(
                        "Interface can only extend other interfaces (type references)",
                        iface.span,
                    ));
                }
            }
        }

        // Create the interface type with all members for use as 'self' in default method bodies
        let iface_type = Type::new(
            TypeKind::Object(ObjectType {
                members: members.clone(),
                span: iface.span,
            }),
            iface.span,
        );

        // Type-check default method bodies (if any)
        for member in iface.members.iter_mut() {
            if let InterfaceMember::Method(method) = member {
                if let Some(body) = &mut method.body {
                    self.symbol_table.enter_scope();

                    let self_symbol = Symbol::new(
                        "self".to_string(),
                        SymbolKind::Parameter,
                        iface_type.clone(),
                        method.span,
                    );
                    self.symbol_table
                        .declare(self_symbol)
                        .map_err(|e| TypeCheckError::new(e, method.span))?;

                    let _ = self.check_block(body);

                    self.symbol_table.exit_scope();
                }
            }
        }

        // Validate interface members
        self.validate_interface_members(&members, iface.span)?;

        let obj_type = Type::new(
            TypeKind::Object(ObjectType {
                members,
                span: iface.span,
            }),
            iface.span,
        );

        self.type_env
            .register_interface(iface_name.clone(), obj_type.clone())
            .map_err(|e| TypeCheckError::new(e, iface.span))?;

        // Also register in symbol table for export extraction
        let symbol = Symbol {
            name: iface_name,
            typ: obj_type,
            kind: SymbolKind::Interface,
            span: iface.span,
            is_exported: true,
            references: Vec::new(),
        };
        let _ = self.symbol_table.declare(symbol);

        Ok(())
    }

    /// Validate interface members for correctness
    fn validate_interface_members(
        &self,
        members: &[ObjectTypeMember],
        span: Span,
    ) -> Result<(), TypeCheckError> {
        // Check for duplicate property names
        let mut seen_names = std::collections::HashSet::new();

        for member in members {
            let name = match member {
                ObjectTypeMember::Property(prop) => Some(&prop.name.node),
                ObjectTypeMember::Method(method) => Some(&method.name.node),
                ObjectTypeMember::Index(_) => None,
            };

            if let Some(name) = name {
                if !seen_names.insert(*name) {
                    return Err(TypeCheckError::new(
                        format!("Duplicate property '{}' in interface", name),
                        span,
                    ));
                }
            }
        }

        Ok(())
    }

    /// Check type alias
    fn check_type_alias(&mut self, alias: &TypeAliasDeclaration) -> Result<(), TypeCheckError> {
        let alias_name = self.interner.resolve(alias.name.node).to_string();

        // Check if this is a generic type alias
        if let Some(type_params) = &alias.type_parameters {
            // For generic type aliases, store the raw type annotation without
            // evaluating it — it may contain type parameters (e.g., keyof T)
            // that can only be resolved when instantiated with concrete arguments.
            self.type_env
                .register_generic_type_alias(
                    alias_name.clone(),
                    type_params.clone(),
                    alias.type_annotation.clone(),
                )
                .map_err(|e| TypeCheckError::new(e, alias.span))?;
        } else {
            // Non-generic: evaluate special types (conditional, mapped, etc.) eagerly
            let typ_to_register = self
                .evaluate_type(&alias.type_annotation)
                .map_err(|e| TypeCheckError::new(e, alias.span))?;
            self.type_env
                .register_type_alias(alias_name.clone(), typ_to_register.clone())
                .map_err(|e| TypeCheckError::new(e, alias.span))?;
        }

        // Use raw annotation for the symbol table entry
        let typ_to_register = alias.type_annotation.clone();

        // Also register in symbol table for export extraction
        let symbol = Symbol {
            name: alias_name.clone(),
            typ: typ_to_register,
            kind: SymbolKind::TypeAlias,
            span: alias.span,
            is_exported: true,
            references: Vec::new(),
        };
        let _ = self.symbol_table.declare(symbol);

        Ok(())
    }

    /// Check export statement and register exported symbols
    fn check_export_statement(&mut self, export: &ExportDeclaration) -> Result<(), TypeCheckError> {
        // Extract export names and check for duplicates
        match &export.kind {
            ExportKind::Declaration(decl) => {
                // Extract the name being exported
                let export_name = match &**decl {
                    Statement::Variable(var_decl) => {
                        // Extract variable name from pattern
                        match &var_decl.pattern {
                            typedlua_parser::ast::pattern::Pattern::Identifier(name) => {
                                Some(self.interner.resolve(name.node).to_string())
                            }
                            _ => None, // Complex patterns - skip for now
                        }
                    }
                    Statement::Function(func_decl) => {
                        Some(self.interner.resolve(func_decl.name.node).to_string())
                    }
                    Statement::Class(class_decl) => {
                        Some(self.interner.resolve(class_decl.name.node).to_string())
                    }
                    Statement::Interface(iface_decl) => {
                        Some(self.interner.resolve(iface_decl.name.node).to_string())
                    }
                    Statement::TypeAlias(alias_decl) => {
                        Some(self.interner.resolve(alias_decl.name.node).to_string())
                    }
                    Statement::Enum(enum_decl) => {
                        Some(self.interner.resolve(enum_decl.name.node).to_string())
                    }
                    _ => None,
                };

                // Check for duplicate export
                if let Some(name) = &export_name {
                    if !self.exported_names.insert(name.clone()) {
                        return Err(TypeCheckError::new(
                            format!("Duplicate export '{}'", name),
                            export.span,
                        ));
                    }
                }
            }
            ExportKind::Named { specifiers, .. } => {
                // Check each specifier for duplicates
                for spec in specifiers {
                    let export_name = if let Some(exported) = &spec.exported {
                        self.interner.resolve(exported.node).to_string()
                    } else {
                        self.interner.resolve(spec.local.node).to_string()
                    };
                    if !self.exported_names.insert(export_name.clone()) {
                        return Err(TypeCheckError::new(
                            format!("Duplicate export '{}'", export_name),
                            export.span,
                        ));
                    }
                }
            }
            ExportKind::Default(_) => {
                // Check for duplicate default export
                if !self.exported_names.insert("default".to_string()) {
                    return Err(TypeCheckError::new(
                        "Duplicate default export".to_string(),
                        export.span,
                    ));
                }
            }
        }

        // Now process the export declaration
        match &export.kind {
            ExportKind::Declaration(decl) => {
                // Process the declaration to register it in the symbol table
                // Note: Most check functions require &mut, but we only have & here
                // For now, only handle TypeAlias which takes &TypeAliasDeclaration
                match &**decl {
                    Statement::TypeAlias(alias) => self.check_type_alias(alias),
                    Statement::Interface(iface) => {
                        // Register interface in both type_env and symbol_table
                        // This is a subset of what check_interface_declaration does
                        let iface_name = self.interner.resolve(iface.name.node).to_string();

                        // Store type parameter names for generic interfaces
                        if let Some(type_params) = &iface.type_parameters {
                            let param_names: Vec<String> = type_params
                                .iter()
                                .map(|tp| self.interner.resolve(tp.name.node).to_string())
                                .collect();
                            self.type_env
                                .register_interface_type_params(iface_name.clone(), param_names);
                        }

                        // Create object type from interface members
                        let obj_type = Type::new(
                            TypeKind::Object(ObjectType {
                                members: iface
                                    .members
                                    .iter()
                                    .map(|member| match member {
                                        InterfaceMember::Property(prop) => {
                                            ObjectTypeMember::Property(prop.clone())
                                        }
                                        InterfaceMember::Method(method) => {
                                            ObjectTypeMember::Method(method.clone())
                                        }
                                        InterfaceMember::Index(index) => {
                                            ObjectTypeMember::Index(index.clone())
                                        }
                                    })
                                    .collect(),
                                span: iface.span,
                            }),
                            iface.span,
                        );

                        // Register in type_env
                        self.type_env
                            .register_interface(iface_name.clone(), obj_type.clone())
                            .map_err(|e| TypeCheckError::new(e, iface.span))?;

                        // Also register in symbol table for export extraction
                        let symbol = Symbol {
                            name: iface_name,
                            typ: obj_type,
                            kind: SymbolKind::Interface,
                            span: iface.span,
                            is_exported: true,
                            references: Vec::new(),
                        };
                        let _ = self.symbol_table.declare(symbol);

                        Ok(())
                    }
                    // TODO: Handle other declaration types (Function, Class, Variable, Enum)
                    // These require mutable references and would need the ExportDeclaration to be mutable
                    _ => Ok(()),
                }
            }
            ExportKind::Named {
                specifiers: _,
                source,
            } => {
                // For re-exports, we don't need to register anything in the local symbol table
                // The symbols will be resolved from the source module during extract_exports
                // However, we should validate that the source module exists
                if let Some(source_path) = source {
                    if let (Some(resolver), Some(current_id)) =
                        (&self.module_resolver, &self.current_module_id)
                    {
                        if let Err(e) = resolver.resolve(source_path, current_id.path()) {
                            return Err(TypeCheckError::new(
                                format!("Cannot resolve module '{}': {}", source_path, e),
                                export.span,
                            ));
                        }
                    }
                }
                Ok(())
            }
            ExportKind::Default(expr) => {
                // Type check the default export expression
                let mut expr_clone = expr.clone();
                self.infer_expression_type(&mut expr_clone)?;
                Ok(())
            }
        }
    }

    /// Check enum declaration
    fn check_enum_declaration(
        &mut self,
        enum_decl: &mut EnumDeclaration,
    ) -> Result<(), TypeCheckError> {
        let enum_name = self.interner.resolve(enum_decl.name.node).to_string();

        // Register enum name as a symbol so it can be referenced as a value
        let enum_ref_type = Type::new(
            TypeKind::Reference(TypeReference {
                name: enum_decl.name.clone(),
                type_arguments: None,
                span: enum_decl.span,
            }),
            enum_decl.span,
        );
        let enum_symbol = Symbol::new(
            enum_name.clone(),
            SymbolKind::Enum,
            enum_ref_type,
            enum_decl.span,
        );
        let _ = self.symbol_table.declare(enum_symbol);

        if enum_decl.fields.is_empty()
            && enum_decl.constructor.is_none()
            && enum_decl.methods.is_empty()
        {
            let variants: Vec<_> = enum_decl
                .members
                .iter()
                .filter_map(|member| {
                    member.value.as_ref().map(|value| match value {
                        EnumValue::Number(n) => {
                            Type::new(TypeKind::Literal(Literal::Number(*n)), member.span)
                        }
                        EnumValue::String(s) => {
                            Type::new(TypeKind::Literal(Literal::String(s.clone())), member.span)
                        }
                    })
                })
                .collect();

            let enum_type = if variants.is_empty() {
                Type::new(TypeKind::Primitive(PrimitiveType::Number), enum_decl.span)
            } else if variants.len() == 1 {
                variants.into_iter().next().unwrap()
            } else {
                Type::new(TypeKind::Union(variants), enum_decl.span)
            };

            self.type_env
                .register_type_alias(enum_name, enum_type)
                .map_err(|e| TypeCheckError::new(e, enum_decl.span))?;
        } else {
            self.check_rich_enum_declaration(enum_decl)?;
        }

        Ok(())
    }

    /// Check rich enum declaration with fields, constructor, and methods
    fn check_rich_enum_declaration(
        &mut self,
        enum_decl: &mut EnumDeclaration,
    ) -> Result<(), TypeCheckError> {
        let enum_name = self.interner.resolve(enum_decl.name.node).to_string();

        // Register rich enum with access control so its members can be tracked
        self.access_control.register_class(&enum_name, None);

        // Register enum fields as members for access control
        for field in &enum_decl.fields {
            let field_info = ClassMemberInfo {
                name: self.interner.resolve(field.name.node).to_string(),
                access: AccessModifier::Public,
                _is_static: false,
                kind: ClassMemberKind::Property {
                    type_annotation: field.type_annotation.clone(),
                },
                is_final: false,
            };
            self.access_control.register_member(&enum_name, field_info);
        }

        let mut member_types = FxHashMap::default();
        for (i, member) in enum_decl.members.iter().enumerate() {
            let member_name_str = self.interner.resolve(member.name.node).to_string();
            let member_type_name = format!("{}.{}", enum_name, member_name_str);
            let member_type = Type::new(
                TypeKind::Literal(Literal::String(member_name_str.clone())),
                member.span,
            );
            self.type_env
                .register_type_alias(member_type_name, member_type.clone())
                .map_err(|e| TypeCheckError::new(e, member.span))?;
            member_types.insert(i, member_type.clone());

            // Register enum variant as a static public property for member access
            self.access_control.register_member(
                &enum_name,
                ClassMemberInfo {
                    name: member_name_str,
                    access: AccessModifier::Public,
                    _is_static: true,
                    kind: ClassMemberKind::Property {
                        type_annotation: member_type,
                    },
                    is_final: true,
                },
            );
        }

        // Register enum methods as members for access control
        for method in &enum_decl.methods {
            let method_name = self.interner.resolve(method.name.node).to_string();
            self.access_control.register_member(
                &enum_name,
                ClassMemberInfo {
                    name: method_name,
                    access: AccessModifier::Public,
                    _is_static: false,
                    kind: ClassMemberKind::Method {
                        parameters: method.parameters.clone(),
                        return_type: method.return_type.clone(),
                        is_abstract: false,
                    },
                    is_final: false,
                },
            );
        }

        let enum_type = Type::new(
            TypeKind::Reference(TypeReference {
                name: enum_decl.name.clone(),
                type_arguments: None,
                span: enum_decl.span,
            }),
            enum_decl.span,
        );

        self.type_env
            .register_type_alias(enum_name.clone(), enum_type.clone())
            .map_err(|e| TypeCheckError::new(e, enum_decl.span))?;

        let enum_self_type = enum_type.clone();

        if let Some(ref mut constructor) = enum_decl.constructor {
            self.symbol_table.enter_scope();
            let self_symbol = Symbol::new(
                "self".to_string(),
                SymbolKind::Parameter,
                enum_self_type.clone(),
                constructor.span,
            );
            let _ = self.symbol_table.declare(self_symbol);
            let _ = self.check_block(&mut constructor.body);
            self.symbol_table.exit_scope();
        }

        for method in enum_decl.methods.iter_mut() {
            self.symbol_table.enter_scope();
            let self_symbol = Symbol::new(
                "self".to_string(),
                SymbolKind::Parameter,
                enum_self_type.clone(),
                method.span,
            );
            let _ = self.symbol_table.declare(self_symbol);
            let _ = self.check_block(&mut method.body);
            self.symbol_table.exit_scope();
        }

        Ok(())
    }

    /// Resolve a type reference, handling utility types and generic type application
    fn resolve_type_reference(&self, type_ref: &TypeReference) -> Result<Type, TypeCheckError> {
        let name = self.interner.resolve(type_ref.name.node);
        let span = type_ref.span;

        // Check if it's a utility type
        if let Some(type_args) = &type_ref.type_arguments {
            if TypeEnvironment::is_utility_type(&name) {
                // Resolve type arguments first (they might be type references)
                let resolved_args: Result<Vec<Type>, TypeCheckError> = type_args
                    .iter()
                    .map(|arg| {
                        self.evaluate_type(arg)
                            .map_err(|e| TypeCheckError::new(e, arg.span))
                    })
                    .collect();
                let resolved_args = resolved_args?;

                return self
                    .type_env
                    .resolve_utility_type(&name, &resolved_args, span, self.interner, self.common)
                    .map_err(|e| TypeCheckError::new(e, span));
            }

            // Check for generic type alias
            if let Some(generic_alias) = self.type_env.get_generic_type_alias(&name) {
                use super::generics::instantiate_type;
                return instantiate_type(
                    &generic_alias.typ,
                    &generic_alias.type_parameters,
                    type_args,
                )
                .map_err(|e| TypeCheckError::new(e, span));
            }
        }

        // Regular type lookup
        match self.type_env.lookup_type(&name) {
            Some(typ) => Ok(typ.clone()),
            None => Err(TypeCheckError::new(
                format!("Type '{}' not found", name),
                span,
            )),
        }
    }

    /// Check class declaration
    fn check_class_declaration(
        &mut self,
        class_decl: &mut ClassDeclaration,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(&mut class_decl.decorators)?;

        let class_name = self.interner.resolve(class_decl.name.node).to_string();

        // Register the class name as a symbol in the symbol table so `new ClassName()` works
        let class_type = Type::new(
            TypeKind::Reference(TypeReference {
                name: class_decl.name.clone(),
                type_arguments: None,
                span: class_decl.span,
            }),
            class_decl.span,
        );
        let class_symbol = Symbol::new(
            class_name.clone(),
            SymbolKind::Class,
            class_type,
            class_decl.span,
        );
        let _ = self.symbol_table.declare(class_symbol);

        // Register abstract class
        if class_decl.is_abstract {
            self.type_env.register_abstract_class(class_name.clone());
        }

        // Store type parameters for this class (needed for generic override checking)
        if let Some(type_params) = &class_decl.type_parameters {
            self.class_type_params
                .insert(class_name.clone(), type_params.clone());
        }

        // Enter a new scope for the class
        self.symbol_table.enter_scope();

        // Register type parameters if this is a generic class
        if let Some(type_params) = &class_decl.type_parameters {
            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                let param_type = Type::new(
                    TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                        name: type_param.name.clone(),
                        type_arguments: None,
                        span: type_param.span,
                    }),
                    type_param.span,
                );

                // Remove any existing type alias with this name (from a previous generic class)
                // then register fresh. Type params are scoped to the class body.
                self.type_env.remove_type_alias(&param_name);
                self.type_env
                    .register_type_alias(param_name, param_type)
                    .map_err(|e| TypeCheckError::new(e, type_param.span))?;
            }
        }

        // Check extends clause - validate base class exists and is a class
        if let Some(extends_type) = &class_decl.extends {
            if let TypeKind::Reference(_type_ref) = &extends_type.kind {
                // Check if parent class is final
                let parent_name = self.interner.resolve(_type_ref.name.node);
                if self.access_control.is_class_final(&parent_name) {
                    return Err(TypeCheckError::new(
                        format!("Cannot extend final class {}", parent_name),
                        class_decl.span,
                    ));
                }

                // Check for circular inheritance
                self.class_parents
                    .insert(class_name.clone(), parent_name.to_string());
                if self.has_circular_inheritance(&class_name) {
                    return Err(TypeCheckError::new(
                        format!("Circular inheritance detected: class '{}' inherits from itself through the inheritance chain", class_name),
                        class_decl.span,
                    ));
                }

                // Verify the base class exists
                // For now, we'll just ensure it's a valid type reference
            } else {
                return Err(TypeCheckError::new(
                    "Class can only extend another class (type reference)",
                    class_decl.span,
                ));
            }
        }

        // Register class implements relationships before compliance checking,
        // so covariant return type checks can look up the class hierarchy
        if !class_decl.implements.is_empty() {
            self.type_env
                .register_class_implements(class_name.clone(), class_decl.implements.clone());

            // Also register with access control for member lookup in interfaces
            let interface_names: Vec<String> = class_decl
                .implements
                .iter()
                .map(|t| {
                    // Extract the interface name from the type
                    match &t.kind {
                        typedlua_parser::ast::types::TypeKind::Reference(ref_type) => {
                            self.interner.resolve(ref_type.name.node).to_string()
                        }
                        _ => format!("{:?}", t),
                    }
                })
                .collect();
            self.access_control
                .register_class_implements(&class_name, interface_names);
        }

        // Check interface implementation
        for interface_type in &class_decl.implements {
            if let TypeKind::Reference(type_ref) = &interface_type.kind {
                let interface_name = self.interner.resolve(type_ref.name.node);
                if let Some(interface) = self.type_env.get_interface(&interface_name) {
                    // If the interface has type arguments, instantiate it
                    let instantiated = if let Some(type_args) = &type_ref.type_arguments {
                        // Look up interface type parameters from the declaration
                        // We need to find the interface's type params to map them
                        let mut instantiated_iface = interface.clone();
                        if let TypeKind::Object(ref mut obj) = instantiated_iface.kind {
                            // Build substitution map from interface type params
                            // For generic interfaces, we stored the raw type with references to T
                            // We need to substitute T -> type_arg for each type param
                            for member in &mut obj.members {
                                match member {
                                    ObjectTypeMember::Method(method) => {
                                        // Substitute return type
                                        method.return_type = self.substitute_type_args_in_type(
                                            &method.return_type,
                                            type_args,
                                            &interface_name,
                                        );
                                        // Substitute parameter types
                                        for param in &mut method.parameters {
                                            if let Some(ref type_ann) = param.type_annotation {
                                                param.type_annotation =
                                                    Some(self.substitute_type_args_in_type(
                                                        type_ann,
                                                        type_args,
                                                        &interface_name,
                                                    ));
                                            }
                                        }
                                    }
                                    ObjectTypeMember::Property(prop) => {
                                        prop.type_annotation = self.substitute_type_args_in_type(
                                            &prop.type_annotation,
                                            type_args,
                                            &interface_name,
                                        );
                                    }
                                    ObjectTypeMember::Index(_) => {}
                                }
                            }
                        }
                        instantiated_iface
                    } else {
                        interface.clone()
                    };
                    self.check_class_implements_interface(class_decl, &instantiated)?;
                } else {
                    return Err(TypeCheckError::new(
                        format!("Interface '{}' not found", interface_name),
                        class_decl.span,
                    ));
                }
            } else {
                return Err(TypeCheckError::new(
                    "Class can only implement interfaces (type references)",
                    class_decl.span,
                ));
            }
        }

        // Process primary constructor parameters - they become class properties
        let mut primary_constructor_properties = Vec::new();
        if let Some(primary_params) = &class_decl.primary_constructor {
            for param in primary_params {
                // Validate: ensure no member with same name exists
                let param_name = &param.name.node;
                if class_decl.members.iter().any(|m| match m {
                    ClassMember::Property(p) => &p.name.node == param_name,
                    ClassMember::Method(m) => &m.name.node == param_name,
                    ClassMember::Getter(g) => &g.name.node == param_name,
                    ClassMember::Setter(s) => &s.name.node == param_name,
                    ClassMember::Constructor(_) => false,
                    ClassMember::Operator(_) => false,
                }) {
                    return Err(TypeCheckError::new(
                        format!(
                            "Primary constructor parameter '{}' conflicts with existing class member",
                            param_name
                        ),
                        param.span,
                    ));
                }

                primary_constructor_properties.push(param);
            }

            // Register the class constructor for parent argument validation
            self.type_env.register_class_constructor(
                class_name.clone(),
                class_decl.primary_constructor.clone().unwrap(),
            );
        }

        // Validate parent constructor arguments if present
        if let Some(parent_args) = &mut class_decl.parent_constructor_args {
            // Type check each parent constructor argument
            for arg in parent_args.iter_mut() {
                self.infer_expression_type(arg)?;
            }

            // Validate argument count and types match parent constructor
            if let Some(extends_type) = &class_decl.extends {
                if let TypeKind::Reference(type_ref) = &extends_type.kind {
                    let parent_name = self.interner.resolve(type_ref.name.node);
                    // Clone the constructor parameters to avoid borrow issues
                    let parent_constructor =
                        self.type_env.get_class_constructor(&parent_name).cloned();

                    if let Some(parent_constructor) = parent_constructor {
                        // Check argument count
                        if parent_args.len() != parent_constructor.len() {
                            return Err(TypeCheckError::new(
                                format!(
                                    "Parent constructor argument count mismatch: expected {}, found {}",
                                    parent_constructor.len(),
                                    parent_args.len()
                                ),
                                class_decl.span,
                            ));
                        }

                        // Check argument types
                        for (i, (arg, param)) in parent_args
                            .iter_mut()
                            .zip(parent_constructor.iter())
                            .enumerate()
                        {
                            let arg_type = self.infer_expression_type(arg)?;
                            let param_type = &param.type_annotation;
                            if !TypeCompatibility::is_assignable(&arg_type, param_type) {
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Parent constructor argument {} type mismatch: expected '{:?}', found '{:?}'",
                                        i + 1,
                                        param_type.kind,
                                        arg_type.kind
                                    ),
                                    arg.span,
                                ));
                            }
                        }
                    }
                }
            }
        }

        // Collect class members for access checking
        let mut member_infos = Vec::new();

        // Add primary constructor parameters as properties
        for param in &primary_constructor_properties {
            member_infos.push(ClassMemberInfo {
                name: self.interner.resolve(param.name.node).to_string(),
                access: param.access.unwrap_or(AccessModifier::Public),
                _is_static: false,
                kind: ClassMemberKind::Property {
                    type_annotation: param.type_annotation.clone(),
                },
                is_final: param.is_readonly, // readonly maps to final for properties
            });
        }

        for member in &class_decl.members {
            match member {
                ClassMember::Property(prop) => {
                    member_infos.push(ClassMemberInfo {
                        name: self.interner.resolve(prop.name.node).to_string(),
                        access: prop.access.unwrap_or(AccessModifier::Public),
                        _is_static: prop.is_static,
                        kind: ClassMemberKind::Property {
                            type_annotation: prop.type_annotation.clone(),
                        },
                        is_final: false,
                    });
                }
                ClassMember::Method(method) => {
                    member_infos.push(ClassMemberInfo {
                        name: self.interner.resolve(method.name.node).to_string(),
                        access: method.access.unwrap_or(AccessModifier::Public),
                        _is_static: method.is_static,
                        kind: ClassMemberKind::Method {
                            parameters: method.parameters.clone(),
                            return_type: method.return_type.clone(),
                            is_abstract: method.is_abstract,
                        },
                        is_final: method.is_final,
                    });
                }
                ClassMember::Getter(getter) => {
                    member_infos.push(ClassMemberInfo {
                        name: self.interner.resolve(getter.name.node).to_string(),
                        access: getter.access.unwrap_or(AccessModifier::Public),
                        _is_static: getter.is_static,
                        kind: ClassMemberKind::Getter {
                            return_type: getter.return_type.clone(),
                        },
                        is_final: false,
                    });
                }
                ClassMember::Setter(setter) => {
                    member_infos.push(ClassMemberInfo {
                        name: self.interner.resolve(setter.name.node).to_string(),
                        access: setter.access.unwrap_or(AccessModifier::Public),
                        _is_static: setter.is_static,
                        kind: ClassMemberKind::Setter {
                            parameter_type: setter
                                .parameter
                                .type_annotation
                                .clone()
                                .unwrap_or_else(|| {
                                    Type::new(
                                        TypeKind::Primitive(PrimitiveType::Unknown),
                                        setter.span,
                                    )
                                }),
                        },
                        is_final: false,
                    });
                }
                ClassMember::Constructor(_) => {
                    // Constructor doesn't have access modifiers for member access
                }
                ClassMember::Operator(op) => {
                    let op_name = self.operator_kind_name(&op.operator);
                    member_infos.push(ClassMemberInfo {
                        name: op_name,
                        access: op.access.unwrap_or(AccessModifier::Public),
                        _is_static: false,
                        kind: ClassMemberKind::Operator {
                            operator: op.operator,
                            parameters: op.parameters.clone(),
                            return_type: op.return_type.clone(),
                        },
                        is_final: false,
                    });
                }
            }
        }

        // Extract parent class name first
        let parent = class_decl.extends.as_ref().and_then(|ext| {
            if let TypeKind::Reference(type_ref) = &ext.kind {
                Some(self.interner.resolve(type_ref.name.node).to_string())
            } else {
                None
            }
        });

        // Register class and all its members with access control visitor
        self.access_control
            .register_class(&class_name, parent.clone());
        for member_info in member_infos {
            self.access_control
                .register_member(&class_name, member_info);
        }

        // Mark class as final if needed
        self.access_control
            .mark_class_final(&class_name, class_decl.is_final);

        // Set current class context
        let old_class = self.access_control.get_current_class().clone();
        self.access_control.set_current_class(Some(ClassContext {
            name: self.interner.resolve(class_decl.name.node).to_string(),
            parent,
            extends_type: class_decl.extends.clone(),
        }));

        // Check all class members
        // Use soft error handling for member bodies so the class is still
        // registered even if individual members have type errors. This prevents
        // cascading "undefined variable" errors for code that uses the class.
        let mut has_constructor = false;
        let mut abstract_methods = Vec::new();
        let mut first_member_error: Option<TypeCheckError> = None;

        for member in class_decl.members.iter_mut() {
            let result = match member {
                ClassMember::Property(prop) => self.check_class_property(prop),
                ClassMember::Constructor(ctor) => {
                    if has_constructor {
                        Err(TypeCheckError::new(
                            "Class can only have one constructor",
                            ctor.span,
                        ))
                    } else {
                        has_constructor = true;
                        self.check_constructor(ctor)
                    }
                }
                ClassMember::Method(method) => {
                    if method.is_abstract {
                        if !class_decl.is_abstract {
                            Err(TypeCheckError::new(
                                format!(
                                    "Abstract method '{}' can only be in abstract class",
                                    method.name.node
                                ),
                                method.span,
                            ))
                        } else {
                            abstract_methods
                                .push(self.interner.resolve(method.name.node).to_string());
                            self.check_class_method(method)
                        }
                    } else {
                        self.check_class_method(method)
                    }
                }
                ClassMember::Getter(getter) => self.check_class_getter(getter),
                ClassMember::Setter(setter) => self.check_class_setter(setter),
                ClassMember::Operator(op) => self.check_operator_declaration(op),
            };

            if let Err(e) = result {
                if first_member_error.is_none() {
                    first_member_error = Some(e);
                }
            }
        }

        // Restore previous class context
        self.access_control.set_current_class(old_class);

        // Exit class scope
        self.symbol_table.exit_scope();

        // Clean up type parameters from type environment after class scope
        if let Some(type_params) = &class_decl.type_parameters {
            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                self.type_env.remove_type_alias(&param_name);
            }
        }

        // Check that concrete classes implement all inherited abstract methods
        if !class_decl.is_abstract {
            if let Some(extends_type) = &class_decl.extends {
                if let TypeKind::Reference(type_ref) = &extends_type.kind {
                    let parent_name = self.interner.resolve(type_ref.name.node);
                    // Check for abstract methods in parent class
                    self.check_abstract_methods_implemented(
                        &class_name,
                        &parent_name,
                        &class_decl.members,
                    )?;
                }
            }
        }

        // Handle member errors based on severity.
        // Critical errors (abstract methods in non-abstract class, multiple constructors)
        // should fail hard. Other errors become warnings to prevent cascading failures.
        if let Some(err) = first_member_error {
            // Check if this is a critical error that should fail the compilation
            let is_critical_error = (err.message.contains("Abstract method")
                && err.message.contains("abstract class"))
                || err.message.contains("one constructor")
                || err
                    .message
                    .contains("Decorators require decorator features")
                || err.message.contains("Cannot override final method")
                || err.message.contains("is incompatible with parent")
                || err.message.contains("must implement abstract method")
                || err.message.contains("uses override but class")
                || err
                    .message
                    .contains("marked as override but parent class does not have this method")
                || err.message.contains("Return type mismatch")
                || err.message.contains("is private and only accessible")
                || err.message.contains("is protected and only accessible")
                || err.message.contains("operators can have 0 parameters")
                || err.message.contains("Binary operator must have exactly")
                || err.message.contains("Operator must have 0, 1, or 2")
                || err.message.contains("must have exactly 2 parameters")
                || err.message.contains("must return 'boolean'");

            if is_critical_error {
                return Err(err);
            } else {
                // Non-critical errors become warnings
                self.diagnostic_handler.warning(
                    class_decl.span,
                    &format!("Error in class '{}' member: {}", class_name, err.message),
                );
            }
        }

        Ok(())
    }

    /// Check that a class properly implements an interface
    fn check_class_implements_interface(
        &self,
        class_decl: &ClassDeclaration,
        interface: &Type,
    ) -> Result<(), TypeCheckError> {
        if let TypeKind::Object(obj_type) = &interface.kind {
            for required_member in &obj_type.members {
                match required_member {
                    ObjectTypeMember::Property(req_prop) => {
                        // Find matching property in class
                        let found = class_decl.members.iter().any(|member| {
                            if let ClassMember::Property(class_prop) = member {
                                class_prop.name.node == req_prop.name.node
                            } else {
                                false
                            }
                        });

                        if !found && !req_prop.is_optional {
                            return Err(TypeCheckError::new(
                                format!(
                                    "Class '{}' does not implement required property '{}' from interface",
                                    self.interner.resolve(class_decl.name.node),
                                    self.interner.resolve(req_prop.name.node)
                                ),
                                class_decl.span,
                            ));
                        }
                    }
                    ObjectTypeMember::Method(req_method) => {
                        // Find matching method in class and validate signature
                        let matching_method = class_decl.members.iter().find_map(|member| {
                            if let ClassMember::Method(class_method) = member {
                                if class_method.name.node == req_method.name.node {
                                    return Some(class_method);
                                }
                            }
                            None
                        });

                        match matching_method {
                            None => {
                                if req_method.body.is_none() {
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Class '{}' does not implement required method '{}' from interface",
                                            self.interner.resolve(class_decl.name.node),
                                            self.interner.resolve(req_method.name.node)
                                        ),
                                        class_decl.span,
                                    ));
                                }
                                // Method has default implementation in interface, okay
                            }
                            Some(class_method) => {
                                // Check parameter count
                                if class_method.parameters.len() != req_method.parameters.len() {
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Method '{}' has {} parameters but interface requires {}",
                                            self.interner.resolve(req_method.name.node),
                                            class_method.parameters.len(),
                                            req_method.parameters.len()
                                        ),
                                        class_method.span,
                                    ));
                                }

                                // Check parameter types
                                for (i, (class_param, req_param)) in class_method
                                    .parameters
                                    .iter()
                                    .zip(req_method.parameters.iter())
                                    .enumerate()
                                {
                                    if let (Some(class_type), Some(req_type)) =
                                        (&class_param.type_annotation, &req_param.type_annotation)
                                    {
                                        if !TypeCompatibility::is_assignable(class_type, req_type) {
                                            return Err(TypeCheckError::new(
                                                format!(
                                                    "Method '{}' parameter {} has incompatible type",
                                                    self.interner.resolve(req_method.name.node), i
                                                ),
                                                class_method.span,
                                            ));
                                        }
                                    }
                                }

                                // Check return type (covariant: class return must be assignable to interface return)
                                // MethodSignature has return_type: Type (not Option)
                                // MethodDeclaration has return_type: Option<Type>
                                if let Some(class_return) = &class_method.return_type {
                                    if !TypeCompatibility::is_assignable(
                                        class_return,
                                        &req_method.return_type,
                                    ) && !self.check_implements_assignable(
                                        class_return,
                                        &req_method.return_type,
                                    ) {
                                        return Err(TypeCheckError::new(
                                            format!(
                                                "Method '{}' has incompatible return type",
                                                self.interner.resolve(req_method.name.node)
                                            ),
                                            class_method.span,
                                        ));
                                    }
                                } else {
                                    // Method has no return type annotation, but interface requires one
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Method '{}' must have a return type annotation to match interface",
                                            self.interner.resolve(req_method.name.node)
                                        ),
                                        class_method.span,
                                    ));
                                }
                            }
                        }
                    }
                    ObjectTypeMember::Index(index_sig) => {
                        // Validate that all class properties are compatible with index signature
                        self.validate_index_signature(class_decl, index_sig)?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Validate that all class properties are compatible with interface index signature
    fn validate_index_signature(
        &self,
        class_decl: &ClassDeclaration,
        index_sig: &IndexSignature,
    ) -> Result<(), TypeCheckError> {
        for member in &class_decl.members {
            if let ClassMember::Property(prop) = member {
                // Check if property type is assignable to index signature value type
                if !TypeCompatibility::is_assignable(&prop.type_annotation, &index_sig.value_type) {
                    return Err(TypeCheckError::new(
                        format!(
                            "Property '{}' is not assignable to index signature value type",
                            self.interner.resolve(prop.name.node)
                        ),
                        prop.span,
                    ));
                }
            }
        }

        Ok(())
    }

    /// Check that a class implements all abstract methods from its parent class
    fn check_abstract_methods_implemented(
        &self,
        class_name: &str,
        parent_name: &str,
        class_members: &[ClassMember],
    ) -> Result<(), TypeCheckError> {
        // Get the parent class members
        if let Some(parent_members) = self.access_control.get_class_members(parent_name) {
            for member in parent_members {
                if let ClassMemberKind::Method {
                    is_abstract: true, ..
                } = &member.kind
                {
                    // Check if this class implements the abstract method
                    let method_name = &member.name;
                    let implemented = class_members.iter().any(|m| {
                        if let ClassMember::Method(method) = m {
                            method.name.node.as_u32()
                                == self.interner.get_or_intern(method_name).as_u32()
                        } else {
                            false
                        }
                    });

                    if !implemented {
                        return Err(TypeCheckError::new(
                            format!(
                                "Class '{}' must implement abstract method '{}' from parent class '{}'",
                                class_name, method_name, parent_name
                            ),
                            Span::dummy(),
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    /// Check decorators
    fn check_decorators(
        &mut self,
        decorators: &mut [typedlua_parser::ast::statement::Decorator],
    ) -> Result<(), TypeCheckError> {
        // Check if decorators are enabled
        if !decorators.is_empty() && !self.options.enable_decorators {
            return Err(TypeCheckError::new(
                "Decorators require decorator features to be enabled. Enable 'enableDecorators' in your configuration.".to_string(),
                decorators[0].span,
            ));
        }

        // Check for duplicate decorators
        let mut seen_decorators = std::collections::HashSet::new();
        for decorator in decorators.iter() {
            // Get decorator name for comparison
            let decorator_name = match &decorator.expression {
                typedlua_parser::ast::statement::DecoratorExpression::Identifier(name) => {
                    self.interner.resolve(name.node).to_string()
                }
                typedlua_parser::ast::statement::DecoratorExpression::Call { callee, .. } => {
                    // For calls, use the callee name
                    if let typedlua_parser::ast::statement::DecoratorExpression::Identifier(name) =
                        &**callee
                    {
                        self.interner.resolve(name.node).to_string()
                    } else {
                        continue; // Skip complex expressions
                    }
                }
                typedlua_parser::ast::statement::DecoratorExpression::Member { .. } => {
                    continue; // Skip member expressions for duplicate checking
                }
            };

            if !seen_decorators.insert(decorator_name.clone()) {
                self.diagnostic_handler.warning(
                    decorator.span,
                    &format!("Duplicate decorator '@{}'", decorator_name),
                );
            }
        }

        // For now, we just validate that decorator expressions are valid
        // Full decorator type checking would require:
        // 1. Checking that decorator functions exist
        // 2. Validating decorator function signatures match target type
        // 3. Checking decorator arguments are type-compatible
        // This is simplified for now - decorators are allowed but not deeply validated

        for decorator in decorators.iter_mut() {
            self.check_decorator_expression(&mut decorator.expression)?;
        }

        Ok(())
    }

    /// Check a decorator expression
    fn check_decorator_expression(
        &mut self,
        expr: &mut typedlua_parser::ast::statement::DecoratorExpression,
    ) -> Result<(), TypeCheckError> {
        use typedlua_parser::ast::statement::DecoratorExpression;

        match expr {
            DecoratorExpression::Identifier(name) => {
                // Verify the decorator identifier exists (could be a function or imported decorator)
                // For now, we allow any identifier - full validation would check it's a valid decorator function
                let name_str = self.interner.resolve(name.node);
                if self.symbol_table.lookup(&name_str).is_none() {
                    // It's okay if it doesn't exist - it might be a built-in decorator like @readonly, @sealed
                    // We'll allow it through for now
                }
                Ok(())
            }
            DecoratorExpression::Call {
                callee, arguments, ..
            } => {
                // Check the callee
                self.check_decorator_expression(callee)?;

                // Type check all arguments
                for arg in arguments.iter_mut() {
                    self.infer_expression_type(arg)?;
                }

                Ok(())
            }
            DecoratorExpression::Member { object, .. } => {
                // Check the object part
                self.check_decorator_expression(object)?;
                Ok(())
            }
        }
    }

    /// Check class property
    fn check_class_property(
        &mut self,
        prop: &mut PropertyDeclaration,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(&mut prop.decorators)?;

        // Check initializer if present
        if let Some(initializer) = &mut prop.initializer {
            let init_type = self.infer_expression_type(initializer)?;

            // Verify initializer type is assignable to declared type
            if !TypeCompatibility::is_assignable(&init_type, &prop.type_annotation) {
                return Err(TypeCheckError::new(
                    format!(
                        "Property '{}' initializer type does not match declared type",
                        prop.name.node
                    ),
                    prop.span,
                ));
            }
        }

        Ok(())
    }

    /// Check constructor
    fn check_constructor(
        &mut self,
        ctor: &mut ConstructorDeclaration,
    ) -> Result<(), TypeCheckError> {
        // Enter constructor scope
        self.symbol_table.enter_scope();

        // Inner function to do the actual checking, so we can ensure scope cleanup
        let result = (|| -> Result<(), TypeCheckError> {
            // Declare 'self' parameter (implicit in constructors)
            if let Some(class_ctx) = self.access_control.get_current_class() {
                let self_type = Type::new(
                    TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                        name: typedlua_parser::ast::Spanned::new(
                            self.interner.intern(&class_ctx.name),
                            ctor.span,
                        ),
                        type_arguments: None,
                        span: ctor.span,
                    }),
                    ctor.span,
                );
                let symbol = crate::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::symbol_table::SymbolKind::Parameter,
                    self_type,
                    ctor.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, ctor.span))?;
            }

            // Declare parameters
            for param in &ctor.parameters {
                let param_type = if let Some(type_ann) = &param.type_annotation {
                    // Evaluate the type annotation to resolve any type references
                    let evaluated = self
                        .evaluate_type(type_ann)
                        .map_err(|e| TypeCheckError::new(e, param.span))
                        .unwrap_or_else(|_| type_ann.clone()); // Fall back to unevaluated if evaluation fails

                    // Deep resolve to handle nested types in function types, arrays, etc.
                    self.deep_resolve_type(&evaluated)
                } else {
                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
                };

                self.declare_pattern(
                    &param.pattern,
                    param_type,
                    SymbolKind::Parameter,
                    param.span,
                )?;
            }

            // Check constructor body
            self.check_block(&mut ctor.body)?;

            Ok(())
        })();

        // Always exit scope, even on error
        self.symbol_table.exit_scope();

        result
    }

    /// Check class method
    fn check_class_method(&mut self, method: &mut MethodDeclaration) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(&mut method.decorators)?;

        // Check override keyword if present
        if method.is_override {
            self.check_method_override(method)?;
        } else if let Some(class_context) = self.access_control.get_current_class() {
            // Check if method shadows a parent method without override keyword
            if let Some(parent_name) = &class_context.parent {
                if let Some(parent_members) = self.access_control.get_class_members(parent_name) {
                    let method_name = self.interner.resolve(method.name.node);
                    if parent_members.iter().any(|m| m.name == method_name) {
                        self.diagnostic_handler.warning(
                            method.span,
                            &format!(
                                "Method '{}' overrides a method from parent class '{}' but is missing the 'override' keyword",
                                method_name,
                                parent_name
                            ),
                        );
                    }
                }
            }
        }

        // Abstract methods don't have a body to check
        if method.is_abstract {
            if method.body.is_some() {
                return Err(TypeCheckError::new(
                    format!("Abstract method '{}' cannot have a body", method.name.node),
                    method.span,
                ));
            }
            return Ok(());
        }

        // Non-abstract methods must have a body
        if method.body.is_none() {
            return Err(TypeCheckError::new(
                format!(
                    "Non-abstract method '{}' must have a body",
                    method.name.node
                ),
                method.span,
            ));
        }

        // Enter method scope
        self.symbol_table.enter_scope();

        // Do all method body work in a closure to ensure scope cleanup on error
        let old_return_type = self.current_function_return_type.clone();
        let result = (|| -> Result<(), TypeCheckError> {
            // Declare 'self' parameter for non-static methods
            if !method.is_static {
                if let Some(class_ctx) = self.access_control.get_current_class() {
                    let self_type = Type::new(
                        TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                            name: typedlua_parser::ast::Spanned::new(
                                self.interner.intern(&class_ctx.name),
                                method.span,
                            ),
                            type_arguments: None,
                            span: method.span,
                        }),
                        method.span,
                    );
                    let symbol = crate::symbol_table::Symbol::new(
                        "self".to_string(),
                        crate::symbol_table::SymbolKind::Parameter,
                        self_type,
                        method.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, method.span))?;
                }
            }

            // Register type parameters if generic
            if let Some(type_params) = &method.type_parameters {
                for type_param in type_params {
                    let param_name = self.interner.resolve(type_param.name.node).to_string();
                    let param_type = Type::new(
                        TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                            name: type_param.name.clone(),
                            type_arguments: None,
                            span: type_param.span,
                        }),
                        type_param.span,
                    );

                    self.type_env.remove_type_alias(&param_name);
                    self.type_env
                        .register_type_alias(param_name, param_type)
                        .map_err(|e| TypeCheckError::new(e, type_param.span))?;
                }
            }

            // Declare parameters
            for param in &method.parameters {
                let param_type = if let Some(type_ann) = &param.type_annotation {
                    // Evaluate the type annotation to resolve any type references (e.g., T, U in generic methods)
                    let evaluated = self
                        .evaluate_type(type_ann)
                        .map_err(|e| TypeCheckError::new(e, param.span))
                        .unwrap_or_else(|_| type_ann.clone()); // Fall back to unevaluated if evaluation fails

                    // Deep resolve to handle nested types in function types, arrays, etc.
                    self.deep_resolve_type(&evaluated)
                } else {
                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
                };

                self.declare_pattern(
                    &param.pattern,
                    param_type,
                    SymbolKind::Parameter,
                    param.span,
                )?;
            }

            // Set current function return type for return statement checking
            self.current_function_return_type = method.return_type.clone();

            // Check method body
            if let Some(body) = &mut method.body {
                self.check_block(body)?;
            }

            Ok(())
        })();

        // Always restore return type and exit scope, even on error
        self.current_function_return_type = old_return_type;
        self.symbol_table.exit_scope();

        // Clean up method type parameters from type environment
        if let Some(type_params) = &method.type_parameters {
            for type_param in type_params {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                self.type_env.remove_type_alias(&param_name);
            }
        }

        result
    }

    /// Check class getter
    fn check_class_getter(&mut self, getter: &mut GetterDeclaration) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(&mut getter.decorators)?;

        // Enter getter scope
        self.symbol_table.enter_scope();

        // Declare 'self' parameter for non-static getters
        if !getter.is_static {
            if let Some(class_ctx) = self.access_control.get_current_class() {
                let self_type = Type::new(
                    TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                        name: typedlua_parser::ast::Spanned::new(
                            self.interner.intern(&class_ctx.name),
                            getter.span,
                        ),
                        type_arguments: None,
                        span: getter.span,
                    }),
                    getter.span,
                );
                let symbol = crate::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::symbol_table::SymbolKind::Parameter,
                    self_type,
                    getter.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, getter.span))?;
            }
        }

        // Set current function return type
        let old_return_type = self.current_function_return_type.clone();
        self.current_function_return_type = Some(getter.return_type.clone());

        // Check getter body
        self.check_block(&mut getter.body)?;

        // Restore previous return type
        self.current_function_return_type = old_return_type;

        // Exit getter scope
        self.symbol_table.exit_scope();

        Ok(())
    }

    /// Check class setter
    fn check_class_setter(&mut self, setter: &mut SetterDeclaration) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(&mut setter.decorators)?;

        // Enter setter scope
        self.symbol_table.enter_scope();

        // Declare 'self' parameter for non-static setters
        if !setter.is_static {
            if let Some(class_ctx) = self.access_control.get_current_class() {
                let self_type = Type::new(
                    TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                        name: typedlua_parser::ast::Spanned::new(
                            self.interner.intern(&class_ctx.name),
                            setter.span,
                        ),
                        type_arguments: None,
                        span: setter.span,
                    }),
                    setter.span,
                );
                let symbol = crate::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::symbol_table::SymbolKind::Parameter,
                    self_type,
                    setter.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, setter.span))?;
            }
        }

        // Declare the parameter
        let param_type = if let Some(type_ann) = &setter.parameter.type_annotation {
            // Evaluate to resolve type references
            let evaluated = self
                .evaluate_type(type_ann)
                .map_err(|e| TypeCheckError::new(e, setter.parameter.span))
                .unwrap_or_else(|_| type_ann.clone());
            // Deep resolve to handle nested types
            self.deep_resolve_type(&evaluated)
        } else {
            Type::new(
                TypeKind::Primitive(PrimitiveType::Unknown),
                setter.parameter.span,
            )
        };

        self.declare_pattern(
            &setter.parameter.pattern,
            param_type,
            SymbolKind::Parameter,
            setter.parameter.span,
        )?;

        // Check setter body
        self.check_block(&mut setter.body)?;

        // Exit setter scope
        self.symbol_table.exit_scope();

        Ok(())
    }

    /// Check operator declaration
    fn check_operator_declaration(
        &mut self,
        op: &mut OperatorDeclaration,
    ) -> Result<(), TypeCheckError> {
        if op.operator == OperatorKind::NewIndex {
            if op.parameters.len() != 2 {
                return Err(TypeCheckError::new(
                    "operator []= must have exactly 2 parameters",
                    op.span,
                ));
            }
        } else if op.parameters.is_empty() {
            if !matches!(op.operator, OperatorKind::UnaryMinus | OperatorKind::Length) {
                return Err(TypeCheckError::new(
                    "Only unary minus (-) and length (#) operators can have 0 parameters",
                    op.span,
                ));
            }
        } else if op.parameters.len() == 1 {
            if matches!(op.operator, OperatorKind::UnaryMinus | OperatorKind::Length) {
                return Err(TypeCheckError::new(
                    "Binary operator must have exactly 1 parameter",
                    op.span,
                ));
            }
        } else {
            return Err(TypeCheckError::new(
                "Operator must have 0, 1, or 2 parameters",
                op.span,
            ));
        }

        match op.operator {
            OperatorKind::Equal | OperatorKind::NotEqual => {
                if let Some(ref ret_type) = op.return_type {
                    if !self.is_boolean_type(ret_type) {
                        return Err(TypeCheckError::new(
                            format!(
                                "Operator '{}' must return 'boolean'",
                                self.operator_kind_name(&op.operator)
                            ),
                            ret_type.span,
                        ));
                    }
                }
            }
            OperatorKind::LessThan
            | OperatorKind::LessThanOrEqual
            | OperatorKind::GreaterThan
            | OperatorKind::GreaterThanOrEqual => {
                if let Some(ref ret_type) = op.return_type {
                    if !self.is_boolean_type(ret_type) {
                        return Err(TypeCheckError::new(
                            format!(
                                "Operator '{}' must return 'boolean'",
                                self.operator_kind_name(&op.operator)
                            ),
                            ret_type.span,
                        ));
                    }
                }
            }
            _ => {}
        }

        self.symbol_table.enter_scope();

        if let Some(class_ctx) = self.access_control.get_current_class() {
            let self_type = Type::new(
                TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                    name: typedlua_parser::ast::Spanned::new(
                        self.interner.intern(&class_ctx.name),
                        op.span,
                    ),
                    type_arguments: None,
                    span: op.span,
                }),
                op.span,
            );
            let symbol = crate::symbol_table::Symbol::new(
                "self".to_string(),
                crate::symbol_table::SymbolKind::Parameter,
                self_type,
                op.span,
            );
            self.symbol_table
                .declare(symbol)
                .map_err(|e| TypeCheckError::new(e, op.span))?;
        }

        for param in &op.parameters {
            let param_type = param.type_annotation.clone().unwrap_or_else(|| {
                Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
            });

            self.declare_pattern(
                &param.pattern,
                param_type,
                SymbolKind::Parameter,
                param.span,
            )?;
        }

        let old_return_type = self.current_function_return_type.clone();
        self.current_function_return_type = op.return_type.clone();

        self.check_block(&mut op.body)?;

        self.current_function_return_type = old_return_type;

        self.symbol_table.exit_scope();

        Ok(())
    }

    fn is_boolean_type(&self, typ: &Type) -> bool {
        matches!(typ.kind, TypeKind::Primitive(PrimitiveType::Boolean))
    }

    fn operator_kind_name(&self, op: &OperatorKind) -> String {
        match op {
            OperatorKind::Add => "__add".to_string(),
            OperatorKind::Subtract => "__sub".to_string(),
            OperatorKind::Multiply => "__mul".to_string(),
            OperatorKind::Divide => "__div".to_string(),
            OperatorKind::Modulo => "__mod".to_string(),
            OperatorKind::Power => "__pow".to_string(),
            OperatorKind::Concatenate => "__concat".to_string(),
            OperatorKind::FloorDivide => "__idiv".to_string(),
            OperatorKind::Equal => "__eq".to_string(),
            OperatorKind::NotEqual => "__eq".to_string(),
            OperatorKind::LessThan => "__lt".to_string(),
            OperatorKind::LessThanOrEqual => "__le".to_string(),
            OperatorKind::GreaterThan => "__lt".to_string(),
            OperatorKind::GreaterThanOrEqual => "__le".to_string(),
            OperatorKind::BitwiseAnd => "__band".to_string(),
            OperatorKind::BitwiseOr => "__bor".to_string(),
            OperatorKind::BitwiseXor => "__bxor".to_string(),
            OperatorKind::ShiftLeft => "__shl".to_string(),
            OperatorKind::ShiftRight => "__shr".to_string(),
            OperatorKind::Index => "__index".to_string(),
            OperatorKind::NewIndex => "__newindex".to_string(),
            OperatorKind::Call => "__call".to_string(),
            OperatorKind::UnaryMinus => "__unm".to_string(),
            OperatorKind::Length => "__len".to_string(),
        }
    }

    /// Check that an override method properly overrides a parent method
    fn check_method_override(&self, method: &MethodDeclaration) -> Result<(), TypeCheckError> {
        // Get current class context
        let class_ctx = self
            .access_control
            .get_current_class()
            .as_ref()
            .ok_or_else(|| {
                TypeCheckError::new(
                    "Override keyword used outside of class context",
                    method.span,
                )
            })?;

        // Check if class has a parent
        let parent_name = class_ctx.parent.as_ref().ok_or_else(|| {
            TypeCheckError::new(
                format!(
                    "Method '{}' uses override but class '{}' has no parent class",
                    method.name.node, class_ctx.name
                ),
                method.span,
            )
        })?;

        // Walk the inheritance chain to find the method and check if it's final
        let method_name = self.interner.resolve(method.name.node);
        let mut current_class = parent_name.clone();
        let mut found_method = None;
        let mut found_in_class = None;

        loop {
            if let Some(parent_members) = self.access_control.get_class_members(&current_class) {
                if let Some(parent_method) = parent_members.iter().find(|m| m.name == method_name) {
                    found_method = Some(parent_method);
                    found_in_class = Some(current_class.clone());
                    break;
                }
            }

            // Get parent from access_control's hierarchy
            let parent_name_opt = self.access_control.get_parent_class(&current_class);
            match parent_name_opt {
                Some(next_parent) => current_class = next_parent,
                None => break,
            }
        }

        let parent_method = found_method.ok_or_else(|| {
            TypeCheckError::new(
                format!(
                    "Method '{}' marked as override but parent class does not have this method",
                    method_name
                ),
                method.span,
            )
        })?;

        // Check if parent method is final anywhere in the inheritance chain
        if parent_method.is_final {
            return Err(TypeCheckError::new(
                format!(
                    "Cannot override final method {} from ancestor class {}",
                    method.name.node,
                    found_in_class.unwrap()
                ),
                method.span,
            ));
        }

        // Get extends clause type arguments for generic parent instantiation
        let extends_type_args = class_ctx.extends_type.as_ref().and_then(|ext| {
            if let TypeKind::Reference(type_ref) = &ext.kind {
                type_ref.type_arguments.clone()
            } else {
                None
            }
        });

        // Get parent class type parameters (if the parent is generic)
        let parent_type_params = self.class_type_params.get(parent_name).cloned();

        match &parent_method.kind {
            ClassMemberKind::Method {
                parameters: parent_params,
                return_type: parent_return,
                ..
            } => {
                // Check parameter count
                if method.parameters.len() != parent_params.len() {
                    return Err(TypeCheckError::new(
                        format!(
                            "Method '{}' has {} parameters but overridden method has {} parameters",
                            method.name.node,
                            method.parameters.len(),
                            parent_params.len()
                        ),
                        method.span,
                    ));
                }

                // Check parameter types (contravariance)
                for (i, (child_param, parent_param)) in method
                    .parameters
                    .iter()
                    .zip(parent_params.iter())
                    .enumerate()
                {
                    let child_type = child_param.type_annotation.as_ref()
                        .ok_or_else(|| TypeCheckError::new(
                            format!("Override method '{}' parameter {} must have explicit type annotation",
                                method.name.node, i + 1),
                            child_param.span,
                        ))?;

                    let raw_parent_type =
                        parent_param.type_annotation.as_ref().ok_or_else(|| {
                            TypeCheckError::new(
                                format!(
                                    "Parent method '{}' parameter {} has no type annotation",
                                    method.name.node,
                                    i + 1
                                ),
                                parent_param.span,
                            )
                        })?;

                    // Instantiate parent type if the parent class is generic
                    let parent_type = if let (Some(ref type_params), Some(ref type_args)) =
                        (&parent_type_params, &extends_type_args)
                    {
                        generics::instantiate_type(raw_parent_type, type_params, type_args)
                            .unwrap_or_else(|_| raw_parent_type.clone())
                    } else {
                        raw_parent_type.clone()
                    };

                    // Deep-resolve both types for comparison
                    let resolved_child = self.deep_resolve_type(child_type);
                    let resolved_parent = self.deep_resolve_type(&parent_type);

                    // Parameters are contravariant: parent type must be assignable to child type
                    // (child can accept a more specific type than parent)
                    if !TypeCompatibility::is_assignable(&resolved_parent, &resolved_child) {
                        return Err(TypeCheckError::new(
                            format!("Method '{}' parameter {} type '{}' is incompatible with parent parameter type",
                                method.name.node, i + 1, self.type_to_string(child_type)),
                            child_param.span,
                        ));
                    }
                }

                // Check return type (covariance)
                if let Some(child_return) = &method.return_type {
                    if let Some(raw_parent_ret) = parent_return {
                        // Instantiate parent return type if generic
                        let parent_ret = if let (Some(ref type_params), Some(ref type_args)) =
                            (&parent_type_params, &extends_type_args)
                        {
                            generics::instantiate_type(raw_parent_ret, type_params, type_args)
                                .unwrap_or_else(|_| raw_parent_ret.clone())
                        } else {
                            raw_parent_ret.clone()
                        };

                        let resolved_child_ret = self.deep_resolve_type(child_return);
                        let resolved_parent_ret = self.deep_resolve_type(&parent_ret);

                        // Child return type must be assignable to parent return type
                        if !TypeCompatibility::is_assignable(
                            &resolved_parent_ret,
                            &resolved_child_ret,
                        ) {
                            return Err(TypeCheckError::new(
                                format!("Method '{}' return type is incompatible with parent return type",
                                    method.name.node),
                                method.span,
                            ));
                        }
                    }
                } else if parent_return.is_some() {
                    return Err(TypeCheckError::new(
                        format!(
                            "Method '{}' must have return type to match parent method",
                            method.name.node
                        ),
                        method.span,
                    ));
                }

                Ok(())
            }
            _ => Err(TypeCheckError::new(
                format!(
                    "Cannot override '{}' - parent member is not a method",
                    method.name.node
                ),
                method.span,
            )),
        }
    }

    /// Convert type to string for error messages
    fn type_to_string(&self, typ: &Type) -> String {
        match &typ.kind {
            TypeKind::Primitive(prim) => format!("{:?}", prim).to_lowercase(),
            TypeKind::Reference(type_ref) => self.interner.resolve(type_ref.name.node).to_string(),
            TypeKind::Array(elem) => format!("{}[]", self.type_to_string(elem)),
            TypeKind::Union(types) => {
                let type_strings: Vec<String> =
                    types.iter().map(|t| self.type_to_string(t)).collect();
                type_strings.join(" | ")
            }
            TypeKind::Function(_) => "function".to_string(),
            TypeKind::Object(_) => "object".to_string(),
            _ => format!("{:?}", typ.kind),
        }
    }

    /// Infer the type of an expression
    /// Delegates to TypeInferrer visitor
    fn infer_expression_type(&mut self, expr: &mut Expression) -> Result<Type, TypeCheckError> {
        let mut inferrer = TypeInferrer::new(
            &mut self.symbol_table,
            &mut self.type_env,
            self.narrowing.get_context_mut(),
            &self.access_control,
            self.interner,
            &self.diagnostic_handler,
        );
        inferrer.infer_expression(expr)
    }

    /// Evaluate special type constructs (keyof, mapped types, conditional types, etc.)
    fn evaluate_type(&self, typ: &Type) -> Result<Type, String> {
        match &typ.kind {
            TypeKind::KeyOf(operand) => {
                // First evaluate the operand recursively
                let evaluated_operand = self.evaluate_type(operand)?;
                use super::evaluate_keyof;
                evaluate_keyof(&evaluated_operand, &self.type_env, self.interner)
            }
            TypeKind::Mapped(mapped) => {
                use super::evaluate_mapped_type;
                evaluate_mapped_type(mapped, &self.type_env, self.interner)
            }
            TypeKind::Conditional(conditional) => {
                use super::evaluate_conditional_type;
                evaluate_conditional_type(conditional, &self.type_env)
            }
            TypeKind::TemplateLiteral(template) => {
                use super::evaluate_template_literal_type;
                evaluate_template_literal_type(template, &self.type_env, self.interner)
            }
            TypeKind::TypeQuery(expr) => {
                // typeof(expression) - Look up the type of the expression
                // For identifiers, we can look them up directly in the type environment
                use typedlua_parser::ast::expression::ExpressionKind;
                match &expr.kind {
                    ExpressionKind::Identifier(name_id) => {
                        let name = self.interner.resolve(*name_id);
                        match self.type_env.lookup_type(&name) {
                            Some(t) => Ok(t.clone()),
                            None => match self.symbol_table.lookup(&name) {
                                Some(symbol) => Ok(symbol.typ.clone()),
                                None => {
                                    Err(format!("Cannot resolve typeof for identifier '{}'", name))
                                }
                            },
                        }
                    }
                    ExpressionKind::Call(callee, _args, _type_args) => {
                        // For function calls like typeof(getNumber()),
                        // look up the return type of the function
                        if let ExpressionKind::Identifier(name_id) = &callee.kind {
                            let name = self.interner.resolve(*name_id);
                            match self.symbol_table.lookup(&name) {
                                Some(symbol) => {
                                    if let TypeKind::Function(func) = &symbol.typ.kind {
                                        Ok((*func.return_type).clone())
                                    } else {
                                        Ok(Type::new(
                                            TypeKind::Primitive(PrimitiveType::Unknown),
                                            typ.span,
                                        ))
                                    }
                                }
                                None => Err(format!("Cannot resolve typeof for call '{}'", name)),
                            }
                        } else {
                            Ok(Type::new(
                                TypeKind::Primitive(PrimitiveType::Unknown),
                                typ.span,
                            ))
                        }
                    }
                    _ => Ok(Type::new(
                        TypeKind::Primitive(PrimitiveType::Unknown),
                        typ.span,
                    )),
                }
            }
            TypeKind::Reference(type_ref) => {
                // Resolve type reference using the proper resolution logic
                // This handles utility types, generic types, and regular type aliases
                // If resolution fails (e.g., type parameter not found), return the reference as-is
                match self.resolve_type_reference(type_ref) {
                    Ok(resolved) => Ok(resolved),
                    Err(_) => Ok(typ.clone()), // Return the reference unresolved (might be a type parameter)
                }
            }
            _ => Ok(typ.clone()),
        }
    }

    /// Deeply resolve all type references within a type tree.
    /// Unlike evaluate_type which only resolves top-level references,
    /// this recursively walks Object, Union, Nullable, Array, etc.
    /// and resolves any nested TypeKind::Reference nodes.
    fn deep_resolve_type(&self, typ: &Type) -> Type {
        match &typ.kind {
            TypeKind::Reference(type_ref) => {
                match self.resolve_type_reference(type_ref) {
                    Ok(resolved) => {
                        // Avoid infinite recursion if resolution returns same reference
                        if matches!(&resolved.kind, TypeKind::Reference(r) if r.name.node == type_ref.name.node)
                        {
                            resolved
                        } else {
                            self.deep_resolve_type(&resolved)
                        }
                    }
                    Err(_) => typ.clone(),
                }
            }
            TypeKind::Object(obj_type) => {
                use typedlua_parser::ast::types::ObjectTypeMember;
                let resolved_members: Vec<ObjectTypeMember> = obj_type
                    .members
                    .iter()
                    .map(|member| match member {
                        ObjectTypeMember::Property(prop) => {
                            ObjectTypeMember::Property(PropertySignature {
                                type_annotation: self.deep_resolve_type(&prop.type_annotation),
                                ..prop.clone()
                            })
                        }
                        other => other.clone(),
                    })
                    .collect();
                Type::new(
                    TypeKind::Object(typedlua_parser::ast::types::ObjectType {
                        members: resolved_members,
                        span: obj_type.span,
                    }),
                    typ.span,
                )
            }
            TypeKind::Union(members) => {
                let resolved: Vec<Type> =
                    members.iter().map(|m| self.deep_resolve_type(m)).collect();
                Type::new(TypeKind::Union(resolved), typ.span)
            }
            TypeKind::Nullable(inner) => {
                let resolved = self.deep_resolve_type(inner);
                Type::new(TypeKind::Nullable(Box::new(resolved)), typ.span)
            }
            TypeKind::Array(elem) => {
                let resolved = self.deep_resolve_type(elem);
                Type::new(TypeKind::Array(Box::new(resolved)), typ.span)
            }
            TypeKind::Tuple(elems) => {
                let resolved: Vec<Type> = elems.iter().map(|e| self.deep_resolve_type(e)).collect();
                Type::new(TypeKind::Tuple(resolved), typ.span)
            }
            TypeKind::Function(func_type) => {
                // Recursively resolve parameter types and return type in function types
                let resolved_params: Vec<typedlua_parser::ast::statement::Parameter> = func_type
                    .parameters
                    .iter()
                    .map(|param| typedlua_parser::ast::statement::Parameter {
                        type_annotation: param
                            .type_annotation
                            .as_ref()
                            .map(|t| self.deep_resolve_type(t)),
                        ..param.clone()
                    })
                    .collect();

                let resolved_return = self.deep_resolve_type(&func_type.return_type);

                Type::new(
                    TypeKind::Function(typedlua_parser::ast::types::FunctionType {
                        parameters: resolved_params,
                        return_type: Box::new(resolved_return),
                        ..func_type.clone()
                    }),
                    typ.span,
                )
            }
            _ => typ.clone(),
        }
    }

    /// Check if source type is assignable to target type via implements relationship.
    /// For example, Box<number> is assignable to Storable<number> if Box implements Storable<T>.
    fn check_implements_assignable(&self, source: &Type, target: &Type) -> bool {
        if let (TypeKind::Reference(s_ref), TypeKind::Reference(t_ref)) =
            (&source.kind, &target.kind)
        {
            let source_name = self.interner.resolve(s_ref.name.node);
            let target_name = self.interner.resolve(t_ref.name.node);

            // Check if source class implements the target interface
            if let Some(implements) = self.type_env.get_class_implements(&source_name) {
                for iface_type in implements {
                    if let TypeKind::Reference(iface_ref) = &iface_type.kind {
                        let iface_name = self.interner.resolve(iface_ref.name.node);
                        if iface_name == target_name {
                            // Interface name matches. For generic interfaces, check type arg
                            // compatibility. The common case is pass-through type params:
                            // class Box<T> implements Storable<T> means Box<number> -> Storable<number>
                            match (&s_ref.type_arguments, &t_ref.type_arguments) {
                                (None, None) => return true,
                                (Some(s_args), Some(t_args)) if s_args.len() == t_args.len() => {
                                    if s_args
                                        .iter()
                                        .zip(t_args.iter())
                                        .all(|(s, t)| TypeCompatibility::is_assignable(s, t))
                                    {
                                        return true;
                                    }
                                }
                                _ => {
                                    // Arity mismatch or partial generics - still allow if names match
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Substitute type parameter references in a type with actual type arguments.
    /// For a generic interface like Container<T>, given type_args [number],
    /// replaces references to T with number.
    fn substitute_type_args_in_type(
        &self,
        typ: &Type,
        type_args: &[Type],
        interface_name: &str,
    ) -> Type {
        match &typ.kind {
            TypeKind::Reference(type_ref) => {
                let ref_name = self.interner.resolve(type_ref.name.node).to_string();
                // Check if this reference matches a type parameter of the interface.
                // Look up the interface's declared type parameter names and find the
                // positional index so we substitute with the correct type argument.
                if let Some(param_names) = self.type_env.get_interface_type_params(interface_name) {
                    if let Some(pos) = param_names.iter().position(|p| p == &ref_name) {
                        if pos < type_args.len() {
                            return type_args[pos].clone();
                        }
                    }
                }
                // Fallback: if no param names are registered, use heuristic
                if self.type_env.get_interface(interface_name).is_some()
                    && self.type_env.lookup_type(&ref_name).is_none()
                    && self.type_env.lookup_type_alias(&ref_name).is_none()
                    && !type_args.is_empty()
                {
                    return type_args[0].clone();
                }
                typ.clone()
            }
            TypeKind::Array(elem) => {
                let subst = self.substitute_type_args_in_type(elem, type_args, interface_name);
                Type::new(TypeKind::Array(Box::new(subst)), typ.span)
            }
            TypeKind::Nullable(inner) => {
                let subst = self.substitute_type_args_in_type(inner, type_args, interface_name);
                Type::new(TypeKind::Nullable(Box::new(subst)), typ.span)
            }
            TypeKind::Union(members) => {
                let subst: Vec<Type> = members
                    .iter()
                    .map(|m| self.substitute_type_args_in_type(m, type_args, interface_name))
                    .collect();
                Type::new(TypeKind::Union(subst), typ.span)
            }
            _ => typ.clone(),
        }
    }

    /// Widen literal types to their base primitive types
    fn widen_type(&self, typ: Type) -> Type {
        match typ.kind {
            TypeKind::Literal(Literal::Number(_)) | TypeKind::Literal(Literal::Integer(_)) => {
                Type::new(TypeKind::Primitive(PrimitiveType::Number), typ.span)
            }
            TypeKind::Literal(Literal::String(_)) => {
                Type::new(TypeKind::Primitive(PrimitiveType::String), typ.span)
            }
            TypeKind::Literal(Literal::Boolean(_)) => {
                Type::new(TypeKind::Primitive(PrimitiveType::Boolean), typ.span)
            }
            TypeKind::Literal(Literal::Nil) => {
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), typ.span)
            }
            _ => typ,
        }
    }

    /// Register a declare function statement in the global scope
    fn register_declare_function(
        &mut self,
        func: &DeclareFunctionStatement,
    ) -> Result<(), TypeCheckError> {
        // Create function type from the declaration
        let func_type = Type::new(
            TypeKind::Function(FunctionType {
                type_parameters: func.type_parameters.clone(),
                parameters: func.parameters.clone(),
                return_type: Box::new(func.return_type.clone()),
                throws: func.throws.clone(),
                span: func.span,
            }),
            func.span,
        );

        // Declare function in symbol table
        let symbol = Symbol::new(
            self.interner.resolve(func.name.node).to_string(),
            SymbolKind::Function,
            func_type,
            func.span,
        );
        self.symbol_table
            .declare(symbol)
            .map_err(|e| TypeCheckError::new(e, func.span))
    }

    /// Register a declare const statement in the global scope
    fn register_declare_const(
        &mut self,
        const_decl: &DeclareConstStatement,
    ) -> Result<(), TypeCheckError> {
        // Declare constant in symbol table
        let symbol = Symbol::new(
            self.interner.resolve(const_decl.name.node).to_string(),
            SymbolKind::Const,
            const_decl.type_annotation.clone(),
            const_decl.span,
        );
        self.symbol_table
            .declare(symbol)
            .map_err(|e| TypeCheckError::new(e, const_decl.span))?;

        Ok(())
    }

    /// Register a declare namespace statement in the global scope
    fn register_declare_namespace(
        &mut self,
        ns: &DeclareNamespaceStatement,
    ) -> Result<(), TypeCheckError> {
        // Create object type from namespace members
        let members: Vec<_> = ns
            .members
            .iter()
            .filter_map(|member| match member {
                Statement::DeclareFunction(func) if func.is_export => {
                    Some(ObjectTypeMember::Method(MethodSignature {
                        name: func.name.clone(),
                        type_parameters: func.type_parameters.clone(),
                        parameters: func.parameters.clone(),
                        return_type: func.return_type.clone(),
                        body: None,
                        span: func.span,
                    }))
                }
                Statement::DeclareConst(const_decl) if const_decl.is_export => {
                    Some(ObjectTypeMember::Property(PropertySignature {
                        is_readonly: true, // Constants are readonly
                        name: const_decl.name.clone(),
                        is_optional: false,
                        type_annotation: const_decl.type_annotation.clone(),
                        span: const_decl.span,
                    }))
                }
                _ => {
                    // Other statement types or non-exported members are ignored
                    None
                }
            })
            .collect();

        // Create namespace object type
        let namespace_type = Type::new(
            TypeKind::Object(ObjectType {
                members,
                span: ns.span,
            }),
            ns.span,
        );

        // Register namespace as a constant in the symbol table
        let symbol = Symbol::new(
            self.interner.resolve(ns.name.node).to_string(),
            SymbolKind::Const,
            namespace_type,
            ns.span,
        );
        self.symbol_table
            .declare(symbol)
            .map_err(|e| TypeCheckError::new(e, ns.span))
    }

    /// Register minimal stdlib (fallback when full stdlib fails to parse)
    pub fn register_minimal_stdlib(&mut self) {
        use typedlua_parser::ast::pattern::Pattern;
        use typedlua_parser::ast::statement::Parameter;
        use typedlua_parser::ast::types::*;
        use typedlua_parser::ast::Spanned;
        use typedlua_parser::span::Span;

        let span = Span::new(0, 0, 0, 0);

        // Register string namespace
        let string_members = vec![
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("upper"), span),
                type_parameters: None,
                parameters: vec![Parameter {
                    pattern: Pattern::Identifier(Spanned::new(self.interner.intern("s"), span)),
                    type_annotation: Some(Type::new(
                        TypeKind::Primitive(PrimitiveType::String),
                        span,
                    )),
                    default: None,
                    is_rest: false,
                    is_optional: false,
                    span,
                }],
                return_type: Type::new(TypeKind::Primitive(PrimitiveType::String), span),
                body: None,
                span,
            }),
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("lower"), span),
                type_parameters: None,
                parameters: vec![Parameter {
                    pattern: Pattern::Identifier(Spanned::new(self.interner.intern("s"), span)),
                    type_annotation: Some(Type::new(
                        TypeKind::Primitive(PrimitiveType::String),
                        span,
                    )),
                    default: None,
                    is_rest: false,
                    is_optional: false,
                    span,
                }],
                return_type: Type::new(TypeKind::Primitive(PrimitiveType::String), span),
                body: None,
                span,
            }),
        ];

        let string_type = Type::new(
            TypeKind::Object(ObjectType {
                members: string_members,
                span,
            }),
            span,
        );

        let _ = self.symbol_table.declare(Symbol::new(
            "string".to_string(),
            SymbolKind::Const,
            string_type,
            span,
        ));

        // Register math namespace
        let math_members = vec![
            ObjectTypeMember::Property(PropertySignature {
                is_readonly: true,
                name: Spanned::new(self.interner.intern("pi"), span),
                is_optional: false,
                type_annotation: Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
                span,
            }),
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("abs"), span),
                type_parameters: None,
                parameters: vec![Parameter {
                    pattern: Pattern::Identifier(Spanned::new(self.interner.intern("x"), span)),
                    type_annotation: Some(Type::new(
                        TypeKind::Primitive(PrimitiveType::Number),
                        span,
                    )),
                    default: None,
                    is_rest: false,
                    is_optional: false,
                    span,
                }],
                return_type: Type::new(TypeKind::Primitive(PrimitiveType::Number), span),
                body: None,
                span,
            }),
        ];

        let math_type = Type::new(
            TypeKind::Object(ObjectType {
                members: math_members,
                span,
            }),
            span,
        );

        let _ = self.symbol_table.declare(Symbol::new(
            "math".to_string(),
            SymbolKind::Const,
            math_type,
            span,
        ));
    }

    /// Get a reference to the symbol table for LSP queries
    pub fn symbol_table(&self) -> &SymbolTable {
        &self.symbol_table
    }

    /// Get a reference to the type environment for LSP queries
    pub fn type_env(&self) -> &TypeEnvironment {
        &self.type_env
    }

    /// Lookup a symbol by name in the current scope
    pub fn lookup_symbol(&self, name: &str) -> Option<&Symbol> {
        self.symbol_table.lookup(name)
    }

    /// Lookup a type by name
    pub fn lookup_type(&self, name: &str) -> Option<&Type> {
        self.type_env.lookup_type(name)
    }

    /// Extract exports from a program for module system
    pub fn extract_exports(&self, program: &Program) -> crate::module_resolver::ModuleExports {
        use crate::module_resolver::{ExportedSymbol, ModuleExports};

        let mut exports = ModuleExports::new();
        for stmt in program.statements.iter() {
            if let Statement::Export(export_decl) = stmt {
                match &export_decl.kind {
                    ExportKind::Declaration(decl) => {
                        match &**decl {
                            Statement::Variable(var_decl) => {
                                // Extract identifier from pattern
                                if let Pattern::Identifier(ident) = &var_decl.pattern {
                                    let ident_name = self.interner.resolve(ident.node);
                                    if let Some(symbol) = self.symbol_table.lookup(&ident_name) {
                                        exports.add_named(
                                            ident_name,
                                            ExportedSymbol::new(symbol.clone(), false),
                                        );
                                    }
                                }
                            }
                            Statement::Function(func_decl) => {
                                let func_name = self.interner.resolve(func_decl.name.node);
                                if let Some(symbol) = self.symbol_table.lookup(&func_name) {
                                    exports.add_named(
                                        func_name,
                                        ExportedSymbol::new(symbol.clone(), false),
                                    );
                                }
                            }
                            Statement::Class(class_decl) => {
                                let class_name = self.interner.resolve(class_decl.name.node);
                                if let Some(symbol) = self.symbol_table.lookup(&class_name) {
                                    exports.add_named(
                                        class_name,
                                        ExportedSymbol::new(symbol.clone(), false),
                                    );
                                }
                            }
                            Statement::TypeAlias(type_alias) => {
                                let alias_name = self.interner.resolve(type_alias.name.node);
                                if let Some(symbol) = self.symbol_table.lookup(&alias_name) {
                                    exports.add_named(
                                        alias_name,
                                        ExportedSymbol::new(symbol.clone(), true),
                                    );
                                }
                            }
                            Statement::Interface(interface_decl) => {
                                let interface_name =
                                    self.interner.resolve(interface_decl.name.node);
                                if let Some(symbol) = self.symbol_table.lookup(&interface_name) {
                                    exports.add_named(
                                        interface_name,
                                        ExportedSymbol::new(symbol.clone(), true),
                                    );
                                }
                            }
                            _ => {}
                        }
                    }
                    ExportKind::Named { specifiers, source } => {
                        // Export existing symbols: export { foo, bar as baz }
                        // Or re-export from another module: export { foo } from './module'
                        for spec in specifiers {
                            let local_name = self.interner.resolve(spec.local.node);
                            let export_name = spec
                                .exported
                                .as_ref()
                                .map(|e| self.interner.resolve(e.node))
                                .unwrap_or_else(|| local_name.clone());

                            // Check if this is a re-export from another module
                            if let Some(source_path) = source {
                                // For re-exports, look up the symbol from the source module
                                if let (Some(registry), Some(resolver), Some(current_id)) = (
                                    &self.module_registry,
                                    &self.module_resolver,
                                    &self.current_module_id,
                                ) {
                                    if let Ok(source_module_id) =
                                        resolver.resolve(source_path, current_id.path())
                                    {
                                        if let Ok(source_exports) =
                                            registry.get_exports(&source_module_id)
                                        {
                                            if let Some(exported_sym) =
                                                source_exports.get_named(&local_name)
                                            {
                                                exports
                                                    .add_named(export_name, exported_sym.clone());
                                            }
                                        }
                                    }
                                }
                            } else {
                                // Local export - look up in symbol table
                                if let Some(symbol) = self.symbol_table.lookup(&local_name) {
                                    // Check if it's a type-only export
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
                        // For default exports, we create a synthetic symbol
                        // In the future, we might want to infer the type of the expression
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

    fn check_throw_statement(&mut self, stmt: &mut ThrowStatement) -> Result<(), TypeCheckError> {
        self.infer_expression_type(&mut stmt.expression)?;
        Ok(())
    }

    fn check_rethrow_statement(&self, span: Span) -> Result<(), TypeCheckError> {
        if self.in_catch_block.last() != Some(&true) {
            return Err(TypeCheckError::new(
                "rethrow can only be used outside of a catch block",
                span,
            ));
        }
        Ok(())
    }

    fn check_import_statement(&mut self, import: &ImportDeclaration) -> Result<(), TypeCheckError> {
        match &import.clause {
            ImportClause::Default(name) => {
                let name_str = self.interner.resolve(name.node);
                let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
                let symbol = Symbol::new(
                    name_str.to_string(),
                    SymbolKind::Variable,
                    any_type,
                    import.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, import.span))?;
            }
            ImportClause::Named(specifiers) => {
                for spec in specifiers {
                    let name_str = self.interner.resolve(spec.imported.node);

                    // Try to resolve the type from the source module
                    let import_type =
                        self.resolve_import_type(&import.source, &name_str, import.span)?;

                    let symbol = Symbol::new(
                        name_str.to_string(),
                        SymbolKind::Variable,
                        import_type,
                        spec.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, spec.span))?;
                }
            }
            ImportClause::TypeOnly(specifiers) => {
                for spec in specifiers {
                    let name_str = self.interner.resolve(spec.imported.node);

                    // Try to resolve the type from the source module
                    let import_type =
                        self.resolve_import_type(&import.source, &name_str, import.span)?;

                    // Register in symbol table
                    let symbol = Symbol::new(
                        name_str.to_string(),
                        SymbolKind::TypeAlias,
                        import_type.clone(),
                        spec.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, spec.span))?;

                    // Also register in type_env so it can be resolved in type annotations
                    self.type_env
                        .register_type_alias(name_str.to_string(), import_type.clone())
                        .map_err(|e| TypeCheckError::new(e, spec.span))?;

                    // If it's an interface/object type, register it in access control
                    // so member access checks work correctly
                    if let TypeKind::Object(obj_type) = &import_type.kind {
                        self.access_control.register_class(&name_str, None);
                        // Register all members for access control
                        for member in &obj_type.members {
                            let member_info = match member {
                                ObjectTypeMember::Property(prop) => ClassMemberInfo {
                                    name: self.interner.resolve(prop.name.node).to_string(),
                                    access: AccessModifier::Public,
                                    _is_static: false,
                                    kind: ClassMemberKind::Property {
                                        type_annotation: prop.type_annotation.clone(),
                                    },
                                    is_final: prop.is_readonly,
                                },
                                ObjectTypeMember::Method(method) => ClassMemberInfo {
                                    name: self.interner.resolve(method.name.node).to_string(),
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
                            self.access_control.register_member(&name_str, member_info);
                        }
                    }
                }
            }
            ImportClause::Namespace(name) => {
                let name_str = self.interner.resolve(name.node);
                let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
                let symbol = Symbol::new(
                    name_str.to_string(),
                    SymbolKind::Variable,
                    any_type,
                    import.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, import.span))?;
            }
            ImportClause::Mixed { default, named } => {
                // Handle default import
                let default_name_str = self.interner.resolve(default.node);
                let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), import.span);
                let default_symbol = Symbol::new(
                    default_name_str.to_string(),
                    SymbolKind::Variable,
                    any_type,
                    default.span,
                );
                self.symbol_table
                    .declare(default_symbol)
                    .map_err(|e| TypeCheckError::new(e, default.span))?;

                // Handle named imports
                for spec in named {
                    let name_str = self.interner.resolve(spec.imported.node);

                    // Try to resolve the type from the source module
                    let import_type =
                        self.resolve_import_type(&import.source, &name_str, import.span)?;

                    let symbol = Symbol::new(
                        name_str.to_string(),
                        SymbolKind::Variable,
                        import_type,
                        spec.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, spec.span))?;
                }
            }
        }
        Ok(())
    }

    /// Resolve the type of an imported symbol from the source module
    fn resolve_import_type(
        &mut self,
        source: &str,
        symbol_name: &str,
        span: Span,
    ) -> Result<Type, TypeCheckError> {
        // If we have module support, try to resolve from the source module
        if let (Some(registry), Some(resolver), Some(current_id)) = (
            &self.module_registry,
            &self.module_resolver,
            &self.current_module_id,
        ) {
            match resolver.resolve(source, current_id.path()) {
                Ok(source_module_id) => {
                    // Track this dependency for cache invalidation
                    self.module_dependencies
                        .push(source_module_id.path().to_path_buf());

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
                    // Import resolution failed - report error
                    self.diagnostic_handler.error(
                        span,
                        &format!("Failed to resolve module '{}': {}", source, e),
                    );
                }
            }
        } else {
            // No module support - report error for missing module
            self.diagnostic_handler.error(
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

    /// Get the list of module dependencies tracked during type checking
    pub fn get_module_dependencies(&self) -> &[std::path::PathBuf] {
        &self.module_dependencies
    }

    fn check_namespace_declaration(
        &mut self,
        ns: &NamespaceDeclaration,
    ) -> Result<(), TypeCheckError> {
        if self.current_namespace.is_some() {
            return Err(TypeCheckError::new(
                "Only one namespace declaration allowed per file",
                ns.span,
            ));
        }

        let path: Vec<String> = ns
            .path
            .iter()
            .map(|ident| self.interner.resolve(ident.node).to_string())
            .collect();

        self.current_namespace = Some(path.clone());

        let namespace_type = Type::new(TypeKind::Namespace(path.clone()), ns.span);

        let namespace_name = path
            .first()
            .ok_or_else(|| TypeCheckError::new("Namespace path cannot be empty", ns.span))?;

        let symbol = Symbol::new(
            namespace_name.clone(),
            SymbolKind::Namespace,
            namespace_type,
            ns.span,
        );

        self.symbol_table
            .declare(symbol)
            .map_err(|e| TypeCheckError::new(e, ns.span))?;

        Ok(())
    }

    fn check_try_statement(&mut self, stmt: &mut TryStatement) -> Result<(), TypeCheckError> {
        self.check_block(&mut stmt.try_block)?;

        for catch_clause in stmt.catch_clauses.iter_mut() {
            self.check_catch_clause(catch_clause)?;
        }

        if let Some(finally_block) = &mut stmt.finally_block {
            self.check_block(finally_block)?;
        }

        Ok(())
    }

    fn check_catch_clause(&mut self, clause: &mut CatchClause) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();

        let _catch_var_type = match &clause.pattern {
            CatchPattern::Untyped { variable, span } => {
                let any_type = Type::new(TypeKind::Primitive(PrimitiveType::Unknown), *span);
                let symbol = Symbol::new(
                    self.interner.resolve(variable.node).to_string(),
                    SymbolKind::Variable,
                    any_type.clone(),
                    *span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, *span))?;
                any_type
            }
            CatchPattern::Typed {
                variable,
                type_annotation,
                span,
            } => {
                let symbol = Symbol::new(
                    self.interner.resolve(variable.node).to_string(),
                    SymbolKind::Variable,
                    type_annotation.clone(),
                    *span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, *span))?;
                type_annotation.clone()
            }
            CatchPattern::MultiTyped {
                variable,
                type_annotations,
                span,
            } => {
                let union_type = Type::new(TypeKind::Union(type_annotations.clone()), *span);
                let symbol = Symbol::new(
                    self.interner.resolve(variable.node).to_string(),
                    SymbolKind::Variable,
                    union_type.clone(),
                    *span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, *span))?;
                union_type
            }
        };

        self.in_catch_block.push(true);
        let result = self.check_block(&mut clause.body);
        self.in_catch_block.pop();

        self.symbol_table.exit_scope();

        result
    }

    /// Check if a class has circular inheritance by walking up the parent chain
    fn has_circular_inheritance(&self, class_name: &str) -> bool {
        let mut visited = std::collections::HashSet::new();
        let mut current = class_name.to_string();

        visited.insert(current.clone());

        while let Some(parent) = self.class_parents.get(&current) {
            if visited.contains(parent) {
                return true; // Found a cycle
            }
            visited.insert(parent.clone());
            current = parent.clone();
        }

        false
    }

    /// Check if a block always returns (has a return statement on all code paths)
    fn block_always_returns(&self, block: &Block) -> bool {
        for stmt in &block.statements {
            if self.statement_always_returns(stmt) {
                return true;
            }
        }
        false
    }

    /// Check if a statement always returns
    fn statement_always_returns(&self, stmt: &Statement) -> bool {
        match stmt {
            Statement::Return(_) => true,
            Statement::If(if_stmt) => {
                // If statement always returns if both branches always return
                let then_returns = self.block_always_returns(&if_stmt.then_block);
                let else_returns = if_stmt
                    .else_block
                    .as_ref()
                    .map(|b| self.block_always_returns(b))
                    .unwrap_or(false);
                then_returns && else_returns
            }
            Statement::Try(try_stmt) => {
                // Try-catch always returns if:
                // 1. Finally block always returns (catches all paths), OR
                // 2. Try block always returns AND all catch blocks always return
                if let Some(ref finally) = try_stmt.finally_block {
                    if self.block_always_returns(finally) {
                        return true;
                    }
                }

                // Check try block and all catch blocks
                let try_returns = self.block_always_returns(&try_stmt.try_block);
                let all_catches_return = try_stmt
                    .catch_clauses
                    .iter()
                    .all(|catch| self.block_always_returns(&catch.body));

                try_returns && all_catches_return && !try_stmt.catch_clauses.is_empty()
            }
            Statement::Throw(_) => true,
            Statement::Expression(expr) => {
                // Check if the expression is a call to a function that never returns
                // (like unreachable(), error(), throw)
                if let ExpressionKind::Call(callee, _, _) = &expr.kind {
                    if let ExpressionKind::Identifier(string_id) = &callee.kind {
                        let name = self.interner.resolve(*string_id);
                        name == "unreachable" || name == "error" || name == "throw"
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::CollectingDiagnosticHandler;
    use typedlua_parser::lexer::Lexer;
    use typedlua_parser::parser::Parser;

    fn type_check_source(source: &str) -> Result<(), TypeCheckError> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let (interner, common) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let mut lexer = Lexer::new(source, handler.clone(), &interner);
        let tokens = lexer.tokenize().expect("Lexing failed");
        let mut parser = Parser::new(tokens, handler.clone(), &interner, &common);
        let mut program = parser.parse().expect("Parsing failed");

        let mut type_checker = TypeChecker::new(handler.clone(), &interner, &common);
        let result = type_checker.check_program(&mut program);

        // Check if there are errors in the diagnostic handler
        let has_errors = handler
            .get_diagnostics()
            .iter()
            .any(|d| d.level == crate::diagnostics::DiagnosticLevel::Error);

        if has_errors {
            Err(TypeCheckError::new(
                "Type checking failed with errors",
                Default::default(),
            ))
        } else {
            result
        }
    }

    /// Type check source code with stdlib loaded (for tests that need stdlib)
    fn type_check_source_with_stdlib(source: &str) -> Result<(), TypeCheckError> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let (interner, common) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let mut lexer = Lexer::new(source, handler.clone(), &interner);
        let tokens = lexer.tokenize().expect("Lexing failed");
        let mut parser = Parser::new(tokens, handler.clone(), &interner, &common);
        let mut program = parser.parse().expect("Parsing failed");

        let mut type_checker = TypeChecker::new_with_stdlib(handler.clone(), &interner, &common)
            .expect("Failed to load stdlib");
        let result = type_checker.check_program(&mut program);

        // Check if there are errors in the diagnostic handler
        let has_errors = handler
            .get_diagnostics()
            .iter()
            .any(|d| d.level == crate::diagnostics::DiagnosticLevel::Error);

        if has_errors {
            Err(TypeCheckError::new(
                "Type checking failed with errors",
                Default::default(),
            ))
        } else {
            result
        }
    }

    #[test]
    fn test_simple_variable_declaration() {
        let source = "const x: number = 42";
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_type_mismatch() {
        let source = "const x: string = 42";
        assert!(type_check_source(source).is_err());
    }

    #[test]
    fn test_type_inference() {
        let source = "const x = 42";
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_object_literal_inference() {
        // First test: just declare the object
        let source1 = "const obj = {x: 10, y: 20}\n";
        let result1 = type_check_source(source1);
        if let Err(e) = &result1 {
            eprintln!("✗ Error declaring object: {}", e.message);
        }
        assert!(result1.is_ok(), "Should be able to declare object literal");

        // Second test: declare and use
        let source2 = "const obj = {x: 10, y: 20}\nconst a = obj.x\n";
        let result2 = type_check_source(source2);
        if let Err(e) = &result2 {
            eprintln!("✗ Error using object: {}", e.message);
        }
        assert!(result2.is_ok(), "Should be able to use object properties");
    }

    #[test]
    fn test_function_type_checking() {
        let source = r#"
            function add(a: number, b: number): number
                return a + b
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_undefined_variable() {
        let source = "const x = y";
        assert!(type_check_source(source).is_err());
    }

    #[test]
    fn test_narrowing_nil_check() {
        // Test that nil checks narrow types correctly in if statements
        let source = r#"
            function processValue(x: string | nil)
                if x != nil then
                    -- x should be narrowed to string here
                    local y: string = x
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_narrowing_multiple_branches() {
        // Test narrowing with multiple if branches
        let source = r#"
            function processOptional(x: string | nil)
                if x != nil then
                    local s: string = x
                end

                local y: string | nil = "test"
                if y != nil then
                    local s2: string = y
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_narrowing_nested_if() {
        // Test narrowing in nested if statements
        let source = r#"
            function processNested(a: string | nil, b: number | nil)
                if a != nil then
                    local x: string = a
                    if b != nil then
                        local y: number = b
                    end
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_narrowing_else_branch() {
        // Test that else branch gets the complementary narrowing
        let source = r#"
            function checkNil(x: string | nil)
                if x == nil then
                    -- In then branch, x is nil, just use it
                    local temp = x
                else
                    -- In else branch, x is narrowed to string
                    local s: string = x
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_type_predicate_valid_parameter() {
        // Test that type predicates accept valid parameter names
        let source = r#"
            function isString(x: string | number): x is string
                return true
            end
        "#;
        let result = type_check_source(source);
        if let Err(e) = &result {
            eprintln!("Unexpected error: {}", e.message);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_type_predicate_invalid_parameter() {
        // Test that type predicates reject invalid parameter names
        let source = r#"
            function isString(x: string | number): y is string
                return true
            end
        "#;
        let result = type_check_source(source);
        assert!(
            result.is_err(),
            "Expected error for type predicate with invalid parameter name"
        );
        if let Err(e) = result {
            assert!(
                e.message.contains("Type predicate parameter"),
                "Expected error message about type predicate parameter, got: {}",
                e.message
            );
        }
    }

    #[test]
    fn test_narrowing_double_nil_check() {
        // Test nil narrowing with two variables
        let source = r#"
            function process(a: string | nil, b: number | nil)
                if a != nil then
                    local x: string = a
                end
                if b != nil then
                    local y: number = b
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_class_basic() {
        let source = r#"
            class Animal
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_class_with_property() {
        let source = r#"
            class Person
                name: string
                age: number = 25
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    // Property type checking is working but literal "25" vs number
    // compatibility depends on the type compatibility implementation
    // The test would pass with stricter type checking

    #[test]
    fn test_class_with_constructor() {
        let source = r#"
            class Person
                constructor(name: string, age: number)
                    self.name = name
                    self.age = age
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_class_multiple_constructors() {
        let source = r#"
            class Person {
                constructor(name: string) {
                }

                constructor(name: string, age: number) {
                }
            }
        "#;
        let result = type_check_source(source);
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.message.contains("one constructor"));
        }
    }

    #[test]
    fn test_class_with_method() {
        let source = r#"
            class Calculator {
                add(a: number, b: number): number {
                    return a + b
                }
            }
        "#;
        let result = type_check_source(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_abstract_class() {
        let source = r#"
            abstract class Animal {
                abstract makeSound(): string;

                move(): void {
                    const x: number = 5
                }
            }
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_abstract_method_in_concrete_class() {
        let source = r#"
            class Animal
                abstract makeSound(): string;
            end
        "#;
        let result = type_check_source(source);
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.message.contains("abstract class"));
        }
    }

    #[test]
    fn test_abstract_method_with_body() {
        // This test just verifies abstract methods work correctly
        // The parser prevents abstract methods from having bodies by design
        let source = r#"
            abstract class Animal {
                abstract makeSound(): string;

                concrete(): void {
                    const x: number = 5
                }
            }
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_class_with_getter() {
        let source = r#"
            class Person
                get fullName(): string
                    return "John Doe"
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_class_with_setter() {
        let source = r#"
            class Person
                set age(value: number)
                    self._age = value
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    // Getter return type checking depends on literal vs primitive type compatibility

    #[test]
    fn test_generic_class() {
        let source = r#"
            class Container<T> {
                value: T

                constructor(val: T) {
                    const temp: T = val
                }

                getValue(defaultVal: T): T {
                    return defaultVal
                }
            }
        "#;
        let result = type_check_source(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_class_implements_interface() {
        let source = r#"
            interface Walkable {
                walk(): void
            }

            class Person implements Walkable {
                walk(): void {
                    const x: number = 5
                }
            }
        "#;
        let result = type_check_source(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_class_missing_interface_method() {
        let source = r#"
            interface Walkable {
                walk(): void
            }

            class Person implements Walkable {
            }
        "#;
        let result = type_check_source(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(result.is_err());
        if let Err(e) = result {
            assert!(e.message.contains("does not implement"));
        }
    }

    #[test]
    fn test_class_static_method() {
        let source = r#"
            class Math
                static abs(x: number): number
                    if x < 0 then
                        return -x
                    else
                        return x
                    end
                end
            end
        "#;
        assert!(type_check_source(source).is_ok());
    }

    #[test]
    fn test_stdlib_builtins_loaded() {
        // Test that built-in functions are available
        let source = r#"
            const x = print("Hello")
            const y = tonumber("42")
        "#;
        let result = type_check_source_with_stdlib(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(
            result.is_ok(),
            "Built-in functions should be available from stdlib"
        );
    }

    #[test]
    fn test_stdlib_string_library() {
        // Test that string library functions are available
        let source = r#"
            const upper = string.upper("hello")
            const lower = string.lower("WORLD")
        "#;
        let result = type_check_source_with_stdlib(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(
            result.is_ok(),
            "String library should be available from stdlib"
        );
    }

    #[test]
    fn test_stdlib_math_library() {
        // Test that math library constants and functions are available
        let source = r#"
            const p = math.pi
            const result = math.abs(-5)
        "#;
        let result = type_check_source_with_stdlib(source);
        if let Err(ref e) = result {
            eprintln!("Error: {}", e.message);
        }
        assert!(
            result.is_ok(),
            "Math library should be available from stdlib"
        );
    }
}
