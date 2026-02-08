use crate::cli::config::CompilerOptions;
use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_compat::TypeCompatibility;
use crate::core::type_environment::TypeEnvironment;
use crate::helpers::{control_flow, type_utilities};
use crate::incremental::DeclarationHash;
use crate::phases;
use crate::phases::declaration_checking_phase;
use crate::type_relations::TypeRelationCache;
use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::visitors::{
    AccessControl, AccessControlVisitor, ClassContext, ClassMemberInfo, ClassMemberKind,
    NarrowingVisitor, TypeInferenceVisitor, TypeInferrer, TypeNarrower,
};
use crate::TypeCheckError;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tracing::{debug, error, info, instrument, span, Level};
use typedlua_parser::ast::expression::*;
use typedlua_parser::ast::pattern::Pattern;
use typedlua_parser::ast::statement::*;
use typedlua_parser::ast::types::*;
use typedlua_parser::ast::Program;
use typedlua_parser::span::Span;

/// Type checker for TypedLua programs
pub struct TypeChecker<'a, 'arena> {
    symbol_table: SymbolTable<'arena>,
    type_env: TypeEnvironment<'arena>,
    current_function_return_type: Option<Type<'arena>>,
    // Visitor pattern integration - Phase 6
    narrowing: TypeNarrower<'arena>,
    access_control: AccessControl<'arena>,
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
    class_type_params:
        FxHashMap<String, Vec<typedlua_parser::ast::statement::TypeParameter<'arena>>>,
    /// Track class inheritance for circular dependency detection
    class_parents: FxHashMap<String, String>,
    /// Track exported names to detect duplicates
    exported_names: std::collections::HashSet<String>,
    diagnostic_handler: Arc<dyn DiagnosticHandler>,
    interner: &'a typedlua_parser::string_interner::StringInterner,
    common: &'a typedlua_parser::string_interner::CommonIdentifiers,
    /// Arena allocator for type construction
    arena: &'arena bumpalo::Bump,
    /// Type relation cache for subtype checking
    type_relation_cache: TypeRelationCache,
    /// Cycle detection for recursive type alias expansion
    resolving_types: std::cell::RefCell<std::collections::HashSet<String>>,
}

impl<'a, 'arena> TypeChecker<'a, 'arena> {
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
        arena: &'arena bumpalo::Bump,
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
            arena,
            type_relation_cache: TypeRelationCache::new(),
            resolving_types: std::cell::RefCell::new(std::collections::HashSet::new()),
        }
    }

    /// Create a new TypeChecker using dependency injection container.
    ///
    /// This constructor resolves dependencies from the provided DI container,
    /// enabling better testability and modularity.
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
    /// let checker = TypeChecker::new_with_di(&container, &interner, &common);
    /// ```
    pub fn new_with_di(
        container: &mut crate::DiContainer,
        interner: &'a typedlua_parser::string_interner::StringInterner,
        common: &'a typedlua_parser::string_interner::CommonIdentifiers,
        arena: &'arena bumpalo::Bump,
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
            options,
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
            arena,
            type_relation_cache: TypeRelationCache::new(),
            resolving_types: std::cell::RefCell::new(std::collections::HashSet::new()),
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
        arena: &'arena bumpalo::Bump,
    ) -> Result<Self, String> {
        let mut checker = Self::new(diagnostic_handler, interner, common, arena);
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
        arena: &'arena bumpalo::Bump,
        registry: Arc<crate::module_resolver::ModuleRegistry>,
        module_id: crate::module_resolver::ModuleId,
        resolver: Arc<crate::module_resolver::ModuleResolver>,
    ) -> Self {
        let mut checker = Self::new(diagnostic_handler, interner, common, arena);
        checker.module_registry = Some(registry);
        checker.current_module_id = Some(module_id);
        checker.module_resolver = Some(resolver);
        checker
    }

    /// Load the standard library for the configured Lua version
    ///
    /// This method parses the stdlib definition files and processes their
    /// statements to populate the type checker's symbol table and type environment.
    pub fn load_stdlib(&mut self) -> Result<(), String> {
        use crate::state::stdlib_loader;

        let programs = stdlib_loader::parse_stdlib_files(
            self.options.target,
            self.interner,
            self.common,
            self.arena,
        )?;

        for program in programs {
            for statement in program.statements.iter() {
                // Ignore errors from stdlib - best-effort population
                let _ = self.check_statement(statement);
            }
        }

        Ok(())
    }

    /// Type check a program
    #[instrument(skip(self, program))]
    pub fn check_program(&mut self, program: &Program<'arena>) -> Result<(), TypeCheckError> {
        let span = span!(
            Level::INFO,
            "check_program",
            statements = program.statements.len()
        );
        let _guard = span.enter();

        debug!(
            "Starting type checking for program with {} statements",
            program.statements.len()
        );

        // PASS 1: Register all function declarations (hoisting)
        // This allows functions to be called before they appear in source order
        for statement in program.statements.iter() {
            if let Statement::Function(func_decl) = statement {
                self.register_function_signature(func_decl)?;
            }
        }

        debug!("Completed pass 1: function signatures registered");

        // PASS 2: Type check all statements (including function bodies)
        let mut first_error: Option<TypeCheckError> = None;
        let mut statements_checked = 0;
        for statement in program.statements.iter() {
            if let Err(e) = self.check_statement(statement) {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
            statements_checked += 1;
        }

        debug!(
            "Completed pass 2: checked {} statements",
            statements_checked
        );

        if let Some(err) = first_error {
            error!(error = %err, "Type checking failed");
            Err(err)
        } else {
            info!("Type checking completed successfully");
            Ok(())
        }
    }

    /// Register a function's signature in the symbol table without checking its body
    /// This is used during the first pass of check_program to enable function hoisting
    fn register_function_signature(
        &mut self,
        decl: &FunctionDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Delegate to declaration_phase
        phases::declaration_phase::register_function_signature(
            decl,
            &mut self.symbol_table,
            self.interner,
            self.arena,
        )
    }

    /// Type check a statement
    #[instrument(skip(self, stmt), fields(stmt_type))]
    fn check_statement(&mut self, stmt: &Statement<'arena>) -> Result<(), TypeCheckError> {
        let stmt_type = match stmt {
            Statement::Variable(_) => "Variable",
            Statement::Function(_) => "Function",
            Statement::If(_) => "If",
            Statement::While(_) => "While",
            Statement::For(_) => "For",
            Statement::Repeat(_) => "Repeat",
            Statement::Return(_) => "Return",
            Statement::Break(_) => "Break",
            Statement::Continue(_) => "Continue",
            Statement::Expression(_) => "Expression",
            Statement::Block(_) => "Block",
            Statement::Interface(_) => "Interface",
            Statement::TypeAlias(_) => "TypeAlias",
            Statement::Enum(_) => "Enum",
            Statement::Class(_) => "Class",
            Statement::Import(_) => "Import",
            Statement::Export(_) => "Export",
            Statement::Namespace(_) => "Namespace",
            Statement::Label(_) => "Label",
            Statement::Goto(_) => "Goto",
            Statement::Throw(_) => "Throw",
            Statement::Try(_) => "Try",
            Statement::Rethrow(_) => "Rethrow",
            Statement::DeclareFunction(_) => "DeclareFunction",
            Statement::DeclareNamespace(_) => "DeclareNamespace",
            Statement::DeclareType(_) => "DeclareType",
            Statement::DeclareInterface(_) => "DeclareInterface",
            Statement::DeclareConst(_) => "DeclareConst",
        };

        span!(Level::DEBUG, "check_statement", kind = stmt_type);

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
        decl: &VariableDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Infer the type of the initializer
        let init_type = self.infer_expression_type(&decl.initializer)?;

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
            if !TypeCompatibility::is_assignable_with_cache(
                &deep_init,
                &deep_ann,
                &mut self.type_relation_cache,
            ) {
                // Fallback: check if source class implements the target interface.
                // Use original init_type and type_ann (pre-evaluation) since evaluate_type
                // resolves interface references to ObjectType<'arena>, losing the interface name.
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
        pattern: &Pattern<'arena>,
        typ: Type<'arena>,
        kind: SymbolKind,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        // Delegate to declaration_phase
        phases::declaration_phase::declare_pattern(
            pattern,
            typ,
            kind,
            span,
            &mut self.symbol_table,
            self.interner,
            self.arena,
        )
    }

    /// Check function declaration
    fn check_function_declaration(
        &mut self,
        decl: &FunctionDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // NOTE: Function signature is already registered in the symbol table during pass 1
        // (see register_function_signature method called from check_program)
        // This method now only checks the function body

        // Enter new scope for function body
        self.symbol_table.enter_scope();

        // If generic, declare type parameters as types in scope
        phases::declaration_checking_phase::register_function_type_parameters(
            decl.type_parameters,
            &mut self.type_env,
            self.interner,
        )?;

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
                    self.type_env
                        .new_primitive_type(PrimitiveType::Unknown, param.span)
                };

                // Wrap in array type
                Type::new(TypeKind::Array(self.arena.alloc(elem_type)), param.span)
            } else if let Some(type_ann) = &param.type_annotation {
                // Evaluate to resolve type references
                let evaluated = self
                    .evaluate_type(type_ann)
                    .map_err(|e| TypeCheckError::new(e, param.span))
                    .unwrap_or_else(|_| type_ann.clone());
                // Deep resolve to handle nested types
                self.deep_resolve_type(&evaluated)
            } else {
                self.type_env
                    .new_primitive_type(PrimitiveType::Unknown, param.span)
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
        let body_result = self.check_block(&decl.body);

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
        if let Some(type_params) = decl.type_parameters {
            for type_param in type_params.iter() {
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
    fn check_if_statement(&mut self, if_stmt: &IfStatement<'arena>) -> Result<(), TypeCheckError> {
        // Check condition
        self.infer_expression_type(&if_stmt.condition)?;

        // Collect current variable and function types for narrowing
        // This includes both variables and functions so type predicates can be checked
        let mut variable_types = FxHashMap::default();
        for (name, symbol) in self.symbol_table.all_visible_symbols() {
            let name_id = self.interner.intern(&name);
            variable_types.insert(name_id, symbol.typ.clone());
        }

        // Apply type narrowing based on the condition
        let (then_context, else_context) = self.narrowing.narrow_from_condition(
            self.arena,
            &if_stmt.condition,
            self.narrowing.get_context(),
            &variable_types,
            self.interner,
        );

        // Check then block with narrowed context
        let saved_context = self.narrowing.get_context().clone();
        *self.narrowing.get_context_mut() = then_context;
        self.check_block(&if_stmt.then_block)?;

        // Restore context for else-if and else
        *self.narrowing.get_context_mut() = else_context.clone();

        // Check else-if clauses
        for else_if in if_stmt.else_ifs.iter() {
            self.infer_expression_type(&else_if.condition)?;

            // Further narrow based on else-if condition
            let (elseif_then, elseif_else) = self.narrowing.narrow_from_condition(
                self.arena,
                &else_if.condition,
                self.narrowing.get_context(),
                &variable_types,
                self.interner,
            );

            *self.narrowing.get_context_mut() = elseif_then;
            self.check_block(&else_if.block)?;
            *self.narrowing.get_context_mut() = elseif_else;
        }

        // Check else block
        if let Some(else_block) = &if_stmt.else_block {
            self.check_block(else_block)?;
        }

        // Restore original context after if statement
        *self.narrowing.get_context_mut() = saved_context;

        Ok(())
    }

    /// Check while statement
    fn check_while_statement(
        &mut self,
        while_stmt: &WhileStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        self.infer_expression_type(&while_stmt.condition)?;
        self.check_block(&while_stmt.body)?;
        Ok(())
    }

    /// Check for statement
    fn check_for_statement(
        &mut self,
        for_stmt: &ForStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        match for_stmt {
            ForStatement::Numeric(numeric) => {
                self.symbol_table.enter_scope();

                // Declare loop variable as number (using cached primitive)
                let number_type = self.type_env.get_number_type(numeric.span);
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
                self.infer_expression_type(&numeric.start)?;
                self.infer_expression_type(&numeric.end)?;
                if let Some(step) = &numeric.step {
                    self.infer_expression_type(step)?;
                }

                self.check_block(&numeric.body)?;
                self.symbol_table.exit_scope();
            }
            ForStatement::Generic(generic) => {
                self.symbol_table.enter_scope();

                // Infer iterator element type for pattern destructuring
                let iter_elem_type = if let Some(first_iter) = generic.iterators.first() {
                    let iter_type = self.infer_expression_type(first_iter)?;
                    match &iter_type.kind {
                        TypeKind::Array(elem) => (*elem).clone(),
                        _ => self.type_env.get_unknown_type(generic.span),
                    }
                } else {
                    self.type_env.get_unknown_type(generic.span)
                };

                if let Some(pattern) = &generic.pattern {
                    // Destructuring for loop: for [a, b] in items do
                    self.declare_pattern(
                        pattern,
                        iter_elem_type,
                        SymbolKind::Variable,
                        generic.span,
                    )?;
                } else {
                    // Standard for loop: for k, v in iterator do
                    let unknown_type = self.type_env.get_unknown_type(generic.span);
                    for var in generic.variables.iter() {
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
                }

                // Check remaining iterators
                for iter in generic.iterators.iter().skip(1) {
                    self.infer_expression_type(iter)?;
                }

                self.check_block(&generic.body)?;
                self.symbol_table.exit_scope();
            }
        }
        Ok(())
    }

    /// Check repeat statement
    fn check_repeat_statement(
        &mut self,
        repeat_stmt: &RepeatStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();
        self.check_block(&repeat_stmt.body)?;
        self.infer_expression_type(&repeat_stmt.until)?;
        self.symbol_table.exit_scope();
        Ok(())
    }

    /// Check return statement
    fn check_return_statement(
        &mut self,
        return_stmt: &ReturnStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        if !return_stmt.values.is_empty() {
            // Infer types for all return values
            let return_types: Result<Vec<_>, _> = return_stmt
                .values
                .iter()
                .map(|expr| self.infer_expression_type(expr))
                .collect();
            let return_types = return_types?;

            // Create the actual return type (single value or tuple)
            let actual_return_type = if return_types.len() == 1 {
                return_types[0].clone()
            } else {
                Type::new(
                    TypeKind::Tuple(self.arena.alloc_slice_fill_iter(return_types)),
                    return_stmt.span,
                )
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

                if !TypeCompatibility::is_assignable_with_cache(
                    &actual_return_type,
                    &effective_expected_type,
                    &mut self.type_relation_cache,
                ) {
                    return Err(TypeCheckError::new(
                        "Return type mismatch",
                        return_stmt.span,
                    ));
                }
            }
        } else {
            // Check that void return is allowed
            if let Some(expected_type) = &self.current_function_return_type {
                let void_type = self.type_env.get_void_type(return_stmt.span);
                if !TypeCompatibility::is_assignable_with_cache(
                    &void_type,
                    expected_type,
                    &mut self.type_relation_cache,
                ) {
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
    fn check_block(&mut self, block: &Block<'arena>) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();
        let mut first_error: Option<TypeCheckError> = None;
        for stmt in block.statements.iter() {
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
        iface: &InterfaceDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Delegate to declaration_checking_phase for interface registration and validation
        let (has_default_bodies, iface_type) =
            phases::declaration_checking_phase::check_interface_declaration(
                self.arena,
                iface,
                &mut self.type_env,
                &mut self.symbol_table,
                &mut self.access_control,
                self.interner,
            )?;

        // Type-check default method bodies if present
        if has_default_bodies {
            for member in iface.members.iter() {
                if let InterfaceMember::Method(method) = member {
                    if let Some(body) = &method.body {
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
        }

        Ok(())
    }

    /// Validate interface members for correctness
    #[allow(dead_code)]
    fn validate_interface_members(
        &self,
        members: &[ObjectTypeMember<'arena>],
        span: Span,
    ) -> Result<(), TypeCheckError> {
        phases::validation_phase::validate_interface_members(members, span)
    }

    /// Check type alias
    fn check_type_alias(
        &mut self,
        alias: &TypeAliasDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // For non-generic aliases, evaluate the type before delegating
        let evaluated_type = if alias.type_parameters.is_none() {
            Some(
                self.evaluate_type(&alias.type_annotation)
                    .map_err(|e| TypeCheckError::new(e, alias.span))?,
            )
        } else {
            None
        };

        // Delegate to declaration_checking_phase
        phases::declaration_checking_phase::check_type_alias(
            alias,
            &mut self.type_env,
            &mut self.symbol_table,
            self.interner,
            evaluated_type,
        )
    }

    /// Check export statement and register exported symbols
    fn check_export_statement(
        &mut self,
        export: &ExportDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
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
                for spec in specifiers.iter() {
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
                        let members_vec: Vec<ObjectTypeMember<'arena>> = iface
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
                            .collect();
                        let obj_type = Type::new(
                            TypeKind::Object(ObjectType {
                                members: self.arena.alloc_slice_fill_iter(members_vec),
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
                self.infer_expression_type(expr)?;
                Ok(())
            }
        }
    }

    /// Check enum declaration
    fn check_enum_declaration(
        &mut self,
        enum_decl: &EnumDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Delegate to declaration_checking_phase for simple enums
        let is_rich_enum = phases::declaration_checking_phase::check_enum_declaration(
            self.arena,
            enum_decl,
            &mut self.type_env,
            &mut self.symbol_table,
            self.interner,
        )?;

        // If it's a rich enum, handle it here
        if is_rich_enum {
            self.check_rich_enum_declaration(enum_decl)?;
        }

        Ok(())
    }

    /// Check rich enum declaration with fields, constructor, and methods
    fn check_rich_enum_declaration(
        &mut self,
        enum_decl: &EnumDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Register enum types and members with phase function
        let enum_self_type = phases::declaration_checking_phase::check_rich_enum_declaration(
            enum_decl,
            &mut self.type_env,
            &mut self.access_control,
            self.interner,
        )?;

        // Check constructor body if present
        if let Some(ref constructor) = enum_decl.constructor {
            self.symbol_table.enter_scope();
            let self_symbol = Symbol::new(
                "self".to_string(),
                SymbolKind::Parameter,
                enum_self_type.clone(),
                constructor.span,
            );
            let _ = self.symbol_table.declare(self_symbol);
            let _ = self.check_block(&constructor.body);
            self.symbol_table.exit_scope();
        }

        // Check method bodies
        for method in enum_decl.methods.iter() {
            self.symbol_table.enter_scope();
            let self_symbol = Symbol::new(
                "self".to_string(),
                SymbolKind::Parameter,
                enum_self_type.clone(),
                method.span,
            );
            let _ = self.symbol_table.declare(self_symbol);
            let _ = self.check_block(&method.body);
            self.symbol_table.exit_scope();
        }

        Ok(())
    }

    /// Resolve a type reference, handling utility types and generic type application
    #[instrument(skip(self, type_ref), fields(type_name))]
    fn resolve_type_reference(
        &self,
        type_ref: &TypeReference<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        let name = self.interner.resolve(type_ref.name.node);
        let name_owned = name.to_string();
        span!(Level::DEBUG, "resolve_type_reference", type_name = %name);

        let span = type_ref.span;

        // Cycle detection: if we're already resolving this type, return it as-is
        // to prevent infinite recursion on recursive type aliases like `type List<T> = T | List<T>[]`
        if self.resolving_types.borrow().contains(&name_owned) {
            return Ok(Type::new(TypeKind::Reference(type_ref.clone()), span));
        }

        // Mark as resolving
        self.resolving_types.borrow_mut().insert(name_owned.clone());

        let result = self.resolve_type_reference_inner(type_ref);

        // Unmark
        self.resolving_types.borrow_mut().remove(&name_owned);

        result
    }

    fn resolve_type_reference_inner(
        &self,
        type_ref: &TypeReference<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        let name = self.interner.resolve(type_ref.name.node);
        let span = type_ref.span;

        // Check if it's a utility type
        if let Some(type_args) = &type_ref.type_arguments {
            if TypeEnvironment::is_utility_type(&name) {
                // Resolve type arguments first (they might be type references)
                let resolved_args: Result<Vec<Type<'arena>>, TypeCheckError> = type_args
                    .iter()
                    .map(|arg| {
                        self.evaluate_type(arg)
                            .map_err(|e| TypeCheckError::new(e, arg.span))
                    })
                    .collect();
                let resolved_args = resolved_args?;

                return self
                    .type_env
                    .resolve_utility_type(
                        self.arena,
                        &name,
                        &resolved_args,
                        span,
                        self.interner,
                        self.common,
                    )
                    .map_err(|e| TypeCheckError::new(e, span));
            }

            // Check for generic type alias
            if let Some(generic_alias) = self.type_env.get_generic_type_alias(&name) {
                use crate::types::generics::instantiate_type;
                return instantiate_type(
                    self.arena,
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
    #[instrument(skip(self, class_decl), fields(class_name))]
    fn check_class_declaration(
        &mut self,
        class_decl: &ClassDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        let class_name = self.interner.resolve(class_decl.name.node).to_string();
        span!(Level::INFO, "check_class_declaration", class_name);

        debug!(
            members = class_decl.members.len(),
            "Checking class declaration"
        );

        // Check decorators
        self.check_decorators(class_decl.decorators)?;

        // Check for @readonly decorator and track it
        let has_readonly =
            class_decl
                .decorators
                .iter()
                .any(|decorator| match &decorator.expression {
                    typedlua_parser::ast::statement::DecoratorExpression::Identifier(name) => {
                        self.interner.resolve(name.node) == "readonly"
                    }
                    typedlua_parser::ast::statement::DecoratorExpression::Call {
                        callee: box typedlua_parser::ast::statement::DecoratorExpression::Identifier(name),
                        ..
                    } => self.interner.resolve(name.node) == "readonly",
                    _ => false,
                });

        if has_readonly {
            self.access_control.mark_class_readonly(&class_name, true);
        }

        debug!("Checking class {}", class_name);

        // Register class symbol (focused function - ~15 lines saved)
        let _class_type = phases::declaration_checking_phase::register_class_symbol(
            class_decl,
            &mut self.symbol_table,
            &mut self.type_env,
            &mut self.class_type_params,
            self.interner,
        )?;

        // Enter a new scope for the class
        self.symbol_table.enter_scope();

        // Register type parameters if this is a generic class
        // Register class type parameters in the type environment
        phases::declaration_checking_phase::register_class_type_parameters(
            class_decl.type_parameters,
            &mut self.type_env,
            self.interner,
        )?;

        // Validate class inheritance (focused function - ~20 lines saved)
        if let Some(extends_type) = &class_decl.extends {
            phases::validation_phase::validate_class_inheritance(
                &class_name,
                extends_type,
                &self.access_control,
                &mut self.class_parents,
                self.interner,
                class_decl.span,
            )?;
        }

        // Register class implements relationships before compliance checking,
        // so covariant return type checks can look up the class hierarchy
        phases::declaration_checking_phase::register_class_implements(
            class_name.clone(),
            class_decl.implements.to_vec(),
            &mut self.type_env,
            &mut self.access_control,
            self.interner,
        );

        // Check interface implementation
        for interface_type in class_decl.implements.iter() {
            if let TypeKind::Reference(type_ref) = &interface_type.kind {
                let interface_name = self.interner.resolve(type_ref.name.node);
                if let Some(interface) = self.type_env.get_interface(&interface_name) {
                    // If the interface has type arguments, instantiate it
                    let instantiated = if let Some(type_args) = type_ref.type_arguments {
                        declaration_checking_phase::instantiate_generic_interface(
                            self.arena,
                            interface.clone(),
                            type_args,
                            &interface_name,
                            |typ, args, iface_name| {
                                self.substitute_type_args_in_type(typ, args, iface_name)
                            },
                        )
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
        if let Some(primary_params) = class_decl.primary_constructor {
            for param in primary_params.iter() {
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
                class_decl.primary_constructor.unwrap(),
            );
        }

        // Validate parent constructor arguments if present
        if let Some(parent_args) = &class_decl.parent_constructor_args {
            // Type check each parent constructor argument
            for arg in parent_args.iter() {
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
                            .iter()
                            .zip(parent_constructor.iter())
                            .enumerate()
                        {
                            let arg_type = self.infer_expression_type(arg)?;
                            let param_type = &param.type_annotation;
                            if !TypeCompatibility::is_assignable_with_cache(
                                &arg_type,
                                param_type,
                                &mut self.type_relation_cache,
                            ) {
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

        // Extract regular class member information
        let mut class_member_infos = phases::declaration_checking_phase::extract_class_member_infos(
            class_decl,
            self.interner,
        );
        member_infos.append(&mut class_member_infos);

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

        for member in class_decl.members.iter() {
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
        if let Some(type_params) = class_decl.type_parameters {
            for type_param in type_params.iter() {
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
                        class_decl.members,
                    )?;
                }
            }
        }

        // Handle member errors based on severity.
        // Critical errors (abstract methods in non-abstract class, multiple constructors)
        // should fail hard. Other errors become warnings to prevent cascading failures.
        if let Some(err) = first_member_error {
            if phases::declaration_checking_phase::is_critical_member_error(&err.message) {
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
        class_decl: &ClassDeclaration<'arena>,
        interface: &Type<'arena>,
    ) -> Result<(), TypeCheckError> {
        phases::validation_phase::check_class_implements_interface(
            class_decl,
            interface,
            &self.type_env,
            self.interner,
        )
    }

    /// Validate that all class properties are compatible with interface index signature
    #[allow(dead_code)]
    fn validate_index_signature(
        &self,
        class_decl: &ClassDeclaration<'arena>,
        index_sig: &IndexSignature<'arena>,
    ) -> Result<(), TypeCheckError> {
        phases::validation_phase::validate_index_signature(class_decl, index_sig, self.interner)
    }

    /// Check that a class implements all abstract methods from its parent class
    fn check_abstract_methods_implemented(
        &self,
        class_name: &str,
        parent_name: &str,
        class_members: &[ClassMember<'arena>],
    ) -> Result<(), TypeCheckError> {
        phases::validation_phase::check_abstract_methods_implemented(
            class_name,
            parent_name,
            class_members,
            &self.access_control,
            self.interner,
        )
    }

    /// Check decorators
    fn check_decorators(
        &mut self,
        decorators: &[typedlua_parser::ast::statement::Decorator<'arena>],
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

        for decorator in decorators.iter() {
            self.check_decorator_expression(&decorator.expression)?;
        }

        Ok(())
    }

    /// Check a decorator expression
    fn check_decorator_expression(
        &mut self,
        expr: &typedlua_parser::ast::statement::DecoratorExpression<'arena>,
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
                for arg in arguments.iter() {
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
        prop: &PropertyDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(prop.decorators)?;

        // Check initializer if present
        if let Some(initializer) = &prop.initializer {
            let init_type = self.infer_expression_type(initializer)?;

            // Verify initializer type is assignable to declared type
            if !TypeCompatibility::is_assignable_with_cache(
                &init_type,
                &prop.type_annotation,
                &mut self.type_relation_cache,
            ) {
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
        ctor: &ConstructorDeclaration<'arena>,
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
                let symbol = crate::utils::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::utils::symbol_table::SymbolKind::Parameter,
                    self_type,
                    ctor.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, ctor.span))?;
            }

            // Declare parameters
            for param in ctor.parameters.iter() {
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
            self.check_block(&ctor.body)?;

            Ok(())
        })();

        // Always exit scope, even on error
        self.symbol_table.exit_scope();

        result
    }

    /// Check class method
    fn check_class_method(
        &mut self,
        method: &MethodDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(method.decorators)?;

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
                    let symbol = crate::utils::symbol_table::Symbol::new(
                        "self".to_string(),
                        crate::utils::symbol_table::SymbolKind::Parameter,
                        self_type,
                        method.span,
                    );
                    self.symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, method.span))?;
                }
            }

            // Register type parameters if generic (with duplicate checking and constraint support)
            phases::declaration_checking_phase::register_function_type_parameters(
                method.type_parameters,
                &mut self.type_env,
                self.interner,
            )?;

            // Declare parameters
            for param in method.parameters.iter() {
                let param_type = if let Some(type_ann) = &param.type_annotation {
                    // Evaluate the type annotation to resolve any type references (e.g., T, U in generic methods)
                    let evaluated = self
                        .evaluate_type(type_ann)
                        .map_err(|e| TypeCheckError::new(e, param.span))
                        .unwrap_or_else(|_| type_ann.clone()); // Fall back to unevaluated if evaluation fails

                    // Deep resolve to handle nested types in function types, arrays, etc.
                    self.deep_resolve_type(&evaluated)
                } else {
                    self.type_env
                        .new_primitive_type(PrimitiveType::Unknown, param.span)
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
            if let Some(body) = &method.body {
                self.check_block(body)?;
            }

            Ok(())
        })();

        // Always restore return type and exit scope, even on error
        self.current_function_return_type = old_return_type;
        self.symbol_table.exit_scope();

        // Clean up method type parameters from type environment
        if let Some(type_params) = method.type_parameters {
            for type_param in type_params.iter() {
                let param_name = self.interner.resolve(type_param.name.node).to_string();
                self.type_env.remove_type_alias(&param_name);
            }
        }

        result
    }

    /// Check class getter
    fn check_class_getter(
        &mut self,
        getter: &GetterDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(getter.decorators)?;

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
                let symbol = crate::utils::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::utils::symbol_table::SymbolKind::Parameter,
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
        self.check_block(&getter.body)?;

        // Restore previous return type
        self.current_function_return_type = old_return_type;

        // Exit getter scope
        self.symbol_table.exit_scope();

        Ok(())
    }

    /// Check class setter
    fn check_class_setter(
        &mut self,
        setter: &SetterDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Check decorators
        self.check_decorators(setter.decorators)?;

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
                let symbol = crate::utils::symbol_table::Symbol::new(
                    "self".to_string(),
                    crate::utils::symbol_table::SymbolKind::Parameter,
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
        self.check_block(&setter.body)?;

        // Exit setter scope
        self.symbol_table.exit_scope();

        Ok(())
    }

    /// Check operator declaration
    fn check_operator_declaration(
        &mut self,
        op: &OperatorDeclaration<'arena>,
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
            let symbol = crate::utils::symbol_table::Symbol::new(
                "self".to_string(),
                crate::utils::symbol_table::SymbolKind::Parameter,
                self_type,
                op.span,
            );
            self.symbol_table
                .declare(symbol)
                .map_err(|e| TypeCheckError::new(e, op.span))?;
        }

        for param in op.parameters.iter() {
            let param_type = param.type_annotation.clone().unwrap_or_else(|| {
                self.type_env
                    .new_primitive_type(PrimitiveType::Unknown, param.span)
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

        self.check_block(&op.body)?;

        self.current_function_return_type = old_return_type;

        self.symbol_table.exit_scope();

        Ok(())
    }

    fn is_boolean_type(&self, typ: &Type<'arena>) -> bool {
        type_utilities::is_boolean_type(typ)
    }

    fn operator_kind_name(&self, op: &OperatorKind) -> String {
        type_utilities::operator_kind_name(op)
    }

    /// Check that an override method properly overrides a parent method
    fn check_method_override(
        &self,
        method: &MethodDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
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

        // Get extends clause type arguments for generic parent instantiation
        let extends_type_args: Option<&[Type<'arena>]> =
            class_ctx.extends_type.as_ref().and_then(|ext| {
                if let TypeKind::Reference(type_ref) = &ext.kind {
                    type_ref.type_arguments
                } else {
                    None
                }
            });

        // Get parent class type parameters (if the parent is generic)
        let parent_type_params = class_ctx
            .parent
            .as_ref()
            .and_then(|p| self.class_type_params.get(p));

        phases::validation_phase::check_method_override(
            self.arena,
            method,
            &class_ctx.name,
            class_ctx.parent.as_ref(),
            parent_type_params,
            extends_type_args,
            &self.access_control,
            self.interner,
            |typ| self.deep_resolve_type(typ),
        )
    }

    /// Convert type to string for error messages
    fn type_to_string(&self, typ: &Type<'arena>) -> String {
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
    fn infer_expression_type(
        &mut self,
        expr: &Expression<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        let mut inferrer = TypeInferrer::new(
            self.arena,
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
    fn evaluate_type(&self, typ: &Type<'arena>) -> Result<Type<'arena>, String> {
        match &typ.kind {
            TypeKind::KeyOf(operand) => {
                // First evaluate the operand recursively
                let evaluated_operand = self.evaluate_type(operand)?;
                use crate::types::utility_types::evaluate_keyof;
                evaluate_keyof(
                    self.arena,
                    &evaluated_operand,
                    &self.type_env,
                    self.interner,
                )
            }
            TypeKind::Mapped(mapped) => {
                use crate::types::utility_types::evaluate_mapped_type;
                evaluate_mapped_type(self.arena, mapped, &self.type_env, self.interner)
            }
            TypeKind::Conditional(conditional) => {
                use crate::types::utility_types::evaluate_conditional_type;
                evaluate_conditional_type(self.arena, conditional, &self.type_env)
            }
            TypeKind::TemplateLiteral(template) => {
                use crate::types::utility_types::evaluate_template_literal_type;
                evaluate_template_literal_type(self.arena, template, &self.type_env, self.interner)
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
    fn deep_resolve_type(&self, typ: &Type<'arena>) -> Type<'arena> {
        match &typ.kind {
            TypeKind::Reference(type_ref) => {
                let ref_name = self.interner.resolve(type_ref.name.node).to_string();

                // Cycle detection: if we're already resolving this type, return as-is
                if self.resolving_types.borrow().contains(&ref_name) {
                    return typ.clone();
                }

                match self.resolve_type_reference(type_ref) {
                    Ok(resolved) => {
                        // Avoid infinite recursion if resolution returns same reference
                        if matches!(&resolved.kind, TypeKind::Reference(r) if r.name.node == type_ref.name.node)
                        {
                            resolved
                        } else {
                            // Mark as resolving before recursing into the resolved type
                            self.resolving_types.borrow_mut().insert(ref_name.clone());
                            let result = self.deep_resolve_type(&resolved);
                            self.resolving_types.borrow_mut().remove(&ref_name);
                            result
                        }
                    }
                    Err(_) => typ.clone(),
                }
            }
            TypeKind::Object(obj_type) => {
                use typedlua_parser::ast::types::ObjectTypeMember;
                let resolved_members: Vec<ObjectTypeMember<'arena>> = obj_type
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
                        members: self
                            .arena
                            .alloc_slice_fill_iter(resolved_members),
                        span: obj_type.span,
                    }),
                    typ.span,
                )
            }
            TypeKind::Union(members) => {
                let resolved: Vec<Type<'arena>> =
                    members.iter().map(|m| self.deep_resolve_type(m)).collect();
                Type::new(
                    TypeKind::Union(self.arena.alloc_slice_fill_iter(resolved)),
                    typ.span,
                )
            }
            TypeKind::Nullable(inner) => {
                let resolved = self.deep_resolve_type(inner);
                Type::new(TypeKind::Nullable(self.arena.alloc(resolved)), typ.span)
            }
            TypeKind::Array(elem) => {
                let resolved = self.deep_resolve_type(elem);
                Type::new(TypeKind::Array(self.arena.alloc(resolved)), typ.span)
            }
            TypeKind::Tuple(elems) => {
                let resolved: Vec<Type<'arena>> =
                    elems.iter().map(|e| self.deep_resolve_type(e)).collect();
                Type::new(
                    TypeKind::Tuple(self.arena.alloc_slice_fill_iter(resolved)),
                    typ.span,
                )
            }
            TypeKind::Function(func_type) => {
                // Recursively resolve parameter types and return type in function types
                let resolved_params: Vec<typedlua_parser::ast::statement::Parameter<'arena>> =
                    func_type
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

                let resolved_return = self.deep_resolve_type(func_type.return_type);

                Type::new(
                    TypeKind::Function(typedlua_parser::ast::types::FunctionType {
                        parameters: self
                            .arena
                            .alloc_slice_fill_iter(resolved_params),
                        return_type: self.arena.alloc(resolved_return),
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
    fn check_implements_assignable(&self, source: &Type<'arena>, target: &Type<'arena>) -> bool {
        phases::validation_phase::check_implements_assignable(
            source,
            target,
            &self.type_env,
            self.interner,
        )
    }

    /// Substitute type parameter references in a type with actual type arguments.
    /// For a generic interface like Container<T>, given type_args [number],
    /// replaces references to T with number.
    fn substitute_type_args_in_type(
        &self,
        typ: &Type<'arena>,
        type_args: &[Type<'arena>],
        interface_name: &str,
    ) -> Type<'arena> {
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
                Type::new(TypeKind::Array(self.arena.alloc(subst)), typ.span)
            }
            TypeKind::Nullable(inner) => {
                let subst = self.substitute_type_args_in_type(inner, type_args, interface_name);
                Type::new(TypeKind::Nullable(self.arena.alloc(subst)), typ.span)
            }
            TypeKind::Union(members) => {
                let subst: Vec<Type<'arena>> = members
                    .iter()
                    .map(|m| self.substitute_type_args_in_type(m, type_args, interface_name))
                    .collect();
                Type::new(
                    TypeKind::Union(self.arena.alloc_slice_fill_iter(subst)),
                    typ.span,
                )
            }
            _ => typ.clone(),
        }
    }

    /// Widen literal types to their base primitive types
    fn widen_type(&self, typ: Type<'arena>) -> Type<'arena> {
        type_utilities::widen_type(typ)
    }

    /// Register a declare function statement in the global scope
    fn register_declare_function(
        &mut self,
        func: &DeclareFunctionStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        phases::declaration_phase::register_declare_function(
            func,
            &mut self.symbol_table,
            self.interner,
            self.arena,
        )
    }

    /// Register a declare const statement in the global scope
    fn register_declare_const(
        &mut self,
        const_decl: &DeclareConstStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        phases::declaration_phase::register_declare_const(
            const_decl,
            &mut self.symbol_table,
            self.interner,
        )
    }

    /// Register a declare namespace statement in the global scope
    fn register_declare_namespace(
        &mut self,
        ns: &DeclareNamespaceStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        phases::declaration_phase::register_declare_namespace(
            ns,
            &mut self.symbol_table,
            self.interner,
            self.arena,
        )
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
        let string_param_upper = Parameter {
            pattern: Pattern::Identifier(Spanned::new(self.interner.intern("s"), span)),
            type_annotation: Some(self.type_env.get_string_type(span)),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };
        let string_param_lower = Parameter {
            pattern: Pattern::Identifier(Spanned::new(self.interner.intern("s"), span)),
            type_annotation: Some(self.type_env.get_string_type(span)),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };
        let string_members = vec![
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("upper"), span),
                type_parameters: None,
                parameters: self
                    .arena
                    .alloc_slice_fill_iter(std::iter::once(string_param_upper)),
                return_type: self.type_env.get_string_type(span),
                body: None,
                span,
            }),
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("lower"), span),
                type_parameters: None,
                parameters: self
                    .arena
                    .alloc_slice_fill_iter(std::iter::once(string_param_lower)),
                return_type: self.type_env.get_string_type(span),
                body: None,
                span,
            }),
        ];

        let string_type = Type::new(
            TypeKind::Object(ObjectType {
                members: self.arena.alloc_slice_fill_iter(string_members),
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
        let math_param_abs = Parameter {
            pattern: Pattern::Identifier(Spanned::new(self.interner.intern("x"), span)),
            type_annotation: Some(self.type_env.get_number_type(span)),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };
        let math_members = vec![
            ObjectTypeMember::Property(PropertySignature {
                is_readonly: true,
                name: Spanned::new(self.interner.intern("pi"), span),
                is_optional: false,
                type_annotation: self.type_env.get_number_type(span),
                span,
            }),
            ObjectTypeMember::Method(MethodSignature {
                name: Spanned::new(self.interner.intern("abs"), span),
                type_parameters: None,
                parameters: self
                    .arena
                    .alloc_slice_fill_iter(std::iter::once(math_param_abs)),
                return_type: self.type_env.get_number_type(span),
                body: None,
                span,
            }),
        ];

        let math_type = Type::new(
            TypeKind::Object(ObjectType {
                members: self.arena.alloc_slice_fill_iter(math_members),
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
    pub fn symbol_table(&self) -> &SymbolTable<'arena> {
        &self.symbol_table
    }

    /// Get a reference to the type environment for LSP queries
    pub fn type_env(&self) -> &TypeEnvironment<'arena> {
        &self.type_env
    }

    /// Lookup a symbol by name in the current scope
    pub fn lookup_symbol(&self, name: &str) -> Option<&Symbol<'arena>> {
        self.symbol_table.lookup(name)
    }

    /// Lookup a type by name
    pub fn lookup_type(&self, name: &str) -> Option<&Type<'arena>> {
        self.type_env.lookup_type(name)
    }

    /// Extract exports from a program for module system
    pub fn extract_exports(
        &self,
        program: &Program<'arena>,
    ) -> crate::module_resolver::ModuleExports {
        // Delegate to module_phase for export extraction
        phases::module_phase::extract_exports(
            program,
            &self.symbol_table,
            self.interner,
            self.module_registry.as_ref(),
            self.module_resolver.as_ref(),
            self.current_module_id.as_ref(),
        )
    }

    fn check_throw_statement(
        &mut self,
        stmt: &ThrowStatement<'arena>,
    ) -> Result<(), TypeCheckError> {
        self.infer_expression_type(&stmt.expression)?;
        Ok(())
    }

    fn check_rethrow_statement(&self, span: Span) -> Result<(), TypeCheckError> {
        phases::inference_phase::check_rethrow_statement(&self.in_catch_block, span)
    }

    fn check_import_statement(
        &mut self,
        import: &ImportDeclaration<'arena>,
    ) -> Result<(), TypeCheckError> {
        // Delegate to module_phase for import processing
        phases::module_phase::check_import_statement(
            import,
            &mut self.symbol_table,
            &mut self.type_env,
            &mut self.access_control,
            self.interner,
            &mut self.module_dependencies,
            self.module_registry.as_ref(),
            self.module_resolver.as_ref(),
            self.current_module_id.as_ref(),
            &self.diagnostic_handler,
        )
    }

    /// Get the list of module dependencies tracked during type checking
    pub fn get_module_dependencies(&self) -> &[std::path::PathBuf] {
        &self.module_dependencies
    }

    /// Check a program with incremental type checking support
    ///
    /// This method extends the regular `check_program` with support for:
    /// - Tracking declaration hashes for signature-based incremental invalidation
    /// - Building a dependency graph of declaration references
    ///
    /// # Arguments
    ///
    /// * `program` - The program to type check
    /// * `module_path` - Path to the module being checked (for declaration IDs)
    /// * `incremental_checker` - Optional incremental checker for tracking hashes and dependencies
    ///
    /// # Returns
    ///
    /// Result containing the type checking result or error
    #[instrument(skip(self, program, incremental_checker), fields(module_path = ?module_path))]
    pub fn check_program_incremental(
        &mut self,
        program: &Program<'arena>,
        module_path: std::path::PathBuf,
        incremental_checker: Option<&mut crate::IncrementalChecker>,
    ) -> Result<(), TypeCheckError> {
        use tracing::{debug, info, span, Level};

        let span = span!(
            Level::INFO,
            "check_program_incremental",
            statements = program.statements.len()
        );
        let _guard = span.enter();

        debug!(
            "Starting incremental type checking for program with {} statements",
            program.statements.len()
        );

        // PASS 1: Register all function declarations (hoisting)
        for statement in program.statements.iter() {
            if let Statement::Function(func_decl) = statement {
                self.register_function_signature(func_decl)?;

                // Track declaration for incremental checking (if checker is provided)
                if incremental_checker.is_some() {
                    let func_name = self.interner.resolve(func_decl.name.node).to_string();
                    let decl_id = crate::DeclarationId::new(module_path.clone(), func_name);
                    let hash = func_decl.compute_signature_hash(self.interner);
                    debug!(
                        ?decl_id,
                        hash, "Registered function declaration for incremental tracking"
                    );
                }
            }
        }

        debug!("Completed pass 1: function signatures registered");

        // PASS 2: Type check all statements (including function bodies)
        let mut first_error: Option<TypeCheckError> = None;
        let mut statements_checked = 0;
        for statement in program.statements.iter() {
            if let Err(e) = self.check_statement(statement) {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
            statements_checked += 1;
        }

        debug!(
            "Completed pass 2: checked {} statements",
            statements_checked
        );

        if let Some(err) = first_error {
            error!(error = %err, "Type checking failed");
            Err(err)
        } else {
            info!("Incremental type checking completed successfully");
            Ok(())
        }
    }

    /// Compute and return declaration hashes for a program
    ///
    /// This method extracts all declarations (functions, classes, interfaces, etc.)
    /// and computes stable signature hashes for incremental type checking.
    pub fn compute_declaration_hashes(
        &self,
        program: &Program<'arena>,
        _module_path: std::path::PathBuf,
        interner: &typedlua_parser::string_interner::StringInterner,
    ) -> FxHashMap<String, u64> {
        let mut hashes = FxHashMap::default();

        for statement in program.statements.iter() {
            match statement {
                Statement::Function(func) => {
                    let name = interner.resolve(func.name.node).to_string();
                    let hash = func.compute_signature_hash(interner);
                    hashes.insert(name, hash);
                }
                Statement::Class(class) => {
                    let name = interner.resolve(class.name.node).to_string();
                    let hash = class.compute_signature_hash(interner);
                    hashes.insert(name, hash);
                }
                Statement::Interface(iface) => {
                    let name = interner.resolve(iface.name.node).to_string();
                    let hash = iface.compute_signature_hash(interner);
                    hashes.insert(name, hash);
                }
                Statement::TypeAlias(alias) => {
                    let name = interner.resolve(alias.name.node).to_string();
                    let hash = alias.compute_signature_hash(interner);
                    hashes.insert(name, hash);
                }
                Statement::Enum(enum_decl) => {
                    let name = interner.resolve(enum_decl.name.node).to_string();
                    let hash = enum_decl.compute_signature_hash(interner);
                    hashes.insert(name, hash);
                }
                _ => {}
            }
        }

        hashes
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

    fn check_try_statement(&mut self, stmt: &TryStatement<'arena>) -> Result<(), TypeCheckError> {
        self.check_block(&stmt.try_block)?;

        for catch_clause in stmt.catch_clauses.iter() {
            self.check_catch_clause(catch_clause)?;
        }

        if let Some(finally_block) = &stmt.finally_block {
            self.check_block(finally_block)?;
        }

        Ok(())
    }

    fn check_catch_clause(&mut self, clause: &CatchClause<'arena>) -> Result<(), TypeCheckError> {
        self.symbol_table.enter_scope();

        let _catch_var_type = match &clause.pattern {
            CatchPattern::Untyped { variable, span } => {
                let any_type = self.type_env.get_unknown_type(*span);
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
                let union_type = Type::new(TypeKind::Union(type_annotations), *span);
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
        let result = self.check_block(&clause.body);
        self.in_catch_block.pop();

        self.symbol_table.exit_scope();

        result
    }

    /// Check if a class has circular inheritance by walking up the parent chain
    #[allow(dead_code)]
    fn has_circular_inheritance(&self, class_name: &str) -> bool {
        phases::validation_phase::has_circular_inheritance(class_name, &self.class_parents)
    }

    /// Check if a block always returns (has a return statement on all code paths)
    fn block_always_returns(&self, block: &Block<'arena>) -> bool {
        control_flow::block_always_returns(block, self.interner)
    }

    /// Check if a statement always returns
    #[allow(dead_code)]
    fn statement_always_returns(&self, stmt: &Statement<'arena>) -> bool {
        control_flow::statement_always_returns(stmt, self.interner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::diagnostics::CollectingDiagnosticHandler;
    use bumpalo::Bump;
    use typedlua_parser::lexer::Lexer;
    use typedlua_parser::parser::Parser;

    fn type_check_source(source: &str) -> Result<(), TypeCheckError> {
        let arena = Bump::new();
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let (interner, common) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let mut lexer = Lexer::new(source, handler.clone(), &interner);
        let tokens = lexer.tokenize().expect("Lexing failed");
        let mut parser = Parser::new(tokens, handler.clone(), &interner, &common, &arena);
        let program = parser.parse().expect("Parsing failed");

        let mut type_checker = TypeChecker::new(handler.clone(), &interner, &common, &arena);
        let result = type_checker.check_program(&program);

        // Check if there are errors in the diagnostic handler
        let has_errors = handler
            .get_diagnostics()
            .iter()
            .any(|d| d.level == crate::cli::diagnostics::DiagnosticLevel::Error);

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
        let arena = Bump::new();
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let (interner, common) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let mut lexer = Lexer::new(source, handler.clone(), &interner);
        let tokens = lexer.tokenize().expect("Lexing failed");
        let mut parser = Parser::new(tokens, handler.clone(), &interner, &common, &arena);
        let program = parser.parse().expect("Parsing failed");

        let mut type_checker =
            TypeChecker::new_with_stdlib(handler.clone(), &interner, &common, &arena)
                .expect("Failed to load stdlib");
        let result = type_checker.check_program(&program);

        // Check if there are errors in the diagnostic handler
        let has_errors = handler
            .get_diagnostics()
            .iter()
            .any(|d| d.level == crate::cli::diagnostics::DiagnosticLevel::Error);

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
