use super::super::visitors::{AccessControl, AccessControlVisitor, ClassMemberKind};
use super::TypeCheckVisitor;
use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_compat::TypeCompatibility;
use crate::core::type_environment::TypeEnvironment;
use crate::types::generics::instantiate_type;
use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::TypeCheckError;
use luanext_parser::ast::expression::*;
use luanext_parser::ast::pattern::{ArrayPatternElement, Pattern, PatternWithDefault};
use luanext_parser::ast::statement::{Block, OperatorKind, Statement};
use luanext_parser::ast::types::*;
use luanext_parser::prelude::{
    Argument, MatchArm, MatchArmBody, MatchExpression, PropertySignature,
};
use luanext_parser::span::Span;
use luanext_parser::string_interner::StringInterner;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tracing::{debug, error, instrument, span, Level};

/// Represents a variable binding from a pattern
#[derive(Debug, Clone)]
struct PatternBinding<'arena> {
    typ: Type<'arena>,
    span: Span,
}

/// Collection of bindings from a pattern
#[derive(Debug, Clone)]
struct PatternBindings<'arena> {
    bindings: FxHashMap<String, PatternBinding<'arena>>,
}

/// Trait for type inference operations
pub trait TypeInferenceVisitor<'arena>: TypeCheckVisitor {
    /// Infer the type of an expression
    fn infer_expression(
        &mut self,
        expr: &Expression<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of binary operation
    fn infer_binary_op(
        &self,
        op: BinaryOp,
        left: &Type<'arena>,
        right: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of unary operation
    fn infer_unary_op(
        &self,
        op: UnaryOp,
        operand: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of function call
    fn infer_call(
        &mut self,
        callee_type: &Type<'arena>,
        args: &[Argument<'arena>],
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of a method call on an object
    fn infer_method(
        &self,
        obj_type: &Type<'arena>,
        method_name: &str,
        _args: &[Argument<'arena>],
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of member access
    fn infer_member(
        &self,
        obj_type: &Type<'arena>,
        member: &str,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Infer type of index access
    fn infer_index(
        &self,
        obj_type: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Make a type optional by adding nil to the union
    fn make_optional(&self, typ: Type<'arena>, span: Span) -> Result<Type<'arena>, TypeCheckError>;

    /// Remove nil from a type
    fn remove_nil(&self, typ: &Type<'arena>, span: Span) -> Result<Type<'arena>, TypeCheckError>;

    /// Check if a type is nil
    fn is_nil(&self, typ: &Type<'arena>) -> bool;

    /// Infer type of null coalescing operation
    fn infer_null_coalesce(
        &self,
        left: &Type<'arena>,
        right: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Check match expression and return result type
    fn check_match(
        &mut self,
        match_expr: &MatchExpression<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError>;

    /// Check a pattern and bind variables
    fn check_pattern(
        &mut self,
        pattern: &Pattern<'arena>,
        expected_type: &Type<'arena>,
    ) -> Result<(), TypeCheckError>;
}

/// Type inference implementation
pub struct TypeInferrer<'a, 'arena> {
    arena: &'arena bumpalo::Bump,
    symbol_table: &'a mut SymbolTable<'arena>,
    type_env: &'a mut TypeEnvironment<'arena>,
    narrowing_context: &'a mut super::NarrowingContext<'arena>,
    access_control: &'a AccessControl<'arena>,
    interner: &'a StringInterner,
    diagnostic_handler: &'a Arc<dyn DiagnosticHandler>,
}

impl<'a, 'arena> TypeInferrer<'a, 'arena> {
    pub fn new(
        arena: &'arena bumpalo::Bump,
        symbol_table: &'a mut SymbolTable<'arena>,
        type_env: &'a mut TypeEnvironment<'arena>,
        narrowing_context: &'a mut super::NarrowingContext<'arena>,
        access_control: &'a AccessControl<'arena>,
        interner: &'a StringInterner,
        diagnostic_handler: &'a Arc<dyn DiagnosticHandler>,
    ) -> Self {
        Self {
            arena,
            symbol_table,
            type_env,
            narrowing_context,
            access_control,
            interner,
            diagnostic_handler,
        }
    }
}

impl<'a, 'arena> TypeCheckVisitor for TypeInferrer<'a, 'arena> {
    fn name(&self) -> &'static str {
        "TypeInferrer"
    }
}

impl<'a, 'arena> TypeInferenceVisitor<'arena> for TypeInferrer<'a, 'arena> {
    #[instrument(skip(self, expr), fields(expr_kind))]
    fn infer_expression(
        &mut self,
        expr: &Expression<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        let span = expr.span;
        let expr_kind = format!("{:?}", expr.kind);

        span!(Level::DEBUG, "infer_expression", kind = %expr_kind);

        match &expr.kind {
            ExpressionKind::Literal(lit) => {
                debug!(literal = ?lit, "Inferring literal type");
                Ok(Type::new(TypeKind::Literal(lit.clone()), span))
            }

            ExpressionKind::Identifier(name) => {
                let name_str = self.interner.resolve(*name);
                debug!(name = %name_str, "Inferring identifier type");

                // Check for narrowed type first
                if let Some(narrowed_type) = self.narrowing_context.get_narrowed_type(*name) {
                    debug!(name = %name_str, "Found narrowed type");
                    return Ok(narrowed_type.clone());
                }

                // Fall back to symbol table
                if let Some(symbol) = self.symbol_table.lookup(&name_str) {
                    debug!(name = %name_str, type = ?symbol.typ, "Found in symbol table");
                    Ok(symbol.typ.clone())
                } else {
                    error!(name = %name_str, "Undefined variable");

                    // Collect all visible symbols as candidates for fuzzy matching
                    let candidates: Vec<String> = self
                        .symbol_table
                        .all_visible_symbols()
                        .keys()
                        .cloned()
                        .collect();

                    let mut error =
                        TypeCheckError::new(format!("Undefined variable '{}'", name_str), span);

                    // Add "did you mean?" suggestion if a similar name is found
                    if let Some(suggestion) =
                        crate::utils::fuzzy::suggest_similar(&name_str, &candidates)
                    {
                        error = error.with_suggestion(suggestion);
                    }

                    Err(error)
                }
            }

            ExpressionKind::Binary(op, left, right) => {
                debug!(op = ?op, "Inferring binary operation type");
                let left_type = self.infer_expression(left)?;
                let right_type = self.infer_expression(right)?;
                self.infer_binary_op(*op, &left_type, &right_type, span)
            }

            ExpressionKind::Unary(op, operand) => {
                debug!(op = ?op, "Inferring unary operation type");
                let operand_type = self.infer_expression(operand)?;
                self.infer_unary_op(*op, &operand_type, span)
            }

            ExpressionKind::Call(callee, args, stored_type_args) => {
                // Check if this is an assertType intrinsic call
                if let ExpressionKind::Identifier(name_id) = &callee.kind {
                    let name = self.interner.resolve(*name_id);
                    if name == "assertType" {
                        return self.check_assert_type_intrinsic(args, *stored_type_args, span);
                    }
                }

                let callee_type = self.infer_expression(callee)?;

                // Note: We can no longer mutate stored_type_args since AST is arena-allocated.
                // Type argument inference results are used directly rather than stored back.

                self.infer_call(&callee_type, args, span)
            }

            ExpressionKind::MethodCall(object, method, args, _) => {
                let obj_type = self.infer_expression(object)?;
                let method_name = self.interner.resolve(method.node);
                let method_type = self.infer_method(&obj_type, &method_name, args, span)?;

                // Note: receiver_class and annotated_type are no longer mutated
                // since AST is arena-allocated (immutable). The type information
                // is returned from infer_expression instead.
                Ok(method_type)
            }

            ExpressionKind::Member(object, member) => {
                let obj_type = self.infer_expression(object)?;
                let member_name = self.interner.resolve(member.node);
                self.infer_member(&obj_type, &member_name, span)
            }

            ExpressionKind::Index(object, index) => {
                let obj_type = self.infer_expression(object)?;
                let _index_type = self.infer_expression(index)?;
                self.infer_index(&obj_type, span)
            }

            ExpressionKind::Assignment(target, _op, value) => {
                debug!("Inferring assignment expression");

                // Check if target is an undefined identifier (new global)
                let _new_global_name = match &target.kind {
                    ExpressionKind::Identifier(name) => {
                        let name_str = self.interner.resolve(*name);
                        if self.symbol_table.lookup(&name_str).is_none() {
                            Some(name_str.clone())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                // For new globals, infer RHS type first, then declare with that type
                let value_type = self.infer_expression(value)?;

                let target_type = match &target.kind {
                    ExpressionKind::Member(object, member) => {
                        let obj_type = self.infer_expression(object)?;
                        let member_name = self.interner.resolve(member.node);

                        if let TypeKind::Reference(type_ref) = &obj_type.kind {
                            let class_name = self.interner.resolve(type_ref.name.node);
                            self.access_control
                                .check_readonly_assignment(&class_name, &member_name)?;
                        }

                        self.infer_member(&obj_type, &member_name, span)?
                    }
                    ExpressionKind::Identifier(name) => {
                        let name_str = self.interner.resolve(*name);
                        if let Some(symbol) = self.symbol_table.lookup(&name_str) {
                            symbol.typ.clone()
                        } else {
                            // In Lua, bare assignment to an undefined variable creates a global
                            // Declare it with the inferred RHS type
                            let symbol = Symbol::new(
                                name_str.clone(),
                                SymbolKind::Variable,
                                value_type.clone(),
                                span,
                            );
                            let _ = self.symbol_table.declare(symbol);

                            value_type.clone()
                        }
                    }
                    _ => Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span),
                };

                if !TypeCompatibility::is_assignable(&value_type, &target_type) {
                    return Err(TypeCheckError::new(
                        "Type is not assignable".to_string(),
                        span,
                    ));
                }

                Ok(target_type)
            }

            ExpressionKind::OptionalMember(object, member) => {
                let obj_type = self.infer_expression(object)?;
                let member_name = self.interner.resolve(member.node);
                let member_type = self.infer_member(&obj_type, &member_name, span)?;
                self.make_optional(member_type, span)
            }

            ExpressionKind::OptionalIndex(object, index) => {
                let obj_type = self.infer_expression(object)?;
                let _index_type = self.infer_expression(index)?;
                let indexed_type = self.infer_index(&obj_type, span)?;
                self.make_optional(indexed_type, span)
            }

            ExpressionKind::OptionalCall(callee, args, _stored_type_args) => {
                let callee_type = self.infer_expression(callee)?;

                // Note: We can no longer mutate stored_type_args since AST is arena-allocated.

                let return_type = self.infer_call(&callee_type, args, span)?;
                self.make_optional(return_type, span)
            }

            ExpressionKind::OptionalMethodCall(object, method, args, _) => {
                let obj_type = self.infer_expression(object)?;
                let method_name = self.interner.resolve(method.node);
                let method_type = self.infer_method(&obj_type, &method_name, args, span)?;
                self.make_optional(method_type, span)
            }

            ExpressionKind::Array(elements) => {
                if elements.is_empty() {
                    // Empty array has unknown element type
                    return Ok(Type::new(
                        TypeKind::Array(
                            self.arena.alloc(Type::new(
                                TypeKind::Primitive(PrimitiveType::Unknown),
                                span,
                            )),
                        ),
                        span,
                    ));
                }

                // Collect all element types, including from spreads
                let mut element_types = Vec::new();

                for elem in elements.iter() {
                    match elem {
                        ArrayElement::Expression(expr) => {
                            let elem_type = self.infer_expression(expr)?;
                            element_types.push(elem_type);
                        }
                        ArrayElement::Spread(expr) => {
                            // Spread expression should be an array
                            let spread_type = self.infer_expression(expr)?;
                            match &spread_type.kind {
                                TypeKind::Array(elem_type) => {
                                    // Extract the element type from the spread array
                                    element_types.push((*elem_type).clone());
                                }
                                _ => {
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Cannot spread non-array type: {:?}",
                                            spread_type.kind
                                        ),
                                        expr.span,
                                    ));
                                }
                            }
                        }
                    }
                }

                // Find common type or create union
                if element_types.is_empty() {
                    return Ok(Type::new(
                        TypeKind::Array(
                            self.arena.alloc(Type::new(
                                TypeKind::Primitive(PrimitiveType::Unknown),
                                span,
                            )),
                        ),
                        span,
                    ));
                }

                let mut union_types = vec![element_types[0].clone()];
                for elem_type in &element_types[1..] {
                    if !TypeCompatibility::is_assignable(&union_types[0], elem_type)
                        && !TypeCompatibility::is_assignable(elem_type, &union_types[0])
                    {
                        // Types are incompatible, add to union
                        if !union_types
                            .iter()
                            .any(|t| TypeCompatibility::is_assignable(t, elem_type))
                        {
                            union_types.push(elem_type.clone());
                        }
                    }
                }

                let result_type = if union_types.len() == 1 {
                    union_types
                        .into_iter()
                        .next()
                        .expect("length checked above")
                } else {
                    let types = self.arena.alloc_slice_fill_iter(union_types.into_iter());
                    Type::new(TypeKind::Union(types), span)
                };

                Ok(Type::new(
                    TypeKind::Array(self.arena.alloc(result_type)),
                    span,
                ))
            }

            ExpressionKind::Object(props) => {
                // Infer object type from properties
                let mut members = Vec::new();

                for prop in props.iter() {
                    match prop {
                        ObjectProperty::Property {
                            key,
                            value,
                            span: prop_span,
                        } => {
                            // Infer the type of the value
                            let value_type = self.infer_expression(value)?;

                            // Create a property signature
                            let prop_sig = PropertySignature {
                                is_readonly: false,
                                name: key.clone(),
                                is_optional: false,
                                type_annotation: value_type,
                                span: *prop_span,
                            };

                            members.push(ObjectTypeMember::Property(prop_sig));
                        }
                        ObjectProperty::Computed {
                            key,
                            value,
                            span: computed_span,
                        } => {
                            // Type check the key expression - should be string or number
                            let key_type = self.infer_expression(key)?;
                            match &key_type.kind {
                                TypeKind::Primitive(PrimitiveType::String)
                                | TypeKind::Primitive(PrimitiveType::Number)
                                | TypeKind::Primitive(PrimitiveType::Integer)
                                | TypeKind::Literal(_) => {
                                    // Valid key type
                                }
                                _ => {
                                    return Err(TypeCheckError::new(
                                        format!("Computed property key must be string or number, got {:?}", key_type.kind),
                                        *computed_span,
                                    ));
                                }
                            }

                            // Type check the value expression
                            self.infer_expression(value)?;

                            // Note: We can't add computed properties to the static object type
                            // since we don't know the key at compile time, but we still validate them
                        }
                        ObjectProperty::Spread {
                            value,
                            span: spread_span,
                        } => {
                            // Spread object properties
                            let spread_type = self.infer_expression(value)?;
                            match &spread_type.kind {
                                TypeKind::Object(obj_type) => {
                                    // Add all members from the spread object
                                    for member in obj_type.members.iter() {
                                        members.push(member.clone());
                                    }
                                }
                                _ => {
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Cannot spread non-object type: {:?}",
                                            spread_type.kind
                                        ),
                                        *spread_span,
                                    ));
                                }
                            }
                        }
                    }
                }

                let members = self.arena.alloc_slice_fill_iter(members.into_iter());
                Ok(Type::new(
                    TypeKind::Object(ObjectType { members, span }),
                    span,
                ))
            }

            ExpressionKind::Function(func_expr) => {
                // Enter a new scope for the function expression
                self.symbol_table.enter_scope();

                // Register parameters in the scope
                for param in func_expr.parameters.iter() {
                    if let Pattern::Identifier(ident) = &param.pattern {
                        let param_type = if let Some(type_ann) = &param.type_annotation {
                            // Use the declared type
                            type_ann.clone()
                        } else {
                            // No type annotation - use unknown
                            Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
                        };

                        let symbol = Symbol::new(
                            self.interner.resolve(ident.node).to_string(),
                            SymbolKind::Variable,
                            param_type,
                            ident.span,
                        );
                        let _ = self.symbol_table.declare(symbol);
                    }
                }

                // Infer the return type from the block body
                let body_type = match self.infer_block_return_type(&func_expr.body)? {
                    Some(return_type) => return_type,
                    None => {
                        // No return statements found - void function
                        Type::new(TypeKind::Primitive(PrimitiveType::Void), span)
                    }
                };

                // Check return type if specified
                if let Some(declared_return_type) = &func_expr.return_type {
                    if !TypeCompatibility::is_assignable(&body_type, declared_return_type) {
                        self.diagnostic_handler.error(
                            span,
                            &format!(
                                "Function expression return type mismatch: expected '{:?}', found '{:?}'",
                                declared_return_type.kind, body_type.kind
                            ),
                        );
                    }
                }

                // Exit the function scope
                self.symbol_table.exit_scope();

                // Build the function type
                let func_type = FunctionType {
                    type_parameters: func_expr.type_parameters,
                    parameters: func_expr.parameters,
                    return_type: self.arena.alloc(
                        func_expr
                            .return_type
                            .clone()
                            .unwrap_or_else(|| body_type.clone()),
                    ),
                    throws: None,
                    span,
                };

                Ok(Type::new(TypeKind::Function(func_type), span))
            }

            ExpressionKind::Arrow(arrow_fn) => {
                // Enter a new scope for the arrow function
                self.symbol_table.enter_scope();

                // Register parameters in the scope
                for param in arrow_fn.parameters.iter() {
                    if let Pattern::Identifier(ident) = &param.pattern {
                        let param_type = if let Some(type_ann) = &param.type_annotation {
                            // Use the declared type
                            type_ann.clone()
                        } else {
                            // No type annotation - use unknown
                            Type::new(TypeKind::Primitive(PrimitiveType::Unknown), param.span)
                        };

                        let symbol = Symbol::new(
                            self.interner.resolve(ident.node).to_string(),
                            SymbolKind::Variable,
                            param_type,
                            ident.span,
                        );
                        let _ = self.symbol_table.declare(symbol);
                    }
                }

                // Infer the body type
                let body_type = match &arrow_fn.body {
                    ArrowBody::Expression(expr) => self.infer_expression(expr)?,
                    ArrowBody::Block(block) => match self.infer_block_return_type(block)? {
                        Some(return_type) => return_type,
                        None => Type::new(TypeKind::Primitive(PrimitiveType::Void), span),
                    },
                };

                // Check return type if specified
                if let Some(declared_return_type) = &arrow_fn.return_type {
                    if !TypeCompatibility::is_assignable(&body_type, declared_return_type) {
                        self.diagnostic_handler.error(
                            span,
                            &format!(
                                "Arrow function return type mismatch: expected '{:?}', found '{:?}'",
                                declared_return_type.kind, body_type.kind
                            ),
                        );
                    }
                }

                // Exit the arrow function scope
                self.symbol_table.exit_scope();

                // Return a function type
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }

            ExpressionKind::Conditional(cond, then_expr, else_expr) => {
                let _cond_type = self.infer_expression(cond)?;
                let then_type = self.infer_expression(then_expr)?;
                let else_type = self.infer_expression(else_expr)?;

                // Return union of both branches
                if TypeCompatibility::is_assignable(&then_type, &else_type) {
                    Ok(else_type)
                } else if TypeCompatibility::is_assignable(&else_type, &then_type) {
                    Ok(then_type)
                } else {
                    let types = self.arena.alloc_slice_fill_iter([then_type, else_type]);
                    Ok(Type::new(TypeKind::Union(types), span))
                }
            }

            ExpressionKind::Match(match_expr) => self.check_match(match_expr),

            ExpressionKind::Pipe(left_expr, right_expr) => {
                // Pipe operator: left |> right
                // The right side should be a function, and we apply left as the first argument
                let _left_type = self.infer_expression(left_expr)?;

                // For now, we'll infer the result type by checking the right expression
                // In a full implementation, we'd check if right is a function and apply left to it
                // For simplicity, we'll type check right and return its type
                // (This handles cases like: value |> func where func returns something)
                self.infer_expression(right_expr)
            }

            ExpressionKind::Try(try_expr) => {
                let expr_type = self.infer_expression(try_expr.expression)?;
                let catch_type = self.infer_expression(try_expr.catch_expression)?;

                if TypeCompatibility::is_assignable(&expr_type, &catch_type) {
                    Ok(catch_type)
                } else if TypeCompatibility::is_assignable(&catch_type, &expr_type) {
                    Ok(expr_type)
                } else {
                    let types = self.arena.alloc_slice_fill_iter([expr_type, catch_type]);
                    Ok(Type::new(TypeKind::Union(types), span))
                }
            }

            ExpressionKind::ErrorChain(left_expr, right_expr) => {
                let _left_type = self.infer_expression(left_expr)?;
                self.infer_expression(right_expr)
            }

            ExpressionKind::New(callee, _args, type_args) => {
                // Infer the class type from the callee expression
                // For `new ClassName(args)`, callee is Identifier("ClassName")
                // For `new ClassName<T>(args)`, type_args carries the <T>
                match &callee.kind {
                    ExpressionKind::Identifier(name) => {
                        let class_name = self.interner.resolve(*name);

                        // Check if the class is abstract
                        if self.type_env.is_abstract_class(&class_name) {
                            return Err(TypeCheckError::new(
                                format!("Cannot instantiate abstract class '{}'", class_name),
                                span,
                            ));
                        }

                        // Return a Reference type to the class, preserving type arguments
                        Ok(Type::new(
                            TypeKind::Reference(TypeReference {
                                name: luanext_parser::ast::Spanned::new(*name, span),
                                type_arguments: *type_args,
                                span,
                            }),
                            span,
                        ))
                    }
                    _ => {
                        // For complex callee expressions, infer the callee type
                        // and use it as the result type
                        Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
                    }
                }
            }

            ExpressionKind::Parenthesized(inner) => {
                // Parenthesized expressions have the same type as their inner expression
                self.infer_expression(inner)
            }

            ExpressionKind::SelfKeyword => {
                // 'self' refers to the current instance in a class method
                // Look up 'self' in the symbol table
                if let Some(symbol) = self.symbol_table.lookup("self") {
                    Ok(symbol.typ.clone())
                } else {
                    Err(TypeCheckError::new(
                        "'self' keyword used outside of class context".to_string(),
                        span,
                    ))
                }
            }

            ExpressionKind::SuperKeyword => {
                // 'super' refers to the parent class
                // Look up 'super' in the symbol table
                if let Some(symbol) = self.symbol_table.lookup("super") {
                    Ok(symbol.typ.clone())
                } else {
                    Err(TypeCheckError::new(
                        "'super' keyword used outside of class context".to_string(),
                        span,
                    ))
                }
            }

            ExpressionKind::Template(template_lit) => {
                // Template literals are always strings
                // Type check the interpolated expressions
                for part in template_lit.parts.iter() {
                    if let luanext_parser::ast::expression::TemplatePart::Expression(expr) = part {
                        // Type check the expression, but we don't need its type
                        // as all values are coerced to strings in template literals
                        self.infer_expression(expr)?;
                    }
                }
                // Template literals always produce strings
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::String), span))
            }

            ExpressionKind::TypeAssertion(expr, asserted_type) => {
                // Type assertions (expr as Type) override the inferred type
                // First, infer the expression type to ensure it's valid
                let expr_type = self.infer_expression(expr)?;

                // Check if the assertion is valid (expression type is compatible with asserted type)
                if !TypeCompatibility::is_assignable(&expr_type, asserted_type)
                    && !TypeCompatibility::is_assignable(asserted_type, &expr_type)
                {
                    self.diagnostic_handler.error(
                        span,
                        &format!(
                            "Type assertion is invalid: cannot assert type '{:?}' on expression of type '{:?}'",
                            asserted_type.kind, expr_type.kind
                        ),
                    );
                }

                // Return the asserted type
                Ok(asserted_type.clone())
            }
        }
    }

    fn infer_binary_op(
        &self,
        op: BinaryOp,
        left: &Type<'arena>,
        right: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        match op {
            BinaryOp::Add
            | BinaryOp::Subtract
            | BinaryOp::Multiply
            | BinaryOp::Divide
            | BinaryOp::Modulo
            | BinaryOp::Power
            | BinaryOp::IntegerDivide => {
                // Check for operator overload on the left operand's class
                if let Some(return_type) = self.check_operator_overload(left, op) {
                    return Ok(return_type);
                }

                // Check that both operands are numbers
                let left_is_number = matches!(
                    left.kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                        | TypeKind::Literal(Literal::Number(_))
                );
                let right_is_number = matches!(
                    right.kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                        | TypeKind::Literal(Literal::Number(_))
                );

                if !left_is_number {
                    self.diagnostic_handler.error(
                        span,
                        &format!(
                            "Left operand of arithmetic operation must be a number, found {:?}",
                            left.kind
                        ),
                    );
                }
                if !right_is_number {
                    self.diagnostic_handler.error(
                        span,
                        &format!(
                            "Right operand of arithmetic operation must be a number, found {:?}",
                            right.kind
                        ),
                    );
                }

                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Number), span))
            }
            BinaryOp::Concatenate => {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::String), span))
            }
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::LessThan
            | BinaryOp::LessThanOrEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterThanOrEqual
            | BinaryOp::Instanceof => {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Boolean), span))
            }
            BinaryOp::And | BinaryOp::Or => {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
            BinaryOp::NullCoalesce => self.infer_null_coalesce(left, right, span),
            BinaryOp::BitwiseAnd
            | BinaryOp::BitwiseOr
            | BinaryOp::BitwiseXor
            | BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight => {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Number), span))
            }
        }
    }

    fn infer_unary_op(
        &self,
        op: UnaryOp,
        _operand: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        match op {
            UnaryOp::Negate => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            UnaryOp::Not => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Boolean), span)),
            UnaryOp::Length => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            UnaryOp::BitwiseNot => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
        }
    }

    #[instrument(skip(self, callee_type, args), fields(args_count = args.len(), return_type))]
    fn infer_call(
        &mut self,
        callee_type: &Type<'arena>,
        args: &[Argument<'arena>],
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        debug!(callee_type = ?callee_type.kind, "Inferring function call type");

        match &callee_type.kind {
            TypeKind::Function(func_type) => {
                // Check argument count
                let actual_args = args.len();
                debug!(actual_args, "Checking function call argument count");

                // Count required parameters (non-optional, non-rest, no default value)
                let required_params = func_type
                    .parameters
                    .iter()
                    .filter(|p| !p.is_rest && !p.is_optional && p.default.is_none())
                    .count();

                // Check if the last parameter is a rest parameter
                let has_rest_param = func_type
                    .parameters
                    .last()
                    .map(|p| p.is_rest)
                    .unwrap_or(false);

                // Count optional parameters (includes parameters with default values)
                let optional_params = func_type
                    .parameters
                    .iter()
                    .filter(|p| (p.is_optional || p.default.is_some()) && !p.is_rest)
                    .count();

                let max_params = if has_rest_param {
                    usize::MAX
                } else {
                    required_params + optional_params
                };

                // Check minimum required arguments
                if actual_args < required_params {
                    error!(
                        expected_min = required_params,
                        actual = actual_args,
                        "Too few arguments"
                    );
                    return Err(TypeCheckError::new(
                        format!(
                            "Function expects at least {} arguments but received {}",
                            required_params, actual_args
                        ),
                        span,
                    ));
                }

                // Check maximum allowed arguments (unless rest parameter)
                if !has_rest_param && actual_args > max_params {
                    error!(
                        expected_max = max_params,
                        actual = actual_args,
                        "Too many arguments"
                    );
                    return Err(TypeCheckError::new(
                        format!(
                            "Function expects at most {} arguments but received {}",
                            max_params, actual_args
                        ),
                        span,
                    ));
                }

                // Check argument types match parameter types
                for (i, arg) in args.iter().enumerate() {
                    if i < func_type.parameters.len() {
                        let param = &func_type.parameters[i];

                        // Infer the argument type
                        if let Ok(arg_type) = self.infer_expression(&arg.value) {
                            if let Some(param_type) = &param.type_annotation {
                                // Check if argument type is assignable to parameter type
                                // Use is_assignable_with_env to properly resolve type aliases
                                if !TypeCompatibility::is_assignable_with_env(
                                    &arg_type,
                                    param_type,
                                    self.type_env,
                                    self.interner,
                                ) {
                                    self.diagnostic_handler.error(
                                        arg.value.span,
                                        &format!(
                                            "Type mismatch in function call: argument {} has type '{:?}' which is not assignable to parameter type '{:?}'",
                                            i + 1,
                                            arg_type.kind,
                                            param_type.kind
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }

                Ok((*func_type.return_type).clone())
            }
            _ => {
                // Non-function called - return unknown
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
        }
    }

    fn infer_method(
        &self,
        obj_type: &Type<'arena>,
        method_name: &str,
        _args: &[Argument<'arena>],
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        // Look up the method in the object type
        match &obj_type.kind {
            TypeKind::Object(obj) => {
                for member in obj.members.iter() {
                    if let ObjectTypeMember::Method(method) = member {
                        if self.interner.resolve(method.name.node) == method_name {
                            // Return the return type of the method
                            return Ok(method.return_type.clone());
                        }
                    }
                }
                // Method not found - return unknown
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
            TypeKind::Reference(type_ref) => {
                let type_name = self.interner.resolve(type_ref.name.node);
                if let Some(class_members) = self.access_control.get_class_members(&type_name) {
                    for member in class_members {
                        if member.name == method_name {
                            if let ClassMemberKind::Method { return_type, .. } = &member.kind {
                                return Ok(return_type.clone().unwrap_or_else(|| {
                                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)
                                }));
                            }
                        }
                    }
                }
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
            _ => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)),
        }
    }

    fn infer_member(
        &self,
        obj_type: &Type<'arena>,
        member: &str,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        match &obj_type.kind {
            TypeKind::Reference(type_ref) => {
                let type_name = self.interner.resolve(type_ref.name.node);

                // Check if this is a generic type alias with type arguments
                if let Some(type_args) = &type_ref.type_arguments {
                    if let Some(generic_alias) = self.type_env.get_generic_type_alias(&type_name) {
                        // Instantiate the generic type alias with the provided type arguments
                        let instantiated = instantiate_type(
                            self.arena,
                            &generic_alias.typ,
                            &generic_alias.type_parameters,
                            type_args,
                        )
                        .map_err(|e| TypeCheckError::new(e, span))?;
                        return self.infer_member(&instantiated, member, span);
                    }
                }

                // Check if this is a type parameter with a constraint
                // If so, resolve member access on the constraint type
                if let Some(constraint) = self.type_env.get_type_param_constraint(&type_name) {
                    return self.infer_member(constraint, member, span);
                }

                // Check access modifiers for class members (only for actual classes)
                self.check_member_access(&type_name, member, span)?;

                // Try to resolve the type reference to get the actual type
                // Use lookup_type to check both type aliases and interfaces
                if let Some(resolved) = self.type_env.lookup_type(&type_name) {
                    // Check for infinite recursion - if resolved type is the same as input, avoid loop
                    if matches!(resolved.kind, TypeKind::Reference(_)) {
                        // If resolved is still a reference, check if it's the same reference
                        if let TypeKind::Reference(resolved_ref) = &resolved.kind {
                            if resolved_ref.name.node == type_ref.name.node {
                                // Same type reference - check if it's a field of the enum
                                // For enums, we need to check fields defined in the enum declaration
                                // For now, return unknown to avoid infinite loop
                                // The field will be looked up from the symbol table instead
                                return Ok(Type::new(
                                    TypeKind::Primitive(PrimitiveType::Unknown),
                                    span,
                                ));
                            }
                        }
                    }
                    return self.infer_member(resolved, member, span);
                }

                // Fall back to access_control for class property/getter types.
                // Only use concrete type annotations (no unresolved type parameters).
                // Generic class members contain raw type params like T that need
                // substitution, so we skip those and fall through to Unknown.
                if let Some(class_members) = self.access_control.get_class_members(&type_name) {
                    for m in class_members {
                        if m.name == member {
                            match &m.kind {
                                ClassMemberKind::Property { type_annotation }
                                    if !self.type_has_unresolved_params(type_annotation) =>
                                {
                                    return Ok(type_annotation.clone());
                                }
                                ClassMemberKind::Getter { return_type }
                                    if !self.type_has_unresolved_params(return_type) =>
                                {
                                    return Ok(return_type.clone());
                                }
                                ClassMemberKind::Method {
                                    return_type: Some(rt),
                                    ..
                                } if !self.type_has_unresolved_params(rt) => {
                                    return Ok(rt.clone());
                                }
                                _ => {}
                            }
                        }
                    }
                }

                // If not resolvable, return unknown
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
            TypeKind::Object(obj) => {
                // Find member in object type
                let member_id = self.interner.intern(member);
                for obj_member in obj.members.iter() {
                    match obj_member {
                        ObjectTypeMember::Property(prop) => {
                            if prop.name.node == member_id {
                                return Ok(prop.type_annotation.clone());
                            }
                        }
                        ObjectTypeMember::Method(method) => {
                            if method.name.node == member_id {
                                return Ok(Type::new(
                                    TypeKind::Primitive(PrimitiveType::Unknown),
                                    span,
                                ));
                            }
                        }
                        _ => {}
                    }
                }
                // Member not found
                Err(TypeCheckError::new(
                    format!("Property '{}' does not exist", member),
                    span,
                ))
            }
            TypeKind::Union(types) => {
                // For union types, try to find the member in each non-nil variant
                let non_nil_types: Vec<&Type<'arena>> =
                    types.iter().filter(|t| !self.is_nil(t)).collect();

                if non_nil_types.is_empty() {
                    // All types are nil - member access on nil returns nil
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Nil), span))
                } else if non_nil_types.len() == 1 {
                    // Single non-nil type - look up member on that
                    self.infer_member(non_nil_types[0], member, span)
                } else {
                    // Multiple non-nil types - try to look up member on first valid one
                    // For simplicity, we try each type and return the first successful lookup
                    for typ in non_nil_types {
                        if let Ok(member_type) = self.infer_member(typ, member, span) {
                            return Ok(member_type);
                        }
                    }
                    // If none succeeded, return unknown
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
                }
            }
            TypeKind::Nullable(inner) => {
                // For nullable types, look up member on the inner type
                self.infer_member(inner, member, span)
            }
            _ => {
                // Non-object member access - return unknown
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
        }
    }

    fn infer_index(
        &self,
        obj_type: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        match &obj_type.kind {
            TypeKind::Array(elem_type) => Ok((**elem_type).clone()),
            TypeKind::Tuple(types) => {
                // For now, return union of all tuple types
                if types.is_empty() {
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
                } else if types.len() == 1 {
                    Ok(types[0].clone())
                } else {
                    Ok(Type::new(TypeKind::Union(types), span))
                }
            }
            _ => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)),
        }
    }

    fn make_optional(&self, typ: Type<'arena>, span: Span) -> Result<Type<'arena>, TypeCheckError> {
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), span);
        let types = self.arena.alloc_slice_fill_iter([typ, nil_type]);
        Ok(Type::new(TypeKind::Union(types), span))
    }

    fn remove_nil(&self, typ: &Type<'arena>, span: Span) -> Result<Type<'arena>, TypeCheckError> {
        match &typ.kind {
            TypeKind::Union(types) => {
                let non_nil_types: Vec<Type<'arena>> =
                    types.iter().filter(|t| !self.is_nil(t)).cloned().collect();
                if non_nil_types.is_empty() {
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
                } else if non_nil_types.len() == 1 {
                    Ok(non_nil_types[0].clone())
                } else {
                    let types = self.arena.alloc_slice_fill_iter(non_nil_types);
                    Ok(Type::new(TypeKind::Union(types), span))
                }
            }
            _ => {
                if self.is_nil(typ) {
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
                } else {
                    Ok(typ.clone())
                }
            }
        }
    }

    fn is_nil(&self, typ: &Type<'arena>) -> bool {
        match &typ.kind {
            TypeKind::Primitive(PrimitiveType::Nil) => true,
            TypeKind::Literal(Literal::Nil) => true,
            TypeKind::Nullable(inner) => self.is_nil(inner),
            _ => false,
        }
    }

    fn infer_null_coalesce(
        &self,
        left: &Type<'arena>,
        right: &Type<'arena>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        // If left is T | nil, the result is T (left without nil)
        // If left is just nil, the result is the type of right
        // Otherwise, the result is the type of left
        let left_without_nil = self.remove_nil(left, span)?;

        // If left was just nil, return right's type
        // Otherwise return left's type without nil
        let result = if matches!(
            left_without_nil.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ) {
            right.clone()
        } else {
            left_without_nil
        };

        Ok(result)
    }

    #[instrument(skip(self, match_expr), fields(arms = match_expr.arms.len()))]
    fn check_match(
        &mut self,
        match_expr: &MatchExpression<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        debug!(span = ?match_expr.span, "Checking match expression");

        // Type check the value being matched
        let value_type = self.infer_expression(match_expr.value)?;
        debug!(value_type = ?value_type.kind, "Matched value type");

        if match_expr.arms.is_empty() {
            error!("Match expression has no arms");
            return Err(TypeCheckError::new(
                "Match expression must have at least one arm".to_string(),
                match_expr.span,
            ));
        }

        // Check exhaustiveness
        self.check_exhaustiveness(match_expr.arms, &value_type, match_expr.span)?;

        // Check for unreachable patterns
        self.check_unreachable_patterns(match_expr.arms);

        // Type check each arm and collect result types
        let mut arm_types = Vec::new();

        for arm in match_expr.arms.iter() {
            // Enter a new scope for this arm
            self.symbol_table.enter_scope();

            // First check that the pattern is compatible with the value type
            self.check_pattern(&arm.pattern, &value_type)?;

            // Then narrow the type based on the pattern for variable bindings
            let _narrowed_type = self.narrow_type_by_pattern(&arm.pattern, &value_type)?;

            // Check the guard if present
            if let Some(guard) = &arm.guard {
                let guard_type = self.infer_expression(guard)?;
                // Guard should be boolean (primitive or literal)
                let is_boolean =
                    matches!(guard_type.kind, TypeKind::Primitive(PrimitiveType::Boolean))
                        || matches!(guard_type.kind, TypeKind::Literal(Literal::Boolean(_)));

                if !is_boolean {
                    return Err(TypeCheckError::new(
                        format!("Match guard must be boolean, found {:?}", guard_type.kind),
                        guard.span,
                    ));
                }
            }

            // Check the arm body
            let arm_type = match &arm.body {
                MatchArmBody::Expression(expr) => self.infer_expression(expr)?,
                MatchArmBody::Block(block) => {
                    // Type check the block
                    for _stmt in block.statements.iter() {
                        // For now, we can't easily check statements here
                        // This would require access to the full type checker
                    }
                    // Return type is void for blocks without explicit return
                    Type::new(TypeKind::Primitive(PrimitiveType::Void), block.span)
                }
            };

            arm_types.push(arm_type);

            // Exit the arm scope
            self.symbol_table.exit_scope();
        }

        // All arms should have compatible types - return a union
        if arm_types.is_empty() {
            return Ok(Type::new(
                TypeKind::Primitive(PrimitiveType::Never),
                match_expr.span,
            ));
        }

        // Find the common type or create a union
        let mut union_types = vec![arm_types[0].clone()];
        for arm_type in &arm_types[1..] {
            if TypeCompatibility::is_assignable(&union_types[0], arm_type) {
                // Keep first type
            } else if TypeCompatibility::is_assignable(arm_type, &union_types[0]) {
                union_types[0] = arm_type.clone();
            } else {
                // Types are incompatible, add to union
                if !union_types
                    .iter()
                    .any(|t| TypeCompatibility::is_assignable(t, arm_type))
                {
                    union_types.push(arm_type.clone());
                }
            }
        }

        let result_type = if union_types.len() == 1 {
            union_types
                .into_iter()
                .next()
                .expect("length checked above")
        } else {
            let types = self.arena.alloc_slice_fill_iter(union_types.into_iter());
            Type::new(TypeKind::Union(types), match_expr.span)
        };

        Ok(result_type)
    }

    fn check_pattern(
        &mut self,
        pattern: &Pattern<'arena>,
        expected_type: &Type<'arena>,
    ) -> Result<(), TypeCheckError> {
        match pattern {
            Pattern::Identifier(ident) => {
                // Bind the identifier to the expected type
                let symbol = Symbol::new(
                    self.interner.resolve(ident.node).to_string(),
                    SymbolKind::Variable,
                    expected_type.clone(),
                    ident.span,
                );
                self.symbol_table
                    .declare(symbol)
                    .map_err(|e| TypeCheckError::new(e, ident.span))?;
                Ok(())
            }
            Pattern::Literal(lit, span) => {
                // Check that the literal pattern type is compatible with the expected type
                // For example, a string literal pattern should not match a number value
                let pattern_is_number = matches!(lit, Literal::Number(_) | Literal::Integer(_));
                let pattern_is_string = matches!(lit, Literal::String(_));
                let pattern_is_boolean = matches!(lit, Literal::Boolean(_));
                let pattern_is_nil = matches!(lit, Literal::Nil);

                let expected_is_number = matches!(
                    expected_type.kind,
                    TypeKind::Primitive(PrimitiveType::Number | PrimitiveType::Integer)
                        | TypeKind::Literal(Literal::Number(_) | Literal::Integer(_))
                );
                let expected_is_string = matches!(
                    expected_type.kind,
                    TypeKind::Primitive(PrimitiveType::String)
                        | TypeKind::Literal(Literal::String(_))
                );
                let expected_is_boolean = matches!(
                    expected_type.kind,
                    TypeKind::Primitive(PrimitiveType::Boolean)
                        | TypeKind::Literal(Literal::Boolean(_))
                );
                let expected_is_nil = matches!(
                    expected_type.kind,
                    TypeKind::Primitive(PrimitiveType::Nil) | TypeKind::Literal(Literal::Nil)
                );

                let is_compatible = (pattern_is_number && expected_is_number)
                    || (pattern_is_string && expected_is_string)
                    || (pattern_is_boolean && expected_is_boolean)
                    || (pattern_is_nil && expected_is_nil);

                if !is_compatible {
                    self.diagnostic_handler.error(
                        *span,
                        &format!(
                            "Pattern type mismatch: cannot match literal '{:?}' against type '{:?}'",
                            lit, expected_type.kind
                        ),
                    );
                }
                Ok(())
            }
            Pattern::Wildcard(_) => {
                // Wildcard matches anything
                Ok(())
            }
            Pattern::Array(array_pattern) => {
                // Expected type should be an array
                match &expected_type.kind {
                    TypeKind::Array(elem_type) => {
                        for elem in array_pattern.elements.iter() {
                            match elem {
                                ArrayPatternElement::Pattern(PatternWithDefault {
                                    pattern: pat,
                                    ..
                                }) => {
                                    self.check_pattern(pat, elem_type)?;
                                }
                                ArrayPatternElement::Rest(ident) => {
                                    // Rest pattern gets the array type
                                    let symbol = Symbol::new(
                                        self.interner.resolve(ident.node).to_string(),
                                        SymbolKind::Variable,
                                        expected_type.clone(),
                                        ident.span,
                                    );
                                    self.symbol_table
                                        .declare(symbol)
                                        .map_err(|e| TypeCheckError::new(e, ident.span))?;
                                }
                                ArrayPatternElement::Hole => {
                                    // Hole doesn't bind anything
                                }
                            }
                        }
                        Ok(())
                    }
                    _ => Err(TypeCheckError::new(
                        format!(
                            "Array pattern requires array type, found {:?}",
                            expected_type.kind
                        ),
                        array_pattern.span,
                    )),
                }
            }
            Pattern::Object(object_pattern) => {
                // Extract property types from the expected object type
                match &expected_type.kind {
                    TypeKind::Object(obj_type) => {
                        for prop in object_pattern.properties.iter() {
                            // Find the property type in the object
                            let prop_type = obj_type
                                .members
                                .iter()
                                .find_map(|member| {
                                    if let ObjectTypeMember::Property(prop_sig) = member {
                                        if prop_sig.name.node == prop.key.node {
                                            return Some(prop_sig.type_annotation.clone());
                                        }
                                    }
                                    None
                                })
                                .unwrap_or_else(|| {
                                    Type::new(
                                        TypeKind::Primitive(PrimitiveType::Unknown),
                                        prop.span,
                                    )
                                });

                            if let Some(value_pattern) = &prop.value {
                                self.check_pattern(value_pattern, &prop_type)?;
                            } else {
                                // Shorthand: bind the key as a variable
                                let symbol = Symbol::new(
                                    self.interner.resolve(prop.key.node).to_string(),
                                    SymbolKind::Variable,
                                    prop_type,
                                    prop.key.span,
                                );
                                self.symbol_table
                                    .declare(symbol)
                                    .map_err(|e| TypeCheckError::new(e, prop.key.span))?;
                            }
                        }
                        Ok(())
                    }
                    _ => {
                        // If it's not an object type, accept any object pattern for now
                        // This handles cases like Table type
                        for prop in object_pattern.properties.iter() {
                            let prop_type =
                                Type::new(TypeKind::Primitive(PrimitiveType::Unknown), prop.span);

                            if let Some(value_pattern) = &prop.value {
                                self.check_pattern(value_pattern, &prop_type)?;
                            } else {
                                let symbol = Symbol::new(
                                    self.interner.resolve(prop.key.node).to_string(),
                                    SymbolKind::Variable,
                                    prop_type,
                                    prop.key.span,
                                );
                                self.symbol_table
                                    .declare(symbol)
                                    .map_err(|e| TypeCheckError::new(e, prop.key.span))?;
                            }
                        }
                        Ok(())
                    }
                }
            }
            Pattern::Or(or_pattern) => {
                // Validate that all alternatives bind the same variables with compatible types
                self.validate_or_pattern_bindings(or_pattern, expected_type)?;

                // Type check and declare symbols from the first alternative only
                // All alternatives are guaranteed to have the same bindings due to validation above
                if let Some(first) = or_pattern.alternatives.first() {
                    self.check_pattern(first, expected_type)?;
                }

                Ok(())
            }
            Pattern::Template(template_pattern) => {
                use luanext_parser::ast::pattern::TemplatePatternPart;

                // Validate matched value is string type
                if !self.is_string_like_type(expected_type) {
                    self.diagnostic_handler.error(
                        template_pattern.span,
                        &format!(
                            "Template pattern can only match string values, but found type {:?}",
                            expected_type.kind
                        ),
                    );
                }

                // Register captures as string type
                for part in template_pattern.parts.iter() {
                    if let TemplatePatternPart::Capture(ident) = part {
                        let symbol = Symbol::new(
                            self.interner.resolve(ident.node).to_string(),
                            SymbolKind::Variable,
                            Type::new(TypeKind::Primitive(PrimitiveType::String), ident.span),
                            ident.span,
                        );
                        self.symbol_table
                            .declare(symbol)
                            .map_err(|e| TypeCheckError::new(e, ident.span))?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl<'a, 'arena> TypeInferrer<'a, 'arena> {
    /// Check if a type contains unresolved type parameters (References that aren't
    /// known types, interfaces, or classes). Used to guard the access_control fallback
    /// in infer_member so we don't return raw type annotations with unsubstituted
    /// type parameters from generic classes.
    fn type_has_unresolved_params(&self, ty: &Type<'arena>) -> bool {
        match &ty.kind {
            TypeKind::Reference(type_ref) => {
                let name = self.interner.resolve(type_ref.name.node);
                self.type_env.lookup_type(&name).is_none()
                    && self.access_control.get_class_members(&name).is_none()
            }
            TypeKind::Union(types) | TypeKind::Intersection(types) | TypeKind::Tuple(types) => {
                types.iter().any(|t| self.type_has_unresolved_params(t))
            }
            TypeKind::Array(elem) | TypeKind::Nullable(elem) | TypeKind::Parenthesized(elem) => {
                self.type_has_unresolved_params(elem)
            }
            _ => false,
        }
    }

    /// Check if a type is string-like (string primitive or string literal union)
    fn is_string_like_type(&self, ty: &Type<'arena>) -> bool {
        use luanext_parser::ast::expression::Literal;
        match &ty.kind {
            TypeKind::Primitive(PrimitiveType::String) => true,
            TypeKind::Literal(Literal::String(_)) => true,
            TypeKind::Union(types) => types.iter().all(|t| self.is_string_like_type(t)),
            _ => false,
        }
    }

    /// Check if a type has an operator overload for the given binary operation.
    /// Returns the operator's return type if found.
    fn check_operator_overload(
        &self,
        operand_type: &Type<'arena>,
        op: BinaryOp,
    ) -> Option<Type<'arena>> {
        let op_kind = match op {
            BinaryOp::Add => OperatorKind::Add,
            BinaryOp::Subtract => OperatorKind::Subtract,
            BinaryOp::Multiply => OperatorKind::Multiply,
            BinaryOp::Divide => OperatorKind::Divide,
            BinaryOp::Modulo => OperatorKind::Modulo,
            BinaryOp::Power => OperatorKind::Power,
            BinaryOp::IntegerDivide => OperatorKind::FloorDivide,
            BinaryOp::Concatenate => OperatorKind::Concatenate,
            BinaryOp::Equal => OperatorKind::Equal,
            BinaryOp::NotEqual => OperatorKind::NotEqual,
            BinaryOp::LessThan => OperatorKind::LessThan,
            BinaryOp::LessThanOrEqual => OperatorKind::LessThanOrEqual,
            BinaryOp::GreaterThan => OperatorKind::GreaterThan,
            BinaryOp::GreaterThanOrEqual => OperatorKind::GreaterThanOrEqual,
            BinaryOp::BitwiseAnd => OperatorKind::BitwiseAnd,
            BinaryOp::BitwiseOr => OperatorKind::BitwiseOr,
            BinaryOp::BitwiseXor => OperatorKind::BitwiseXor,
            BinaryOp::ShiftLeft => OperatorKind::ShiftLeft,
            BinaryOp::ShiftRight => OperatorKind::ShiftRight,
            _ => return None,
        };

        // Get the class name from the operand type
        let class_name = match &operand_type.kind {
            TypeKind::Reference(type_ref) => self.interner.resolve(type_ref.name.node),
            _ => return None,
        };

        // Look up class members for operator overloads
        let members = self.access_control.get_class_members(&class_name)?;
        for member in members {
            if let ClassMemberKind::Operator {
                operator,
                return_type,
                ..
            } = &member.kind
            {
                if *operator == op_kind {
                    return return_type.clone();
                }
            }
        }

        None
    }

    /// Extract all variable bindings from a pattern
    fn extract_pattern_bindings(
        &self,
        pattern: &Pattern<'arena>,
        expected_type: &Type<'arena>,
    ) -> Result<PatternBindings<'arena>, TypeCheckError> {
        let mut bindings = PatternBindings {
            bindings: FxHashMap::default(),
        };
        self.extract_pattern_bindings_recursive(pattern, expected_type, &mut bindings)?;
        Ok(bindings)
    }

    /// Recursive helper for extracting bindings from a pattern
    fn extract_pattern_bindings_recursive(
        &self,
        pattern: &Pattern<'arena>,
        expected_type: &Type<'arena>,
        bindings: &mut PatternBindings<'arena>,
    ) -> Result<(), TypeCheckError> {
        match pattern {
            Pattern::Identifier(ident) => {
                // Add binding for the identifier
                let name = self.interner.resolve(ident.node).to_string();
                let binding = PatternBinding {
                    typ: expected_type.clone(),
                    span: ident.span,
                };
                bindings.bindings.insert(name, binding);
                Ok(())
            }
            Pattern::Array(array_pattern) => {
                // Extract element type and recurse into elements
                let elem_type = match &expected_type.kind {
                    TypeKind::Array(et) => (*et).clone(),
                    _ => {
                        // If expected type is not an array, use Unknown as element type
                        // This allows us to extract bindings even when type info is incomplete
                        Type::new(
                            TypeKind::Primitive(PrimitiveType::Unknown),
                            expected_type.span,
                        )
                    }
                };

                for elem in array_pattern.elements.iter() {
                    match elem {
                        ArrayPatternElement::Pattern(PatternWithDefault {
                            pattern: pat, ..
                        }) => {
                            self.extract_pattern_bindings_recursive(pat, &elem_type, bindings)?;
                        }
                        ArrayPatternElement::Rest(ident) => {
                            let name = self.interner.resolve(ident.node).to_string();
                            let binding = PatternBinding {
                                typ: expected_type.clone(),
                                span: ident.span,
                            };
                            bindings.bindings.insert(name, binding);
                        }
                        ArrayPatternElement::Hole => {
                            // Hole doesn't bind anything
                        }
                    }
                }
                Ok(())
            }
            Pattern::Object(object_pattern) => {
                // Extract property types and recurse
                for prop in object_pattern.properties.iter() {
                    let prop_type = match &expected_type.kind {
                        TypeKind::Object(obj_type) => obj_type
                            .members
                            .iter()
                            .find_map(|member| {
                                if let ObjectTypeMember::Property(prop_sig) = member {
                                    if prop_sig.name.node == prop.key.node {
                                        return Some(prop_sig.type_annotation.clone());
                                    }
                                }
                                None
                            })
                            .unwrap_or_else(|| {
                                Type::new(TypeKind::Primitive(PrimitiveType::Unknown), prop.span)
                            }),
                        _ => {
                            // If expected type is not an object, use Unknown for property type
                            Type::new(TypeKind::Primitive(PrimitiveType::Unknown), prop.span)
                        }
                    };

                    if let Some(value_pattern) = &prop.value {
                        self.extract_pattern_bindings_recursive(
                            value_pattern,
                            &prop_type,
                            bindings,
                        )?;
                    } else {
                        // Shorthand: { x } means { x: x }
                        let name = self.interner.resolve(prop.key.node).to_string();
                        let binding = PatternBinding {
                            typ: prop_type,
                            span: prop.key.span,
                        };
                        bindings.bindings.insert(name, binding);
                    }
                }
                Ok(())
            }
            Pattern::Or(or_pattern) => {
                // For or-patterns, we'll handle this at a higher level
                // For now, just extract from the first alternative
                if let Some(first) = or_pattern.alternatives.first() {
                    self.extract_pattern_bindings_recursive(first, expected_type, bindings)?;
                }
                Ok(())
            }
            Pattern::Template(template_pattern) => {
                use luanext_parser::ast::pattern::TemplatePatternPart;
                // Extract captures as string type
                for part in template_pattern.parts.iter() {
                    if let TemplatePatternPart::Capture(ident) = part {
                        let name = self.interner.resolve(ident.node).to_string();
                        let binding = PatternBinding {
                            typ: Type::new(TypeKind::Primitive(PrimitiveType::String), ident.span),
                            span: ident.span,
                        };
                        bindings.bindings.insert(name, binding);
                    }
                }
                Ok(())
            }
            Pattern::Literal(_, _) | Pattern::Wildcard(_) => {
                // No bindings
                Ok(())
            }
        }
    }

    /// Validate that all alternatives in an or-pattern bind the same variables with compatible types
    fn validate_or_pattern_bindings(
        &self,
        or_pattern: &luanext_parser::ast::pattern::OrPattern<'arena>,
        expected_type: &Type<'arena>,
    ) -> Result<PatternBindings<'arena>, TypeCheckError> {
        use rustc_hash::FxHashSet;

        if or_pattern.alternatives.is_empty() {
            return Err(TypeCheckError::new(
                "Or-pattern must have at least one alternative",
                or_pattern.span,
            ));
        }

        // Extract bindings from first alternative (reference)
        let first_alt = &or_pattern.alternatives[0];
        let first_bindings = self.extract_pattern_bindings(first_alt, expected_type)?;

        // Check each subsequent alternative
        for (i, alt) in or_pattern.alternatives.iter().enumerate().skip(1) {
            let alt_bindings = self.extract_pattern_bindings(alt, expected_type)?;

            // Check 1: Same variable names
            let first_names: FxHashSet<&String> = first_bindings.bindings.keys().collect();
            let alt_names: FxHashSet<&String> = alt_bindings.bindings.keys().collect();

            // Variables in first but not in alt
            if let Some(missing) = first_names.difference(&alt_names).next() {
                return Err(TypeCheckError::new(
                    format!(
                        "Or-pattern alternative {} does not bind variable '{}' (bound in alternative 0)",
                        i, missing
                    ),
                    alt.span(),
                ));
            }

            // Variables in alt but not in first
            if let Some(extra) = alt_names.difference(&first_names).next() {
                return Err(TypeCheckError::new(
                    format!(
                        "Or-pattern alternative {} binds variable '{}' not present in alternative 0",
                        i, extra
                    ),
                    alt.span(),
                ));
            }

            // Check 2: Type compatibility for common variables
            for (name, first_binding) in &first_bindings.bindings {
                let alt_binding = &alt_bindings.bindings[name];

                // Types must be mutually assignable
                if !TypeCompatibility::is_assignable(&first_binding.typ, &alt_binding.typ)
                    && !TypeCompatibility::is_assignable(&alt_binding.typ, &first_binding.typ)
                {
                    return Err(TypeCheckError::new(
                        format!(
                            "Variable '{}' has incompatible types across or-pattern alternatives: {:?} vs {:?}",
                            name, first_binding.typ.kind, alt_binding.typ.kind
                        ),
                        alt_binding.span,
                    ));
                }
            }
        }

        Ok(first_bindings)
    }

    /// Check if an earlier pattern subsumes a later pattern
    /// Returns true if all values matching the later pattern would also match the earlier pattern
    fn pattern_subsumes(&self, earlier: &Pattern, later: &Pattern) -> bool {
        match (earlier, later) {
            // Wildcard and identifier always subsume everything
            (Pattern::Wildcard(_), _) | (Pattern::Identifier(_), _) => true,

            // Nothing subsumes wildcard/identifier (they're most general)
            (_, Pattern::Wildcard(_)) | (_, Pattern::Identifier(_)) => false,

            // Literal subsumption: exact match only
            (Pattern::Literal(a, _), Pattern::Literal(b, _)) => a == b,

            // Or-pattern subsumption cases
            (Pattern::Or(or1), Pattern::Or(or2)) => {
                self.or_pattern_subsumes_or_pattern(or1.alternatives, or2.alternatives)
            }
            (Pattern::Or(or_pat), later_pat) => {
                self.or_pattern_subsumes_pattern(or_pat.alternatives, later_pat)
            }
            (earlier_pat, Pattern::Or(or_pat)) => {
                self.pattern_subsumes_or_pattern(earlier_pat, or_pat.alternatives)
            }

            // Array pattern subsumption
            (Pattern::Array(arr1), Pattern::Array(arr2)) => self.array_pattern_subsumes(arr1, arr2),

            // Object pattern subsumption
            (Pattern::Object(obj1), Pattern::Object(obj2)) => {
                self.object_pattern_subsumes(obj1, obj2)
            }

            // Different pattern types don't subsume each other
            _ => false,
        }
    }

    /// Or-pattern subsumes single pattern if ANY alternative subsumes it
    fn or_pattern_subsumes_pattern(&self, or_alts: &[Pattern], later: &Pattern) -> bool {
        or_alts.iter().any(|alt| self.pattern_subsumes(alt, later))
    }

    /// Single pattern subsumes or-pattern if it subsumes ALL alternatives
    fn pattern_subsumes_or_pattern(&self, earlier: &Pattern, or_alts: &[Pattern]) -> bool {
        or_alts
            .iter()
            .all(|alt| self.pattern_subsumes(earlier, alt))
    }

    /// Or-pattern subsumes or-pattern if every later alternative is subsumed by some earlier alternative
    fn or_pattern_subsumes_or_pattern(
        &self,
        earlier_alts: &[Pattern],
        later_alts: &[Pattern],
    ) -> bool {
        later_alts.iter().all(|later_alt| {
            earlier_alts
                .iter()
                .any(|earlier_alt| self.pattern_subsumes(earlier_alt, later_alt))
        })
    }

    /// Array pattern subsumption
    fn array_pattern_subsumes(
        &self,
        earlier: &luanext_parser::ast::pattern::ArrayPattern,
        later: &luanext_parser::ast::pattern::ArrayPattern,
    ) -> bool {
        let earlier_elems = &earlier.elements;
        let later_elems = &later.elements;

        // Check if patterns have rest elements
        let earlier_has_rest = earlier_elems
            .iter()
            .any(|e| matches!(e, ArrayPatternElement::Rest(_)));
        let later_has_rest = later_elems
            .iter()
            .any(|e| matches!(e, ArrayPatternElement::Rest(_)));

        // If neither has rest, lengths must match
        if !earlier_has_rest && !later_has_rest && earlier_elems.len() != later_elems.len() {
            return false;
        }

        // If earlier has rest but later doesn't, earlier can match more cases
        // Need to check that later's elements match earlier's prefix
        if earlier_has_rest && !later_has_rest {
            // Find the position of the rest element in earlier
            if let Some(rest_pos) = earlier_elems
                .iter()
                .position(|e| matches!(e, ArrayPatternElement::Rest(_)))
            {
                // Check that later has at least rest_pos elements
                if later_elems.len() < rest_pos {
                    return false;
                }

                // Check element-by-element for the prefix
                for i in 0..rest_pos {
                    if !self.array_elements_subsume_single(&earlier_elems[i], &later_elems[i]) {
                        return false;
                    }
                }
                return true;
            }
        }

        // Element-by-element subsumption
        earlier_elems
            .iter()
            .zip(later_elems.iter())
            .all(|(e1, e2)| self.array_elements_subsume_single(e1, e2))
    }

    /// Check if array pattern element e1 subsumes e2
    fn array_elements_subsume_single(
        &self,
        e1: &ArrayPatternElement,
        e2: &ArrayPatternElement,
    ) -> bool {
        match (e1, e2) {
            (
                ArrayPatternElement::Pattern(PatternWithDefault { pattern: p1, .. }),
                ArrayPatternElement::Pattern(PatternWithDefault { pattern: p2, .. }),
            ) => self.pattern_subsumes(p1, p2),
            (ArrayPatternElement::Rest(_), ArrayPatternElement::Rest(_)) => true,
            (ArrayPatternElement::Hole, ArrayPatternElement::Hole) => true,
            _ => false,
        }
    }

    /// Object pattern subsumption
    fn object_pattern_subsumes(
        &self,
        earlier: &luanext_parser::ast::pattern::ObjectPattern,
        later: &luanext_parser::ast::pattern::ObjectPattern,
    ) -> bool {
        let earlier_props = &earlier.properties;
        let later_props = &later.properties;

        // Earlier must have ≤ properties (less constrained)
        if earlier_props.len() > later_props.len() {
            return false;
        }

        // Every property in earlier must subsume corresponding property in later
        earlier_props.iter().all(|earlier_prop| {
            later_props.iter().any(|later_prop| {
                // Properties must have same key
                if earlier_prop.key.node != later_prop.key.node {
                    return false;
                }

                // Check value pattern subsumption
                match (&earlier_prop.value, &later_prop.value) {
                    (Some(p1), Some(p2)) => self.pattern_subsumes(p1, p2),
                    (None, None) => true,     // Both are shorthand bindings
                    (None, Some(_)) => true,  // Earlier shorthand subsumes explicit pattern
                    (Some(_), None) => false, // Explicit pattern more specific
                }
            })
        })
    }

    /// Check for unreachable patterns in match arms
    fn check_unreachable_patterns(&self, arms: &[MatchArm<'arena>]) {
        for (i, arm) in arms.iter().enumerate() {
            // Skip checking arms with guards - they may not match
            if arm.guard.is_some() {
                continue;
            }

            // Check against all previous arms
            for (j, earlier_arm) in arms[..i].iter().enumerate() {
                // Earlier arms with guards don't guarantee subsumption
                if earlier_arm.guard.is_some() {
                    continue;
                }

                if self.pattern_subsumes(&earlier_arm.pattern, &arm.pattern) {
                    self.emit_unreachable_warning(i, j, earlier_arm, arm);
                    break; // Only warn once per unreachable pattern
                }
            }
        }
    }

    /// Emit a warning for an unreachable pattern
    fn emit_unreachable_warning(
        &self,
        _current_idx: usize,
        subsuming_idx: usize,
        earlier_arm: &MatchArm,
        current_arm: &MatchArm,
    ) {
        use crate::cli::diagnostics::error_codes::UNREACHABLE_PATTERN;

        let message = format!(
            "Pattern is unreachable because it is already covered by arm {} (line {})",
            subsuming_idx + 1,
            earlier_arm.pattern.span().line
        );

        let diagnostic =
            crate::cli::diagnostics::Diagnostic::warning(current_arm.pattern.span(), message)
                .with_code(UNREACHABLE_PATTERN);

        self.diagnostic_handler.report(diagnostic);
    }

    /// Check member access permissions
    fn check_member_access(
        &self,
        class_name: &str,
        member_name: &str,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        self.access_control.check_member_access(
            self.access_control.get_current_class(),
            class_name,
            member_name,
            span,
        )
    }

    /// Check if match arms are exhaustive for the given type
    /// Helper to collect all literals from a pattern, including those in or-patterns
    fn collect_pattern_literals<'b>(
        &self,
        pattern: &'b Pattern<'arena>,
        literals: &mut Vec<&'b Literal>,
    ) {
        match pattern {
            Pattern::Literal(lit, _) => {
                literals.push(lit);
            }
            Pattern::Or(or_pattern) => {
                // Recursively collect from all alternatives
                for alt in or_pattern.alternatives.iter() {
                    self.collect_pattern_literals(alt, literals);
                }
            }
            _ => {}
        }
    }

    fn check_exhaustiveness(
        &self,
        arms: &[MatchArm<'arena>],
        value_type: &Type<'arena>,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        // If there's a wildcard or identifier pattern without a guard, it's exhaustive
        let has_wildcard = arms.iter().any(|arm| {
            matches!(arm.pattern, Pattern::Wildcard(_) | Pattern::Identifier(_))
                && arm.guard.is_none()
        });

        if has_wildcard {
            return Ok(());
        }

        // Check exhaustiveness based on type
        match &value_type.kind {
            TypeKind::Primitive(PrimitiveType::Boolean) => {
                // Boolean must match both true and false
                let mut has_true = false;
                let mut has_false = false;

                for arm in arms {
                    let mut literals = Vec::new();
                    self.collect_pattern_literals(&arm.pattern, &mut literals);

                    for lit in literals {
                        if let Literal::Boolean(b) = lit {
                            if *b {
                                has_true = true;
                            } else {
                                has_false = true;
                            }
                        }
                    }
                }

                if !has_true || !has_false {
                    return Err(TypeCheckError::new(
                        "Non-exhaustive match: missing case for boolean type. Add patterns for both true and false, or use a wildcard (_) pattern.".to_string(),
                        span,
                    ));
                }
                Ok(())
            }
            TypeKind::Union(types) => {
                // For unions, we need to cover all union members
                // This is a simplified check - we verify that each union member has a potential match
                for union_type in types.iter() {
                    let covered = arms.iter().any(|arm| {
                        // Check if this arm could match this union member
                        self.pattern_could_match(&arm.pattern, union_type)
                    });

                    if !covered {
                        return Err(TypeCheckError::new(
                            format!("Non-exhaustive match: union type {:?} is not covered. Add a pattern to match this type or use a wildcard (_) pattern.", union_type.kind),
                            span,
                        ));
                    }
                }
                Ok(())
            }
            TypeKind::Literal(lit) => {
                // For literal types, must match exactly that literal
                let covered = arms.iter().any(|arm| {
                    let mut literals = Vec::new();
                    self.collect_pattern_literals(&arm.pattern, &mut literals);
                    literals.contains(&lit)
                });

                if !covered {
                    return Err(TypeCheckError::new(
                        format!("Non-exhaustive match: literal {:?} is not matched. Add a pattern to match this literal or use a wildcard (_) pattern.", lit),
                        span,
                    ));
                }
                Ok(())
            }
            // For other types, we can't easily verify exhaustiveness
            // Require a wildcard/identifier pattern or emit a warning
            _ => {
                // Emit a warning that exhaustiveness cannot be verified
                // For now, we'll allow it but this could be improved
                Ok(())
            }
        }
    }

    /// Helper to check if a pattern could match a type
    fn pattern_could_match(&self, pattern: &Pattern<'arena>, typ: &Type<'arena>) -> bool {
        match pattern {
            Pattern::Wildcard(_) | Pattern::Identifier(_) => true,
            Pattern::Literal(lit, _) => match &typ.kind {
                TypeKind::Literal(type_lit) => lit == type_lit,
                TypeKind::Primitive(PrimitiveType::Boolean) => matches!(lit, Literal::Boolean(_)),
                TypeKind::Primitive(PrimitiveType::Number) => matches!(lit, Literal::Number(_)),
                TypeKind::Primitive(PrimitiveType::String) => matches!(lit, Literal::String(_)),
                _ => false,
            },
            Pattern::Array(_) => matches!(typ.kind, TypeKind::Array(_) | TypeKind::Tuple(_)),
            Pattern::Object(_) => matches!(typ.kind, TypeKind::Object(_)),
            Pattern::Or(or_pattern) => {
                // Or-pattern matches if ANY alternative could match
                or_pattern
                    .alternatives
                    .iter()
                    .any(|alt| self.pattern_could_match(alt, typ))
            }
            Pattern::Template(_) => {
                // Template patterns match string types
                matches!(
                    typ.kind,
                    TypeKind::Primitive(PrimitiveType::String)
                        | TypeKind::Literal(Literal::String(_))
                )
            }
        }
    }

    /// Narrow the type based on the pattern
    fn narrow_type_by_pattern(
        &self,
        pattern: &Pattern<'arena>,
        typ: &Type<'arena>,
    ) -> Result<Type<'arena>, TypeCheckError> {
        match pattern {
            Pattern::Wildcard(_) | Pattern::Identifier(_) => {
                // No narrowing for wildcard or identifier
                Ok(typ.clone())
            }
            Pattern::Literal(lit, span) => {
                // Narrow to literal type
                Ok(Type::new(TypeKind::Literal(lit.clone()), *span))
            }
            Pattern::Array(_) => {
                // For array patterns, narrow to array type if it's a union
                match &typ.kind {
                    TypeKind::Union(types) => {
                        // Find the array type in the union
                        for t in types.iter() {
                            if matches!(t.kind, TypeKind::Array(_) | TypeKind::Tuple(_)) {
                                return Ok(t.clone());
                            }
                        }
                        // No array type found, return original
                        Ok(typ.clone())
                    }
                    _ => Ok(typ.clone()),
                }
            }
            Pattern::Object(obj_pattern) => {
                // For object patterns, narrow based on properties
                match &typ.kind {
                    TypeKind::Union(types) => {
                        // Find object types in the union that have the required properties
                        let matching_types: Vec<_> = types
                            .iter()
                            .filter(|t| {
                                if let TypeKind::Object(obj_type) = &t.kind {
                                    // Check if all pattern properties exist in this object type
                                    obj_pattern.properties.iter().all(|prop| {
                                        obj_type.members.iter().any(|member| {
                                            if let ObjectTypeMember::Property(prop_sig) = member {
                                                prop_sig.name.node == prop.key.node
                                            } else {
                                                false
                                            }
                                        })
                                    })
                                } else {
                                    false
                                }
                            })
                            .cloned()
                            .collect();

                        if matching_types.is_empty() {
                            Ok(typ.clone())
                        } else if matching_types.len() == 1 {
                            Ok(matching_types[0].clone())
                        } else {
                            let types = self.arena.alloc_slice_fill_iter(matching_types);
                            Ok(Type::new(TypeKind::Union(types), typ.span))
                        }
                    }
                    _ => Ok(typ.clone()),
                }
            }
            Pattern::Or(or_pattern) => {
                // Narrow to union of all narrowed alternative types
                let mut narrowed_types = Vec::new();

                for alt in or_pattern.alternatives.iter() {
                    let narrowed = self.narrow_type_by_pattern(alt, typ)?;
                    narrowed_types.push(narrowed);
                }

                // If all narrowed to same type, return single type
                if narrowed_types.len() == 1 {
                    Ok(narrowed_types[0].clone())
                } else {
                    // Different types - return union
                    let types = self.arena.alloc_slice_fill_iter(narrowed_types);
                    Ok(Type::new(TypeKind::Union(types), typ.span))
                }
            }
            Pattern::Template(_) => {
                // Template patterns narrow to string type
                // If the type is a union, extract the string component
                match &typ.kind {
                    TypeKind::Union(types) => {
                        for t in types.iter() {
                            if matches!(
                                t.kind,
                                TypeKind::Primitive(PrimitiveType::String)
                                    | TypeKind::Literal(Literal::String(_))
                            ) {
                                return Ok(t.clone());
                            }
                        }
                        // No string type found, return primitive string
                        Ok(Type::new(
                            TypeKind::Primitive(PrimitiveType::String),
                            typ.span,
                        ))
                    }
                    _ => Ok(typ.clone()),
                }
            }
        }
    }

    /// Infer the return type from a block by collecting all return statements
    /// Returns None if no return statements are found (void function)
    fn infer_block_return_type(
        &mut self,
        block: &Block<'arena>,
    ) -> Result<Option<Type<'arena>>, TypeCheckError> {
        self.infer_block_return_type_recursive(block)
    }

    /// Recursively collect return types from a block
    fn infer_block_return_type_recursive(
        &mut self,
        block: &Block<'arena>,
    ) -> Result<Option<Type<'arena>>, TypeCheckError> {
        let mut return_types: Vec<Type<'arena>> = Vec::new();

        for stmt in block.statements.iter() {
            match stmt {
                Statement::Return(return_stmt) => {
                    // Infer the type of the return expression(s)
                    if return_stmt.values.is_empty() {
                        // Void return
                        return_types.push(Type::new(
                            TypeKind::Primitive(PrimitiveType::Void),
                            return_stmt.span,
                        ));
                    } else if return_stmt.values.len() == 1 {
                        // Single return value
                        let typ = self.infer_expression(&return_stmt.values[0])?;
                        return_types.push(typ);
                    } else {
                        // Multiple return values - create a tuple
                        let mut tuple_types = Vec::new();
                        for expr in return_stmt.values.iter() {
                            let typ = self.infer_expression(expr)?;
                            tuple_types.push(typ);
                        }
                        let tuple_types = self.arena.alloc_slice_fill_iter(tuple_types.into_iter());
                        return_types
                            .push(Type::new(TypeKind::Tuple(tuple_types), return_stmt.span));
                    }
                }
                Statement::If(if_stmt) => {
                    // Check the then block
                    if let Some(then_type) =
                        self.infer_block_return_type_recursive(&if_stmt.then_block)?
                    {
                        return_types.push(then_type);
                    }

                    // Check else-if blocks
                    for else_if in if_stmt.else_ifs.iter() {
                        if let Some(else_if_type) =
                            self.infer_block_return_type_recursive(&else_if.block)?
                        {
                            return_types.push(else_if_type);
                        }
                    }

                    // Check else block
                    if let Some(else_block) = &if_stmt.else_block {
                        if let Some(else_type) =
                            self.infer_block_return_type_recursive(else_block)?
                        {
                            return_types.push(else_type);
                        }
                    }
                }
                Statement::Try(try_stmt) => {
                    // Check try block
                    if let Some(try_type) =
                        self.infer_block_return_type_recursive(&try_stmt.try_block)?
                    {
                        return_types.push(try_type);
                    }

                    // Check catch blocks
                    for catch in try_stmt.catch_clauses.iter() {
                        if let Some(catch_type) =
                            self.infer_block_return_type_recursive(&catch.body)?
                        {
                            return_types.push(catch_type);
                        }
                    }

                    // Check finally block (though finally typically doesn't return)
                    if let Some(finally) = &try_stmt.finally_block {
                        if let Some(finally_type) =
                            self.infer_block_return_type_recursive(finally)?
                        {
                            return_types.push(finally_type);
                        }
                    }
                }
                Statement::While(while_stmt) => {
                    if let Some(body_type) =
                        self.infer_block_return_type_recursive(&while_stmt.body)?
                    {
                        return_types.push(body_type);
                    }
                }
                Statement::Repeat(repeat_stmt) => {
                    if let Some(body_type) =
                        self.infer_block_return_type_recursive(&repeat_stmt.body)?
                    {
                        return_types.push(body_type);
                    }
                }
                Statement::For(for_stmt) => match *for_stmt {
                    luanext_parser::ast::statement::ForStatement::Numeric(numeric) => {
                        if let Some(body_type) =
                            self.infer_block_return_type_recursive(&numeric.body)?
                        {
                            return_types.push(body_type);
                        }
                    }
                    luanext_parser::ast::statement::ForStatement::Generic(ref generic) => {
                        if let Some(body_type) =
                            self.infer_block_return_type_recursive(&generic.body)?
                        {
                            return_types.push(body_type);
                        }
                    }
                },
                _ => {
                    // Other statements don't contain return statements at the top level
                    // but might contain them in nested expressions (like lambdas)
                }
            }
        }

        if return_types.is_empty() {
            Ok(None)
        } else if return_types.len() == 1 {
            Ok(Some(return_types[0].clone()))
        } else {
            // Multiple return types - try to find a common type
            // For now, create a union of all return types
            let return_types = self.arena.alloc_slice_fill_iter(return_types);
            Ok(Some(Type::new(TypeKind::Union(return_types), block.span)))
        }
    }

    /// Check the assertType<T>(value) intrinsic function call
    ///
    /// Validates:
    /// - Exactly one type argument provided
    /// - Exactly one value argument provided
    /// - Type argument is a checkable type (not generic type parameter)
    ///
    /// Returns the type argument T as the result type
    fn check_assert_type_intrinsic(
        &mut self,
        args: &[Argument<'arena>],
        type_args: Option<&'arena [Type<'arena>]>,
        span: Span,
    ) -> Result<Type<'arena>, TypeCheckError> {
        // Validate exactly one type argument
        let type_arg = match type_args {
            None => {
                return Err(TypeCheckError::new(
                    "assertType requires exactly one type argument (e.g., assertType<string>(value))".to_string(),
                    span,
                ));
            }
            Some([]) => {
                return Err(TypeCheckError::new(
                    "assertType requires exactly one type argument (e.g., assertType<string>(value))".to_string(),
                    span,
                ));
            }
            Some(type_args) if type_args.len() > 1 => {
                return Err(TypeCheckError::new(
                    format!(
                        "assertType expects exactly one type argument but received {}",
                        type_args.len()
                    ),
                    span,
                ));
            }
            Some(type_args) => &type_args[0],
        };

        // Validate exactly one value argument
        if args.is_empty() {
            return Err(TypeCheckError::new(
                "assertType requires exactly one argument (e.g., assertType<string>(value))"
                    .to_string(),
                span,
            ));
        }
        if args.len() > 1 {
            return Err(TypeCheckError::new(
                format!(
                    "assertType expects exactly one argument but received {}",
                    args.len()
                ),
                span,
            ));
        }

        // Validate the type argument is checkable (not a bare generic type parameter)
        // Allow: primitives, classes, interfaces, unions, optionals, literals, etc.
        // Disallow: bare type parameters (e.g., T in a generic function)
        if let TypeKind::Reference(type_ref) = &type_arg.kind {
            let type_name = self.interner.resolve(type_ref.name.node);
            // Check if this is a type parameter by looking it up in type_env
            // If it's not found in type_env, it might be a type parameter from a generic function
            // For now, we'll allow it through - runtime validation will use Unknown for type parameters
            // TODO: In a future phase, we could track type parameters more explicitly
            if self.type_env.lookup_type(&type_name).is_none() {
                // Check if it's a class or interface via symbol table
                if let Some(symbol) = self.symbol_table.lookup(&type_name) {
                    match symbol.kind {
                        crate::utils::symbol_table::SymbolKind::Class
                        | crate::utils::symbol_table::SymbolKind::Interface => {
                            // OK - it's a class or interface
                        }
                        _ => {
                            return Err(TypeCheckError::new(
                                format!("assertType cannot validate type parameter '{}' at runtime. Use a concrete type instead.", type_name),
                                span,
                            ));
                        }
                    }
                }
            }
        }

        // Type-check the value argument to ensure it's valid
        let _value_type = self.infer_expression(&args[0].value)?;

        // Narrow the argument variable if it's an identifier
        // This enables: assertType<string>(x); x.length // x is now string
        if let ExpressionKind::Identifier(var_name) = &args[0].value.kind {
            self.narrowing_context
                .set_narrowed_type(*var_name, type_arg.clone());
        }

        // The return type is the type argument T
        // This enables type narrowing: after assertType<string>(x), x is known to be string
        Ok(type_arg.clone())
    }
}

#[cfg(test)]
mod inference_tests;
