use super::super::visitors::{AccessControl, AccessControlVisitor, ClassMemberKind};
use super::TypeCheckVisitor;
use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_compat::TypeCompatibility;
use crate::core::type_environment::TypeEnvironment;
use crate::types::generics::infer_type_arguments;
use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::TypeCheckError;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tracing::{debug, error, instrument, span, Level};
use typedlua_parser::ast::expression::*;
use typedlua_parser::ast::pattern::{ArrayPatternElement, Pattern};
use typedlua_parser::ast::statement::{Block, OperatorKind, Statement};
use typedlua_parser::ast::types::*;
use typedlua_parser::prelude::{
    Argument, MatchArm, MatchArmBody, MatchExpression, PropertySignature,
};
use typedlua_parser::span::Span;
use typedlua_parser::string_interner::StringInterner;

/// Represents a variable binding from a pattern
#[derive(Debug, Clone)]
struct PatternBinding {
    typ: Type,
    span: Span,
}

/// Collection of bindings from a pattern
#[derive(Debug, Clone)]
struct PatternBindings {
    bindings: FxHashMap<String, PatternBinding>,
}

/// Trait for type inference operations
pub trait TypeInferenceVisitor: TypeCheckVisitor {
    /// Infer the type of an expression
    fn infer_expression(&mut self, expr: &mut Expression) -> Result<Type, TypeCheckError>;

    /// Infer type of binary operation
    fn infer_binary_op(
        &self,
        op: BinaryOp,
        left: &Type,
        right: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Infer type of unary operation
    fn infer_unary_op(
        &self,
        op: UnaryOp,
        operand: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Infer type of function call
    fn infer_call(
        &mut self,
        callee_type: &Type,
        args: &mut [Argument],
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Infer type of a method call on an object
    fn infer_method(
        &self,
        obj_type: &Type,
        method_name: &str,
        _args: &[Argument],
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Infer type of member access
    fn infer_member(
        &self,
        obj_type: &Type,
        member: &str,
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Infer type of index access
    fn infer_index(&self, obj_type: &Type, span: Span) -> Result<Type, TypeCheckError>;

    /// Make a type optional by adding nil to the union
    fn make_optional(&self, typ: Type, span: Span) -> Result<Type, TypeCheckError>;

    /// Remove nil from a type
    fn remove_nil(&self, typ: &Type, span: Span) -> Result<Type, TypeCheckError>;

    /// Check if a type is nil
    fn is_nil(&self, typ: &Type) -> bool;

    /// Infer type of null coalescing operation
    fn infer_null_coalesce(
        &self,
        left: &Type,
        right: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError>;

    /// Check match expression and return result type
    fn check_match(&mut self, match_expr: &mut MatchExpression) -> Result<Type, TypeCheckError>;

    /// Check a pattern and bind variables
    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected_type: &Type,
    ) -> Result<(), TypeCheckError>;
}

/// Type inference implementation
pub struct TypeInferrer<'a> {
    symbol_table: &'a mut SymbolTable,
    type_env: &'a mut TypeEnvironment,
    narrowing_context: &'a mut super::NarrowingContext,
    access_control: &'a AccessControl,
    interner: &'a StringInterner,
    diagnostic_handler: &'a Arc<dyn DiagnosticHandler>,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(
        symbol_table: &'a mut SymbolTable,
        type_env: &'a mut TypeEnvironment,
        narrowing_context: &'a mut super::NarrowingContext,
        access_control: &'a AccessControl,
        interner: &'a StringInterner,
        diagnostic_handler: &'a Arc<dyn DiagnosticHandler>,
    ) -> Self {
        Self {
            symbol_table,
            type_env,
            narrowing_context,
            access_control,
            interner,
            diagnostic_handler,
        }
    }
}

impl TypeCheckVisitor for TypeInferrer<'_> {
    fn name(&self) -> &'static str {
        "TypeInferrer"
    }
}

impl TypeInferenceVisitor for TypeInferrer<'_> {
    #[instrument(skip(self, expr), fields(expr_kind))]
    fn infer_expression(&mut self, expr: &mut Expression) -> Result<Type, TypeCheckError> {
        let span = expr.span;
        let expr_kind = format!("{:?}", expr.kind);

        span!(Level::DEBUG, "infer_expression", kind = %expr_kind);

        match &mut expr.kind {
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
                    Err(TypeCheckError::new(
                        format!("Undefined variable '{}'", name_str),
                        span,
                    ))
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

            ExpressionKind::Call(callee, args, ref mut stored_type_args) => {
                let callee_type = self.infer_expression(callee)?;

                // If callee is a generic function, infer and store type arguments
                if let TypeKind::Function(func_type) = &callee_type.kind {
                    if let Some(type_params) = &func_type.type_parameters {
                        // Infer argument types
                        let mut arg_types = Vec::with_capacity(args.len());
                        for arg in args.iter_mut() {
                            let arg_type =
                                self.infer_expression(&mut arg.value).unwrap_or_else(|_| {
                                    Type::new(
                                        TypeKind::Primitive(PrimitiveType::Unknown),
                                        arg.value.span,
                                    )
                                });
                            arg_types.push(arg_type);
                        }

                        // Infer type arguments from function signature and argument types
                        if let Ok(inferred_types) =
                            infer_type_arguments(type_params, &func_type.parameters, &arg_types)
                        {
                            *stored_type_args = Some(inferred_types);
                        }
                    }
                }

                self.infer_call(&callee_type, args, span)
            }

            ExpressionKind::MethodCall(object, method, args, _) => {
                let obj_type = self.infer_expression(object)?;
                let method_name = self.interner.resolve(method.node);
                let method_type = self.infer_method(&obj_type, &method_name, args, span)?;

                // Set receiver_class based on inferred type (not variable name)
                // This enables method-to-function conversion optimization
                if let TypeKind::Reference(type_ref) = &obj_type.kind {
                    let type_name = self.interner.resolve(type_ref.name.node);
                    // Only set for classes (not interfaces) - check class_members
                    if self.access_control.get_class_members(&type_name).is_some() {
                        expr.receiver_class = Some(ReceiverClassInfo {
                            class_name: type_ref.name.node,
                            is_static: false,
                        });
                    }
                }

                expr.annotated_type = Some(method_type.clone());
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

                let target_type = match &mut target.kind {
                    ExpressionKind::Member(object, member) => {
                        let obj_type = self.infer_expression(object.as_mut())?;
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
                            return Err(TypeCheckError::new(
                                format!("Undefined variable '{}'", name_str),
                                span,
                            ));
                        }
                    }
                    _ => Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span),
                };

                let value_type = self.infer_expression(value)?;

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

            ExpressionKind::OptionalCall(callee, args, ref mut stored_type_args) => {
                let callee_type = self.infer_expression(callee)?;

                // If callee is a generic function, infer and store type arguments
                if let TypeKind::Function(func_type) = &callee_type.kind {
                    if let Some(type_params) = &func_type.type_parameters {
                        let mut arg_types = Vec::with_capacity(args.len());
                        for arg in args.iter_mut() {
                            let arg_type =
                                self.infer_expression(&mut arg.value).unwrap_or_else(|_| {
                                    Type::new(
                                        TypeKind::Primitive(PrimitiveType::Unknown),
                                        arg.value.span,
                                    )
                                });
                            arg_types.push(arg_type);
                        }

                        if let Ok(inferred_types) =
                            infer_type_arguments(type_params, &func_type.parameters, &arg_types)
                        {
                            *stored_type_args = Some(inferred_types);
                        }
                    }
                }

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
                        TypeKind::Array(Box::new(Type::new(
                            TypeKind::Primitive(PrimitiveType::Unknown),
                            span,
                        ))),
                        span,
                    ));
                }

                // Collect all element types, including from spreads
                let mut element_types = Vec::new();

                for elem in elements {
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
                                    element_types.push((**elem_type).clone());
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
                        TypeKind::Array(Box::new(Type::new(
                            TypeKind::Primitive(PrimitiveType::Unknown),
                            span,
                        ))),
                        span,
                    ));
                }

                let mut result_type = element_types[0].clone();
                for elem_type in &element_types[1..] {
                    if !TypeCompatibility::is_assignable(&result_type, elem_type)
                        && !TypeCompatibility::is_assignable(elem_type, &result_type)
                    {
                        // Types are incompatible, create union
                        match &mut result_type.kind {
                            TypeKind::Union(types) => {
                                if !types
                                    .iter()
                                    .any(|t| TypeCompatibility::is_assignable(t, elem_type))
                                {
                                    types.push(elem_type.clone());
                                }
                            }
                            _ => {
                                result_type = Type::new(
                                    TypeKind::Union(vec![result_type.clone(), elem_type.clone()]),
                                    span,
                                );
                            }
                        }
                    }
                }

                Ok(Type::new(TypeKind::Array(Box::new(result_type)), span))
            }

            ExpressionKind::Object(props) => {
                // Infer object type from properties
                let mut members = Vec::new();

                for prop in props {
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
                                    for member in &obj_type.members {
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

                Ok(Type::new(
                    TypeKind::Object(ObjectType { members, span }),
                    span,
                ))
            }

            ExpressionKind::Function(func_expr) => {
                // Enter a new scope for the function expression
                self.symbol_table.enter_scope();

                // Register parameters in the scope
                for param in &func_expr.parameters {
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
                let mut body = func_expr.body.clone();
                let body_type = match self.infer_block_return_type(&mut body)? {
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
                    type_parameters: func_expr.type_parameters.clone(),
                    parameters: func_expr.parameters.clone(),
                    return_type: Box::new(
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
                for param in &arrow_fn.parameters {
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
                    ArrowBody::Expression(expr_box) => {
                        // Make a mutable copy to infer
                        let mut expr_copy = (**expr_box).clone();
                        self.infer_expression(&mut expr_copy)?
                    }
                    ArrowBody::Block(_block) => {
                        // Block bodies not fully supported yet
                        Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)
                    }
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
                    Ok(Type::new(TypeKind::Union(vec![then_type, else_type]), span))
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
                let expr_type = self.infer_expression(&mut try_expr.expression)?;
                let catch_type = self.infer_expression(&mut try_expr.catch_expression)?;

                if TypeCompatibility::is_assignable(&expr_type, &catch_type) {
                    Ok(catch_type)
                } else if TypeCompatibility::is_assignable(&catch_type, &expr_type) {
                    Ok(expr_type)
                } else {
                    Ok(Type::new(
                        TypeKind::Union(vec![expr_type, catch_type]),
                        span,
                    ))
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
                                name: typedlua_parser::ast::Spanned::new(*name, span),
                                type_arguments: type_args.clone(),
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

            _ => {
                // For unimplemented expression types, return unknown
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span))
            }
        }
    }

    fn infer_binary_op(
        &self,
        op: BinaryOp,
        left: &Type,
        right: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError> {
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
        _operand: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError> {
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
        callee_type: &Type,
        args: &mut [Argument],
        span: Span,
    ) -> Result<Type, TypeCheckError> {
        debug!(callee_type = ?callee_type.kind, "Inferring function call type");

        match &callee_type.kind {
            TypeKind::Function(func_type) => {
                // Check argument count
                let actual_args = args.len();
                debug!(actual_args, "Checking function call argument count");

                // Count required parameters (non-optional, non-rest)
                let required_params = func_type
                    .parameters
                    .iter()
                    .filter(|p| !p.is_rest && !p.is_optional)
                    .count();

                // Check if the last parameter is a rest parameter
                let has_rest_param = func_type
                    .parameters
                    .last()
                    .map(|p| p.is_rest)
                    .unwrap_or(false);

                // Count optional parameters
                let optional_params = func_type
                    .parameters
                    .iter()
                    .filter(|p| p.is_optional && !p.is_rest)
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
                for (i, arg) in args.iter_mut().enumerate() {
                    if i < func_type.parameters.len() {
                        let param = &func_type.parameters[i];

                        // Infer the argument type
                        if let Ok(arg_type) = self.infer_expression(&mut arg.value) {
                            if let Some(param_type) = &param.type_annotation {
                                // Check if argument type is assignable to parameter type
                                if !TypeCompatibility::is_assignable(&arg_type, param_type) {
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
        obj_type: &Type,
        method_name: &str,
        _args: &[Argument],
        span: Span,
    ) -> Result<Type, TypeCheckError> {
        // Look up the method in the object type
        match &obj_type.kind {
            TypeKind::Object(obj) => {
                for member in &obj.members {
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
        obj_type: &Type,
        member: &str,
        span: Span,
    ) -> Result<Type, TypeCheckError> {
        match &obj_type.kind {
            TypeKind::Reference(type_ref) => {
                let type_name = self.interner.resolve(type_ref.name.node);

                // Check if this is a generic type alias with type arguments
                if let Some(type_args) = &type_ref.type_arguments {
                    if let Some(generic_alias) = self.type_env.get_generic_type_alias(&type_name) {
                        // Instantiate the generic type alias with the provided type arguments
                        use crate::types::generics::instantiate_type;
                        let instantiated = instantiate_type(
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
                for obj_member in &obj.members {
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
                let non_nil_types: Vec<&Type> = types.iter().filter(|t| !self.is_nil(t)).collect();

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

    fn infer_index(&self, obj_type: &Type, span: Span) -> Result<Type, TypeCheckError> {
        match &obj_type.kind {
            TypeKind::Array(elem_type) => Ok((**elem_type).clone()),
            TypeKind::Tuple(types) => {
                // For now, return union of all tuple types
                if types.is_empty() {
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
                } else if types.len() == 1 {
                    Ok(types[0].clone())
                } else {
                    Ok(Type::new(TypeKind::Union(types.clone()), span))
                }
            }
            _ => Ok(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)),
        }
    }

    fn make_optional(&self, typ: Type, span: Span) -> Result<Type, TypeCheckError> {
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), span);
        Ok(Type::new(TypeKind::Union(vec![typ, nil_type]), span))
    }

    fn remove_nil(&self, typ: &Type, span: Span) -> Result<Type, TypeCheckError> {
        match &typ.kind {
            TypeKind::Union(types) => {
                let non_nil_types: Vec<Type> =
                    types.iter().filter(|t| !self.is_nil(t)).cloned().collect();
                if non_nil_types.is_empty() {
                    Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
                } else if non_nil_types.len() == 1 {
                    Ok(non_nil_types[0].clone())
                } else {
                    Ok(Type::new(TypeKind::Union(non_nil_types), span))
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

    fn is_nil(&self, typ: &Type) -> bool {
        match &typ.kind {
            TypeKind::Primitive(PrimitiveType::Nil) => true,
            TypeKind::Literal(Literal::Nil) => true,
            TypeKind::Nullable(inner) => self.is_nil(inner),
            _ => false,
        }
    }

    fn infer_null_coalesce(
        &self,
        left: &Type,
        right: &Type,
        span: Span,
    ) -> Result<Type, TypeCheckError> {
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
    fn check_match(&mut self, match_expr: &mut MatchExpression) -> Result<Type, TypeCheckError> {
        debug!(span = ?match_expr.span, "Checking match expression");

        // Type check the value being matched
        let value_type = self.infer_expression(&mut match_expr.value)?;
        debug!(value_type = ?value_type.kind, "Matched value type");

        if match_expr.arms.is_empty() {
            error!("Match expression has no arms");
            return Err(TypeCheckError::new(
                "Match expression must have at least one arm".to_string(),
                match_expr.span,
            ));
        }

        // Check exhaustiveness
        self.check_exhaustiveness(&match_expr.arms, &value_type, match_expr.span)?;

        // Check for unreachable patterns
        self.check_unreachable_patterns(&match_expr.arms);

        // Type check each arm and collect result types
        let mut arm_types = Vec::new();

        for arm in match_expr.arms.iter_mut() {
            // Enter a new scope for this arm
            self.symbol_table.enter_scope();

            // First check that the pattern is compatible with the value type
            self.check_pattern(&arm.pattern, &value_type)?;

            // Then narrow the type based on the pattern for variable bindings
            let _narrowed_type = self.narrow_type_by_pattern(&arm.pattern, &value_type)?;

            // Check the guard if present
            if let Some(guard) = &mut arm.guard {
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
            let arm_type = match &mut arm.body {
                MatchArmBody::Expression(expr) => self.infer_expression(expr)?,
                MatchArmBody::Block(block) => {
                    // Type check the block
                    for _stmt in &mut block.statements {
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
        let mut result_type = arm_types[0].clone();
        for arm_type in &arm_types[1..] {
            if TypeCompatibility::is_assignable(&result_type, arm_type) {
                // Keep result_type
            } else if TypeCompatibility::is_assignable(arm_type, &result_type) {
                result_type = arm_type.clone();
            } else {
                // Types are incompatible, create a union
                match &mut result_type.kind {
                    TypeKind::Union(types) => {
                        types.push(arm_type.clone());
                    }
                    _ => {
                        result_type = Type::new(
                            TypeKind::Union(vec![result_type.clone(), arm_type.clone()]),
                            match_expr.span,
                        );
                    }
                }
            }
        }

        Ok(result_type)
    }

    fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected_type: &Type,
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
                        for elem in &array_pattern.elements {
                            match elem {
                                ArrayPatternElement::Pattern(pat) => {
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
                        for prop in &object_pattern.properties {
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
                        for prop in &object_pattern.properties {
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
        }
    }
}

impl TypeInferrer<'_> {
    /// Check if a type contains unresolved type parameters (References that aren't
    /// known types, interfaces, or classes). Used to guard the access_control fallback
    /// in infer_member so we don't return raw type annotations with unsubstituted
    /// type parameters from generic classes.
    fn type_has_unresolved_params(&self, ty: &Type) -> bool {
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

    /// Check if a type has an operator overload for the given binary operation.
    /// Returns the operator's return type if found.
    fn check_operator_overload(&self, operand_type: &Type, op: BinaryOp) -> Option<Type> {
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
        pattern: &Pattern,
        expected_type: &Type,
    ) -> Result<PatternBindings, TypeCheckError> {
        let mut bindings = PatternBindings {
            bindings: FxHashMap::default(),
        };
        self.extract_pattern_bindings_recursive(pattern, expected_type, &mut bindings)?;
        Ok(bindings)
    }

    /// Recursive helper for extracting bindings from a pattern
    fn extract_pattern_bindings_recursive(
        &self,
        pattern: &Pattern,
        expected_type: &Type,
        bindings: &mut PatternBindings,
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
                let elem_type_box: Box<Type> = match &expected_type.kind {
                    TypeKind::Array(et) => et.clone(),
                    _ => {
                        // If expected type is not an array, use Unknown as element type
                        // This allows us to extract bindings even when type info is incomplete
                        Box::new(Type::new(
                            TypeKind::Primitive(PrimitiveType::Unknown),
                            expected_type.span,
                        ))
                    }
                };

                for elem in &array_pattern.elements {
                    match elem {
                        ArrayPatternElement::Pattern(pat) => {
                            self.extract_pattern_bindings_recursive(pat, &elem_type_box, bindings)?;
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
                for prop in &object_pattern.properties {
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
            Pattern::Literal(_, _) | Pattern::Wildcard(_) => {
                // No bindings
                Ok(())
            }
        }
    }

    /// Validate that all alternatives in an or-pattern bind the same variables with compatible types
    fn validate_or_pattern_bindings(
        &self,
        or_pattern: &typedlua_parser::ast::pattern::OrPattern,
        expected_type: &Type,
    ) -> Result<PatternBindings, TypeCheckError> {
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
                self.or_pattern_subsumes_or_pattern(&or1.alternatives, &or2.alternatives)
            }
            (Pattern::Or(or_pat), later_pat) => {
                self.or_pattern_subsumes_pattern(&or_pat.alternatives, later_pat)
            }
            (earlier_pat, Pattern::Or(or_pat)) => {
                self.pattern_subsumes_or_pattern(earlier_pat, &or_pat.alternatives)
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
        earlier: &typedlua_parser::ast::pattern::ArrayPattern,
        later: &typedlua_parser::ast::pattern::ArrayPattern,
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
            (ArrayPatternElement::Pattern(p1), ArrayPatternElement::Pattern(p2)) => {
                self.pattern_subsumes(p1, p2)
            }
            (ArrayPatternElement::Rest(_), ArrayPatternElement::Rest(_)) => true,
            (ArrayPatternElement::Hole, ArrayPatternElement::Hole) => true,
            _ => false,
        }
    }

    /// Object pattern subsumption
    fn object_pattern_subsumes(
        &self,
        earlier: &typedlua_parser::ast::pattern::ObjectPattern,
        later: &typedlua_parser::ast::pattern::ObjectPattern,
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
    fn check_unreachable_patterns(&self, arms: &[MatchArm]) {
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
    fn collect_pattern_literals<'a>(&self, pattern: &'a Pattern, literals: &mut Vec<&'a Literal>) {
        match pattern {
            Pattern::Literal(lit, _) => {
                literals.push(lit);
            }
            Pattern::Or(or_pattern) => {
                // Recursively collect from all alternatives
                for alt in &or_pattern.alternatives {
                    self.collect_pattern_literals(alt, literals);
                }
            }
            _ => {}
        }
    }

    fn check_exhaustiveness(
        &self,
        arms: &[MatchArm],
        value_type: &Type,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        // If there's a wildcard or identifier pattern without a guard, it's exhaustive
        let has_wildcard = arms.iter().any(|arm| {
            let is_wildcard = matches!(arm.pattern, Pattern::Wildcard(_) | Pattern::Identifier(_))
                && arm.guard.is_none();
            eprintln!(
                "DEBUG check_exhaustiveness: arm pattern = {:?}, is_wildcard = {}",
                arm.pattern, is_wildcard
            );
            is_wildcard
        });
        eprintln!(
            "DEBUG check_exhaustiveness: has_wildcard = {}",
            has_wildcard
        );

        if has_wildcard {
            return Ok(());
        }

        // Check exhaustiveness based on type
        eprintln!(
            "DEBUG check_exhaustiveness: value_type.kind = {:?}",
            value_type.kind
        );
        match &value_type.kind {
            TypeKind::Primitive(PrimitiveType::Boolean) => {
                // Boolean must match both true and false
                let mut has_true = false;
                let mut has_false = false;

                eprintln!(
                    "DEBUG exhaustiveness: checking {} arms for boolean",
                    arms.len()
                );
                for arm in arms {
                    // Collect all literals from the pattern, including those in or-patterns
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
                eprintln!(
                    "DEBUG exhaustiveness: has_true={}, has_false={}",
                    has_true, has_false
                );

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
                for union_type in types {
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
    fn pattern_could_match(&self, pattern: &Pattern, typ: &Type) -> bool {
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
        }
    }

    /// Narrow the type based on the pattern
    fn narrow_type_by_pattern(
        &self,
        pattern: &Pattern,
        typ: &Type,
    ) -> Result<Type, TypeCheckError> {
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
                        for t in types {
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
                            Ok(Type::new(TypeKind::Union(matching_types), typ.span))
                        }
                    }
                    _ => Ok(typ.clone()),
                }
            }
            Pattern::Or(or_pattern) => {
                // Narrow to union of all narrowed alternative types
                let mut narrowed_types = Vec::new();

                for alt in &or_pattern.alternatives {
                    let narrowed = self.narrow_type_by_pattern(alt, typ)?;
                    narrowed_types.push(narrowed);
                }

                // If all narrowed to same type, return single type
                if narrowed_types.len() == 1 {
                    Ok(narrowed_types[0].clone())
                } else {
                    // Different types - return union
                    Ok(Type::new(TypeKind::Union(narrowed_types), typ.span))
                }
            }
        }
    }

    /// Infer the return type from a block by collecting all return statements
    /// Returns None if no return statements are found (void function)
    fn infer_block_return_type(
        &mut self,
        block: &mut Block,
    ) -> Result<Option<Type>, TypeCheckError> {
        self.infer_block_return_type_recursive(block)
    }

    /// Recursively collect return types from a block
    fn infer_block_return_type_recursive(
        &mut self,
        block: &mut Block,
    ) -> Result<Option<Type>, TypeCheckError> {
        let mut return_types: Vec<Type> = Vec::new();

        for stmt in &mut block.statements {
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
                        let mut expr = return_stmt.values[0].clone();
                        let typ = self.infer_expression(&mut expr)?;
                        return_types.push(typ);
                    } else {
                        // Multiple return values - create a tuple
                        let mut tuple_types = Vec::new();
                        for expr in return_stmt.values.iter_mut() {
                            let mut expr_copy: Expression = expr.clone();
                            let typ = self.infer_expression(&mut expr_copy)?;
                            tuple_types.push(typ);
                        }
                        return_types
                            .push(Type::new(TypeKind::Tuple(tuple_types), return_stmt.span));
                    }
                }
                Statement::If(if_stmt) => {
                    // Check the then block
                    if let Some(then_type) =
                        self.infer_block_return_type_recursive(&mut if_stmt.then_block)?
                    {
                        return_types.push(then_type);
                    }

                    // Check else-if blocks
                    for else_if in &mut if_stmt.else_ifs {
                        if let Some(else_if_type) =
                            self.infer_block_return_type_recursive(&mut else_if.block)?
                        {
                            return_types.push(else_if_type);
                        }
                    }

                    // Check else block
                    if let Some(else_block) = &mut if_stmt.else_block {
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
                        self.infer_block_return_type_recursive(&mut try_stmt.try_block)?
                    {
                        return_types.push(try_type);
                    }

                    // Check catch blocks
                    for catch in &mut try_stmt.catch_clauses {
                        if let Some(catch_type) =
                            self.infer_block_return_type_recursive(&mut catch.body)?
                        {
                            return_types.push(catch_type);
                        }
                    }

                    // Check finally block (though finally typically doesn't return)
                    if let Some(finally) = &mut try_stmt.finally_block {
                        if let Some(finally_type) =
                            self.infer_block_return_type_recursive(finally)?
                        {
                            return_types.push(finally_type);
                        }
                    }
                }
                Statement::While(while_stmt) => {
                    if let Some(body_type) =
                        self.infer_block_return_type_recursive(&mut while_stmt.body)?
                    {
                        return_types.push(body_type);
                    }
                }
                Statement::Repeat(repeat_stmt) => {
                    if let Some(body_type) =
                        self.infer_block_return_type_recursive(&mut repeat_stmt.body)?
                    {
                        return_types.push(body_type);
                    }
                }
                Statement::For(for_stmt) => match &mut **for_stmt {
                    typedlua_parser::ast::statement::ForStatement::Numeric(numeric) => {
                        if let Some(body_type) =
                            self.infer_block_return_type_recursive(&mut numeric.body)?
                        {
                            return_types.push(body_type);
                        }
                    }
                    typedlua_parser::ast::statement::ForStatement::Generic(generic) => {
                        if let Some(body_type) =
                            self.infer_block_return_type_recursive(&mut generic.body)?
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
            Ok(Some(Type::new(TypeKind::Union(return_types), block.span)))
        }
    }
}

#[cfg(test)]
mod inference_tests;
