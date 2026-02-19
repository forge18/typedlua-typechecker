use luanext_parser::ast::statement::TypeParameter;
use luanext_parser::ast::types::{Type, TypeKind, TypeReference};
use luanext_parser::string_interner::StringId;
use rustc_hash::FxHashMap;

#[cfg(test)]
use luanext_parser::span::Span;

/// Substitutes type parameters with concrete types in a type
pub fn instantiate_type<'arena>(
    arena: &'arena bumpalo::Bump,
    typ: &Type<'arena>,
    type_params: &[TypeParameter<'arena>],
    type_args: &[Type<'arena>],
) -> Result<Type<'arena>, String> {
    if type_params.len() != type_args.len() {
        return Err(format!(
            "Expected {} type arguments, but got {}",
            type_params.len(),
            type_args.len()
        ));
    }

    // Build substitution map
    let mut substitutions: FxHashMap<StringId, Type<'arena>> = FxHashMap::default();
    for (param, arg) in type_params.iter().zip(type_args.iter()) {
        substitutions.insert(param.name.node, arg.clone());
    }

    substitute_type(arena, typ, &substitutions)
}

/// Recursively substitute type parameters in a type
fn substitute_type<'arena>(
    arena: &'arena bumpalo::Bump,
    typ: &Type<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> Result<Type<'arena>, String> {
    match &typ.kind {
        // If this is a type reference that matches a type parameter, substitute it
        TypeKind::Reference(type_ref) => {
            let name = type_ref.name.node;

            // Check if this is a type parameter
            if let Some(substituted) = substitutions.get(&name) {
                // Apply type arguments if present (e.g., for higher-kinded types)
                if let Some(args) = type_ref.type_arguments {
                    // This would be a higher-kinded type - not common, but we should handle it
                    // For now, just return an error
                    if !args.is_empty() {
                        return Err(format!(
                            "Type parameter {:?} cannot have type arguments",
                            name
                        ));
                    }
                }
                Ok(substituted.clone())
            } else {
                // Not a type parameter - recursively substitute in type arguments
                if let Some(args) = type_ref.type_arguments {
                    let substituted_args: Result<Vec<_>, _> = args
                        .iter()
                        .map(|arg| substitute_type(arena, arg, substitutions))
                        .collect();
                    let substituted_args = substituted_args?;

                    Ok(Type::new(
                        TypeKind::Reference(TypeReference {
                            name: type_ref.name.clone(),
                            type_arguments: Some(arena.alloc_slice_fill_iter(substituted_args)),
                            span: type_ref.span,
                        }),
                        typ.span,
                    ))
                } else {
                    Ok(typ.clone())
                }
            }
        }

        // Array type: substitute element type
        TypeKind::Array(elem) => {
            let substituted_elem = substitute_type(arena, elem, substitutions)?;
            Ok(Type::new(
                TypeKind::Array(arena.alloc(substituted_elem)),
                typ.span,
            ))
        }

        // Tuple type: substitute each element
        TypeKind::Tuple(elems) => {
            let substituted_elems: Result<Vec<_>, _> = elems
                .iter()
                .map(|elem| substitute_type(arena, elem, substitutions))
                .collect();

            Ok(Type::new(
                TypeKind::Tuple(arena.alloc_slice_fill_iter(substituted_elems?)),
                typ.span,
            ))
        }

        // Union type: substitute each member
        TypeKind::Union(members) => {
            let substituted_members: Result<Vec<_>, _> = members
                .iter()
                .map(|member| substitute_type(arena, member, substitutions))
                .collect();

            Ok(Type::new(
                TypeKind::Union(arena.alloc_slice_fill_iter(substituted_members?)),
                typ.span,
            ))
        }

        // Intersection type: substitute each member
        TypeKind::Intersection(members) => {
            let substituted_members: Result<Vec<_>, _> = members
                .iter()
                .map(|member| substitute_type(arena, member, substitutions))
                .collect();

            Ok(Type::new(
                TypeKind::Intersection(arena.alloc_slice_fill_iter(substituted_members?)),
                typ.span,
            ))
        }

        // Function type: substitute parameter and return types
        TypeKind::Function(func_type) => {
            use luanext_parser::ast::statement::Parameter;

            let substituted_params: Result<Vec<Parameter<'arena>>, String> = func_type
                .parameters
                .iter()
                .map(|param| {
                    if let Some(ref type_ann) = param.type_annotation {
                        let substituted = substitute_type(arena, type_ann, substitutions)?;
                        Ok(Parameter {
                            pattern: param.pattern.clone(),
                            type_annotation: Some(substituted),
                            default: param.default.clone(),
                            is_rest: param.is_rest,
                            is_optional: param.is_optional,
                            span: param.span,
                        })
                    } else {
                        Ok(param.clone())
                    }
                })
                .collect();

            let substituted_return = substitute_type(arena, func_type.return_type, substitutions)?;

            Ok(Type::new(
                TypeKind::Function(luanext_parser::ast::types::FunctionType {
                    type_parameters: None, // Type parameters are gone after substitution
                    parameters: arena.alloc_slice_fill_iter(substituted_params?),
                    return_type: arena.alloc(substituted_return),
                    throws: func_type.throws,
                    span: func_type.span,
                }),
                typ.span,
            ))
        }

        // Nullable type: substitute inner type
        TypeKind::Nullable(inner) => {
            let substituted_inner = substitute_type(arena, inner, substitutions)?;
            Ok(Type::new(
                TypeKind::Nullable(arena.alloc(substituted_inner)),
                typ.span,
            ))
        }

        // Parenthesized type: substitute inner type
        TypeKind::Parenthesized(inner) => {
            let substituted_inner = substitute_type(arena, inner, substitutions)?;
            Ok(Type::new(
                TypeKind::Parenthesized(arena.alloc(substituted_inner)),
                typ.span,
            ))
        }

        // Object type: substitute property type annotations
        TypeKind::Object(obj_type) => {
            use luanext_parser::ast::statement::{MethodSignature, PropertySignature};
            use luanext_parser::ast::types::ObjectTypeMember;

            let mut substituted_members: Vec<ObjectTypeMember<'arena>> = Vec::new();
            for member in obj_type.members.iter() {
                let substituted = match member {
                    ObjectTypeMember::Property(prop) => {
                        let substituted_type =
                            substitute_type(arena, &prop.type_annotation, substitutions)?;
                        ObjectTypeMember::Property(PropertySignature {
                            type_annotation: substituted_type,
                            ..prop.clone()
                        })
                    }
                    ObjectTypeMember::Method(method) => {
                        // For methods, substitute the return type
                        // Note: method parameters are handled separately during function type checking
                        let substituted_return =
                            substitute_type(arena, &method.return_type, substitutions)?;

                        ObjectTypeMember::Method(MethodSignature {
                            return_type: substituted_return,
                            ..method.clone()
                        })
                    }
                    ObjectTypeMember::Index(index) => {
                        // Index signatures have key_type and value_type
                        // key_type is IndexKeyType (String or Number), not Type
                        let substituted_value =
                            substitute_type(arena, &index.value_type, substitutions)?;

                        ObjectTypeMember::Index(luanext_parser::ast::statement::IndexSignature {
                            value_type: substituted_value,
                            ..index.clone()
                        })
                    }
                };
                substituted_members.push(substituted);
            }

            Ok(Type::new(
                TypeKind::Object(luanext_parser::ast::types::ObjectType {
                    members: arena.alloc_slice_fill_iter(substituted_members),
                    span: obj_type.span,
                }),
                typ.span,
            ))
        }

        // Conditional types, mapped types, etc. would need similar handling
        // For now, just clone types that don't contain type parameters
        _ => Ok(typ.clone()),
    }
}

/// Check if type arguments satisfy type parameter constraints
pub fn check_type_constraints<'arena>(
    type_params: &[TypeParameter<'arena>],
    type_args: &[Type<'arena>],
) -> Result<(), String> {
    if type_params.len() != type_args.len() {
        return Err(format!(
            "Expected {} type arguments, but got {}",
            type_params.len(),
            type_args.len()
        ));
    }

    for (param, arg) in type_params.iter().zip(type_args.iter()) {
        if let Some(constraint) = param.constraint {
            // Check if arg is assignable to constraint
            // This is a simplified check - a real implementation would use TypeCompatibility
            // For now, we'll just do a basic check
            if !is_type_compatible(arg, constraint) {
                return Err(format!(
                    "Type argument does not satisfy constraint for parameter '{}'",
                    param.name.node
                ));
            }
        }
    }

    Ok(())
}

/// Check if a type is compatible with a constraint
/// Uses the TypeCompatibility module for proper checking
fn is_type_compatible<'arena>(arg: &Type<'arena>, constraint: &Type<'arena>) -> bool {
    use crate::core::type_compat::TypeCompatibility;
    TypeCompatibility::is_assignable(arg, constraint)
}

/// Infer type arguments for a generic function from argument types
/// Returns a map from type parameter name to inferred type
pub fn infer_type_arguments<'arena>(
    type_params: &[TypeParameter<'arena>],
    function_params: &[luanext_parser::ast::statement::Parameter<'arena>],
    arg_types: &[Type<'arena>],
) -> Result<Vec<Type<'arena>>, String> {
    if function_params.len() != arg_types.len() {
        return Err(format!(
            "Expected {} arguments, got {}",
            function_params.len(),
            arg_types.len()
        ));
    }

    let mut inferred: FxHashMap<StringId, Type<'arena>> = FxHashMap::default();

    // For each parameter-argument pair, try to infer type arguments
    for (param, arg_type) in function_params.iter().zip(arg_types.iter()) {
        if let Some(param_type) = &param.type_annotation {
            infer_from_types(param_type, arg_type, &mut inferred)?;
        }
    }

    // Build result vector in the same order as type parameters
    type_params
        .iter()
        .map(|type_param| {
            inferred
                .get(&type_param.name.node)
                .cloned()
                .or_else(|| type_param.default.cloned())
                .ok_or_else(|| {
                    format!(
                        "Could not infer type argument for parameter '{:?}'",
                        type_param.name.node
                    )
                })
        })
        .collect()
}

/// Helper to infer type arguments by matching param_type pattern against arg_type
fn infer_from_types<'arena>(
    param_type: &Type<'arena>,
    arg_type: &Type<'arena>,
    inferred: &mut FxHashMap<StringId, Type<'arena>>,
) -> Result<(), String> {
    match &param_type.kind {
        // If parameter is a type reference (e.g., T), and it's a type parameter
        TypeKind::Reference(type_ref) if type_ref.type_arguments.is_none() => {
            // This might be a type parameter - record the inference
            let param_name = type_ref.name.node;

            // Check if we already inferred this type parameter
            if let Some(existing) = inferred.get(&param_name) {
                // Verify they match (simplified - should use proper type equality)
                if !types_equal(existing, arg_type) {
                    return Err(format!(
                        "Conflicting type inference for parameter '{:?}'",
                        param_name
                    ));
                }
            } else {
                inferred.insert(param_name, arg_type.clone());
            }
            Ok(())
        }

        // If parameter is Array<T>, and argument is Array<U>, infer T = U
        TypeKind::Array(elem_param) => {
            if let TypeKind::Array(elem_arg) = &arg_type.kind {
                infer_from_types(elem_param, elem_arg, inferred)
            } else {
                Ok(()) // Type mismatch, but don't error during inference
            }
        }

        // If parameter is a generic type application like Map<K, V>
        TypeKind::Reference(type_ref) if type_ref.type_arguments.is_some() => {
            if let TypeKind::Reference(arg_ref) = &arg_type.kind {
                // Names should match
                if type_ref.name.node == arg_ref.name.node {
                    if let (Some(param_args), Some(arg_args)) =
                        (&type_ref.type_arguments, &arg_ref.type_arguments)
                    {
                        // Infer from each type argument pair
                        for (p, a) in param_args.iter().zip(arg_args.iter()) {
                            infer_from_types(p, a, inferred)?;
                        }
                    }
                }
            }
            Ok(())
        }

        // For other types, no inference needed
        _ => Ok(()),
    }
}

/// Simple type equality check (simplified)
fn types_equal<'arena>(t1: &Type<'arena>, t2: &Type<'arena>) -> bool {
    // Simplified - just check if both are the same primitive
    match (&t1.kind, &t2.kind) {
        (TypeKind::Primitive(p1), TypeKind::Primitive(p2)) => p1 == p2,
        (TypeKind::Reference(r1), TypeKind::Reference(r2)) => r1.name.node == r2.name.node,
        _ => false, // For now, consider other types as not equal
    }
}

// =============================================================================
// Body Instantiation Functions for Generic Specialization
// =============================================================================

/// Build a substitution map from type parameters and type arguments
pub fn build_substitutions<'arena>(
    type_params: &[TypeParameter<'arena>],
    type_args: &[Type<'arena>],
) -> Result<FxHashMap<StringId, Type<'arena>>, String> {
    if type_params.len() != type_args.len() {
        return Err(format!(
            "Expected {} type arguments, but got {}",
            type_params.len(),
            type_args.len()
        ));
    }

    let mut substitutions: FxHashMap<StringId, Type<'arena>> = FxHashMap::default();
    for (param, arg) in type_params.iter().zip(type_args.iter()) {
        substitutions.insert(param.name.node, arg.clone());
    }
    Ok(substitutions)
}

/// Instantiate a block with type substitutions
/// Clones the block and substitutes type annotations in all statements
pub fn instantiate_block<'arena>(
    arena: &'arena bumpalo::Bump,
    block: &luanext_parser::ast::statement::Block<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::statement::Block<'arena> {
    use luanext_parser::ast::statement::Block;

    let stmts: Vec<_> = block
        .statements
        .iter()
        .map(|stmt| instantiate_statement(arena, stmt, substitutions))
        .collect();
    Block {
        statements: arena.alloc_slice_fill_iter(stmts),
        span: block.span,
    }
}

/// Instantiate a statement with type substitutions
pub fn instantiate_statement<'arena>(
    arena: &'arena bumpalo::Bump,
    stmt: &luanext_parser::ast::statement::Statement<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::statement::Statement<'arena> {
    use luanext_parser::ast::statement::{
        ElseIf, ForGeneric, ForNumeric, ForStatement, IfStatement, RepeatStatement,
        ReturnStatement, Statement, ThrowStatement, VariableDeclaration, WhileStatement,
    };

    match stmt {
        Statement::Variable(var_decl) => Statement::Variable(VariableDeclaration {
            kind: var_decl.kind,
            pattern: var_decl.pattern.clone(),
            type_annotation: var_decl
                .type_annotation
                .as_ref()
                .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
            initializer: instantiate_expression(arena, &var_decl.initializer, substitutions),
            span: var_decl.span,
        }),

        Statement::Function(func_decl) => Statement::Function(instantiate_function_declaration(
            arena,
            func_decl,
            substitutions,
        )),

        Statement::Expression(expr) => {
            Statement::Expression(instantiate_expression(arena, expr, substitutions))
        }

        Statement::Return(ret) => {
            let values: Vec<_> = ret
                .values
                .iter()
                .map(|e| instantiate_expression(arena, e, substitutions))
                .collect();
            Statement::Return(ReturnStatement {
                values: arena.alloc_slice_fill_iter(values),
                span: ret.span,
            })
        }

        Statement::If(if_stmt) => {
            let else_ifs: Vec<_> = if_stmt
                .else_ifs
                .iter()
                .map(|elif| ElseIf {
                    condition: instantiate_expression(arena, &elif.condition, substitutions),
                    block: instantiate_block(arena, &elif.block, substitutions),
                    span: elif.span,
                })
                .collect();
            Statement::If(IfStatement {
                condition: instantiate_expression(arena, &if_stmt.condition, substitutions),
                then_block: instantiate_block(arena, &if_stmt.then_block, substitutions),
                else_ifs: arena.alloc_slice_fill_iter(else_ifs),
                else_block: if_stmt
                    .else_block
                    .as_ref()
                    .map(|b| instantiate_block(arena, b, substitutions)),
                span: if_stmt.span,
            })
        }

        Statement::While(while_stmt) => Statement::While(WhileStatement {
            condition: instantiate_expression(arena, &while_stmt.condition, substitutions),
            body: instantiate_block(arena, &while_stmt.body, substitutions),
            span: while_stmt.span,
        }),

        Statement::For(for_stmt) => {
            let new_for = match *for_stmt {
                ForStatement::Numeric(num) => {
                    let new_num = ForNumeric {
                        variable: num.variable.clone(),
                        start: instantiate_expression(arena, &num.start, substitutions),
                        end: instantiate_expression(arena, &num.end, substitutions),
                        step: num
                            .step
                            .as_ref()
                            .map(|e| instantiate_expression(arena, e, substitutions)),
                        body: instantiate_block(arena, &num.body, substitutions),
                        span: num.span,
                    };
                    ForStatement::Numeric(arena.alloc(new_num))
                }
                ForStatement::Generic(ref gen) => {
                    let iterators: Vec<_> = gen
                        .iterators
                        .iter()
                        .map(|e| instantiate_expression(arena, e, substitutions))
                        .collect();
                    ForStatement::Generic(ForGeneric {
                        variables: gen.variables,
                        pattern: gen.pattern.clone(),
                        iterators: arena.alloc_slice_fill_iter(iterators),
                        body: instantiate_block(arena, &gen.body, substitutions),
                        span: gen.span,
                    })
                }
            };
            Statement::For(arena.alloc(new_for))
        }

        Statement::Repeat(repeat) => Statement::Repeat(RepeatStatement {
            body: instantiate_block(arena, &repeat.body, substitutions),
            until: instantiate_expression(arena, &repeat.until, substitutions),
            span: repeat.span,
        }),

        Statement::Block(block) => Statement::Block(instantiate_block(arena, block, substitutions)),

        Statement::Throw(throw) => Statement::Throw(ThrowStatement {
            expression: instantiate_expression(arena, &throw.expression, substitutions),
            span: throw.span,
        }),

        // Statements that don't contain type parameters or are complex - clone as-is
        Statement::Break(span) => Statement::Break(*span),
        Statement::Continue(span) => Statement::Continue(*span),
        Statement::Rethrow(span) => Statement::Rethrow(*span),
        Statement::Class(class_decl) => Statement::Class(class_decl.clone()),
        Statement::Interface(iface) => Statement::Interface(iface.clone()),
        Statement::TypeAlias(alias) => Statement::TypeAlias(alias.clone()),
        Statement::Enum(enum_decl) => Statement::Enum(enum_decl.clone()),
        Statement::Import(import) => Statement::Import(import.clone()),
        Statement::Export(export) => Statement::Export(export.clone()),
        Statement::Try(try_stmt) => Statement::Try(try_stmt.clone()),
        Statement::Namespace(ns) => Statement::Namespace(ns.clone()),
        Statement::DeclareFunction(df) => Statement::DeclareFunction(df.clone()),
        Statement::DeclareNamespace(dn) => Statement::DeclareNamespace(dn.clone()),
        Statement::DeclareType(dt) => Statement::DeclareType(dt.clone()),
        Statement::DeclareInterface(di) => Statement::DeclareInterface(di.clone()),
        Statement::DeclareConst(dc) => Statement::DeclareConst(dc.clone()),
        Statement::Label(l) => Statement::Label(l.clone()),
        Statement::Goto(g) => Statement::Goto(g.clone()),
        Statement::MultiAssignment(multi) => {
            let targets: Vec<_> = multi
                .targets
                .iter()
                .map(|e| instantiate_expression(arena, e, substitutions))
                .collect();
            let values: Vec<_> = multi
                .values
                .iter()
                .map(|e| instantiate_expression(arena, e, substitutions))
                .collect();
            Statement::MultiAssignment(luanext_parser::ast::statement::MultiAssignmentStatement {
                targets: arena.alloc_slice_fill_iter(targets),
                values: arena.alloc_slice_fill_iter(values),
                span: multi.span,
            })
        }
    }
}

/// Instantiate a function declaration with type substitutions
pub fn instantiate_function_declaration<'arena>(
    arena: &'arena bumpalo::Bump,
    func: &luanext_parser::ast::statement::FunctionDeclaration<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::statement::FunctionDeclaration<'arena> {
    let params: Vec<_> = func
        .parameters
        .iter()
        .map(|p| instantiate_parameter(arena, p, substitutions))
        .collect();
    luanext_parser::ast::statement::FunctionDeclaration {
        name: func.name.clone(),
        type_parameters: None, // Remove type parameters after specialization
        parameters: arena.alloc_slice_fill_iter(params),
        return_type: func
            .return_type
            .as_ref()
            .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
        body: instantiate_block(arena, &func.body, substitutions),
        throws: func.throws,
        span: func.span,
    }
}

/// Instantiate a parameter with type substitutions
pub fn instantiate_parameter<'arena>(
    arena: &'arena bumpalo::Bump,
    param: &luanext_parser::ast::statement::Parameter<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::statement::Parameter<'arena> {
    luanext_parser::ast::statement::Parameter {
        pattern: param.pattern.clone(),
        type_annotation: param
            .type_annotation
            .as_ref()
            .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
        default: param
            .default
            .as_ref()
            .map(|e| instantiate_expression(arena, e, substitutions)),
        is_rest: param.is_rest,
        is_optional: param.is_optional,
        span: param.span,
    }
}

/// Instantiate an expression with type substitutions
pub fn instantiate_expression<'arena>(
    arena: &'arena bumpalo::Bump,
    expr: &luanext_parser::ast::expression::Expression<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::Expression<'arena> {
    use luanext_parser::ast::expression::{Expression, ExpressionKind};

    let new_kind = match &expr.kind {
        ExpressionKind::Literal(lit) => ExpressionKind::Literal(lit.clone()),
        ExpressionKind::Identifier(id) => ExpressionKind::Identifier(*id),

        ExpressionKind::Binary(op, left, right) => ExpressionKind::Binary(
            *op,
            arena.alloc(instantiate_expression(arena, left, substitutions)),
            arena.alloc(instantiate_expression(arena, right, substitutions)),
        ),

        ExpressionKind::Unary(op, operand) => ExpressionKind::Unary(
            *op,
            arena.alloc(instantiate_expression(arena, operand, substitutions)),
        ),

        ExpressionKind::Assignment(target, op, value) => ExpressionKind::Assignment(
            arena.alloc(instantiate_expression(arena, target, substitutions)),
            *op,
            arena.alloc(instantiate_expression(arena, value, substitutions)),
        ),

        ExpressionKind::Call(callee, args, type_args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| instantiate_argument(arena, a, substitutions))
                .collect();
            let new_type_args = type_args.as_ref().map(|tas| {
                let v: Vec<_> = tas
                    .iter()
                    .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone()))
                    .collect();
                arena.alloc_slice_fill_iter(v) as &[_]
            });
            ExpressionKind::Call(
                arena.alloc(instantiate_expression(arena, callee, substitutions)),
                arena.alloc_slice_fill_iter(new_args),
                new_type_args,
            )
        }

        ExpressionKind::MethodCall(obj, method, args, type_args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| instantiate_argument(arena, a, substitutions))
                .collect();
            let new_type_args = type_args.as_ref().map(|tas| {
                let v: Vec<_> = tas
                    .iter()
                    .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone()))
                    .collect();
                arena.alloc_slice_fill_iter(v) as &[_]
            });
            ExpressionKind::MethodCall(
                arena.alloc(instantiate_expression(arena, obj, substitutions)),
                method.clone(),
                arena.alloc_slice_fill_iter(new_args),
                new_type_args,
            )
        }

        ExpressionKind::Member(obj, member) => ExpressionKind::Member(
            arena.alloc(instantiate_expression(arena, obj, substitutions)),
            member.clone(),
        ),

        ExpressionKind::Index(obj, index) => ExpressionKind::Index(
            arena.alloc(instantiate_expression(arena, obj, substitutions)),
            arena.alloc(instantiate_expression(arena, index, substitutions)),
        ),

        ExpressionKind::Array(elements) => {
            let elems: Vec<_> = elements
                .iter()
                .map(|elem| instantiate_array_element(arena, elem, substitutions))
                .collect();
            ExpressionKind::Array(arena.alloc_slice_fill_iter(elems))
        }

        ExpressionKind::Object(props) => {
            let new_props: Vec<_> = props
                .iter()
                .map(|prop| instantiate_object_property(arena, prop, substitutions))
                .collect();
            ExpressionKind::Object(arena.alloc_slice_fill_iter(new_props))
        }

        ExpressionKind::Function(func) => {
            ExpressionKind::Function(instantiate_function_expression(arena, func, substitutions))
        }

        ExpressionKind::Arrow(arrow) => {
            ExpressionKind::Arrow(instantiate_arrow_function(arena, arrow, substitutions))
        }

        ExpressionKind::Conditional(cond, then_expr, else_expr) => ExpressionKind::Conditional(
            arena.alloc(instantiate_expression(arena, cond, substitutions)),
            arena.alloc(instantiate_expression(arena, then_expr, substitutions)),
            arena.alloc(instantiate_expression(arena, else_expr, substitutions)),
        ),

        ExpressionKind::Pipe(left, right) => ExpressionKind::Pipe(
            arena.alloc(instantiate_expression(arena, left, substitutions)),
            arena.alloc(instantiate_expression(arena, right, substitutions)),
        ),

        ExpressionKind::Match(match_expr) => ExpressionKind::Match(instantiate_match_expression(
            arena,
            match_expr,
            substitutions,
        )),

        ExpressionKind::Parenthesized(inner) => ExpressionKind::Parenthesized(
            arena.alloc(instantiate_expression(arena, inner, substitutions)),
        ),

        ExpressionKind::TypeAssertion(expr_inner, typ) => ExpressionKind::TypeAssertion(
            arena.alloc(instantiate_expression(arena, expr_inner, substitutions)),
            substitute_type(arena, typ, substitutions).unwrap_or_else(|_| typ.clone()),
        ),

        ExpressionKind::OptionalMember(obj, member) => ExpressionKind::OptionalMember(
            arena.alloc(instantiate_expression(arena, obj, substitutions)),
            member.clone(),
        ),

        ExpressionKind::OptionalIndex(obj, index) => ExpressionKind::OptionalIndex(
            arena.alloc(instantiate_expression(arena, obj, substitutions)),
            arena.alloc(instantiate_expression(arena, index, substitutions)),
        ),

        ExpressionKind::OptionalCall(callee, args, type_args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| instantiate_argument(arena, a, substitutions))
                .collect();
            let new_type_args = type_args.as_ref().map(|tas| {
                let v: Vec<_> = tas
                    .iter()
                    .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone()))
                    .collect();
                arena.alloc_slice_fill_iter(v) as &[_]
            });
            ExpressionKind::OptionalCall(
                arena.alloc(instantiate_expression(arena, callee, substitutions)),
                arena.alloc_slice_fill_iter(new_args),
                new_type_args,
            )
        }

        ExpressionKind::OptionalMethodCall(obj, method, args, type_args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| instantiate_argument(arena, a, substitutions))
                .collect();
            let new_type_args = type_args.as_ref().map(|tas| {
                let v: Vec<_> = tas
                    .iter()
                    .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone()))
                    .collect();
                arena.alloc_slice_fill_iter(v) as &[_]
            });
            ExpressionKind::OptionalMethodCall(
                arena.alloc(instantiate_expression(arena, obj, substitutions)),
                method.clone(),
                arena.alloc_slice_fill_iter(new_args),
                new_type_args,
            )
        }

        ExpressionKind::Template(template) => {
            ExpressionKind::Template(instantiate_template_literal(arena, template, substitutions))
        }

        ExpressionKind::New(callee, args, type_args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| instantiate_argument(arena, a, substitutions))
                .collect();
            let new_type_args = type_args.as_ref().map(|tas| {
                let v: Vec<_> = tas
                    .iter()
                    .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone()))
                    .collect();
                arena.alloc_slice_fill_iter(v) as &[_]
            });
            ExpressionKind::New(
                arena.alloc(instantiate_expression(arena, callee, substitutions)),
                arena.alloc_slice_fill_iter(new_args),
                new_type_args,
            )
        }

        ExpressionKind::Try(try_expr) => {
            ExpressionKind::Try(instantiate_try_expression(arena, try_expr, substitutions))
        }

        ExpressionKind::ErrorChain(left, right) => ExpressionKind::ErrorChain(
            arena.alloc(instantiate_expression(arena, left, substitutions)),
            arena.alloc(instantiate_expression(arena, right, substitutions)),
        ),

        // Simple expression kinds - clone as-is
        ExpressionKind::SelfKeyword => ExpressionKind::SelfKeyword,
        ExpressionKind::SuperKeyword => ExpressionKind::SuperKeyword,
    };

    Expression {
        kind: new_kind,
        span: expr.span,
        annotated_type: expr
            .annotated_type
            .as_ref()
            .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
        receiver_class: expr.receiver_class.clone(),
    }
}

/// Helper to instantiate an argument
fn instantiate_argument<'arena>(
    arena: &'arena bumpalo::Bump,
    arg: &luanext_parser::ast::expression::Argument<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::Argument<'arena> {
    luanext_parser::ast::expression::Argument {
        value: instantiate_expression(arena, &arg.value, substitutions),
        is_spread: arg.is_spread,
        span: arg.span,
    }
}

/// Helper to instantiate an array element
fn instantiate_array_element<'arena>(
    arena: &'arena bumpalo::Bump,
    elem: &luanext_parser::ast::expression::ArrayElement<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::ArrayElement<'arena> {
    use luanext_parser::ast::expression::ArrayElement;
    match elem {
        ArrayElement::Expression(e) => {
            ArrayElement::Expression(instantiate_expression(arena, e, substitutions))
        }
        ArrayElement::Spread(e) => {
            ArrayElement::Spread(instantiate_expression(arena, e, substitutions))
        }
    }
}

/// Helper to instantiate an object property
fn instantiate_object_property<'arena>(
    arena: &'arena bumpalo::Bump,
    prop: &luanext_parser::ast::expression::ObjectProperty<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::ObjectProperty<'arena> {
    use luanext_parser::ast::expression::ObjectProperty;
    match prop {
        ObjectProperty::Property { key, value, span } => ObjectProperty::Property {
            key: key.clone(),
            value: arena.alloc(instantiate_expression(arena, value, substitutions)),
            span: *span,
        },
        ObjectProperty::Computed { key, value, span } => ObjectProperty::Computed {
            key: arena.alloc(instantiate_expression(arena, key, substitutions)),
            value: arena.alloc(instantiate_expression(arena, value, substitutions)),
            span: *span,
        },
        ObjectProperty::Spread { value, span } => ObjectProperty::Spread {
            value: arena.alloc(instantiate_expression(arena, value, substitutions)),
            span: *span,
        },
    }
}

/// Helper to instantiate a function expression
fn instantiate_function_expression<'arena>(
    arena: &'arena bumpalo::Bump,
    func: &luanext_parser::ast::expression::FunctionExpression<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::FunctionExpression<'arena> {
    let params: Vec<_> = func
        .parameters
        .iter()
        .map(|p| instantiate_parameter(arena, p, substitutions))
        .collect();
    luanext_parser::ast::expression::FunctionExpression {
        type_parameters: None, // Remove type parameters after specialization
        parameters: arena.alloc_slice_fill_iter(params),
        return_type: func
            .return_type
            .as_ref()
            .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
        body: instantiate_block(arena, &func.body, substitutions),
        span: func.span,
    }
}

/// Helper to instantiate an arrow function
fn instantiate_arrow_function<'arena>(
    arena: &'arena bumpalo::Bump,
    arrow: &luanext_parser::ast::expression::ArrowFunction<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::ArrowFunction<'arena> {
    use luanext_parser::ast::expression::{ArrowBody, ArrowFunction};
    let params: Vec<_> = arrow
        .parameters
        .iter()
        .map(|p| instantiate_parameter(arena, p, substitutions))
        .collect();
    ArrowFunction {
        parameters: arena.alloc_slice_fill_iter(params),
        return_type: arrow
            .return_type
            .as_ref()
            .map(|t| substitute_type(arena, t, substitutions).unwrap_or_else(|_| t.clone())),
        body: match &arrow.body {
            ArrowBody::Expression(e) => {
                ArrowBody::Expression(arena.alloc(instantiate_expression(arena, e, substitutions)))
            }
            ArrowBody::Block(b) => ArrowBody::Block(instantiate_block(arena, b, substitutions)),
        },
        span: arrow.span,
    }
}

/// Helper to instantiate a template literal
fn instantiate_template_literal<'arena>(
    arena: &'arena bumpalo::Bump,
    template: &luanext_parser::ast::expression::TemplateLiteral<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::TemplateLiteral<'arena> {
    use luanext_parser::ast::expression::{TemplateLiteral, TemplatePart};
    let parts: Vec<_> = template
        .parts
        .iter()
        .map(|part| match part {
            TemplatePart::String(s) => TemplatePart::String(s.clone()),
            TemplatePart::Expression(e) => TemplatePart::Expression(
                arena.alloc(instantiate_expression(arena, e, substitutions)),
            ),
        })
        .collect();
    TemplateLiteral {
        parts: arena.alloc_slice_fill_iter(parts),
        span: template.span,
    }
}

/// Helper to instantiate a match expression
fn instantiate_match_expression<'arena>(
    arena: &'arena bumpalo::Bump,
    match_expr: &luanext_parser::ast::expression::MatchExpression<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::MatchExpression<'arena> {
    use luanext_parser::ast::expression::{MatchArm, MatchArmBody, MatchExpression};
    let arms: Vec<_> = match_expr
        .arms
        .iter()
        .map(|arm| MatchArm {
            pattern: arm.pattern.clone(),
            guard: arm
                .guard
                .as_ref()
                .map(|e| instantiate_expression(arena, e, substitutions)),
            body: match &arm.body {
                MatchArmBody::Expression(e) => MatchArmBody::Expression(
                    arena.alloc(instantiate_expression(arena, e, substitutions)),
                ),
                MatchArmBody::Block(b) => {
                    MatchArmBody::Block(instantiate_block(arena, b, substitutions))
                }
            },
            span: arm.span,
        })
        .collect();
    MatchExpression {
        value: arena.alloc(instantiate_expression(
            arena,
            match_expr.value,
            substitutions,
        )),
        arms: arena.alloc_slice_fill_iter(arms),
        span: match_expr.span,
    }
}

/// Helper to instantiate a try expression
fn instantiate_try_expression<'arena>(
    arena: &'arena bumpalo::Bump,
    try_expr: &luanext_parser::ast::expression::TryExpression<'arena>,
    substitutions: &FxHashMap<StringId, Type<'arena>>,
) -> luanext_parser::ast::expression::TryExpression<'arena> {
    luanext_parser::ast::expression::TryExpression {
        expression: arena.alloc(instantiate_expression(
            arena,
            try_expr.expression,
            substitutions,
        )),
        catch_variable: try_expr.catch_variable.clone(),
        catch_expression: arena.alloc(instantiate_expression(
            arena,
            try_expr.catch_expression,
            substitutions,
        )),
        span: try_expr.span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;
    use luanext_parser::ast::types::{PrimitiveType, TypeKind};
    use luanext_parser::ast::Spanned;

    #[test]
    fn test_instantiate_simple_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        // Type parameter T
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Type reference T
        let type_ref_t = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned::new(t_id, span),
                type_arguments: None,
                span,
            }),
            span,
        );

        // Type argument: number
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Instantiate T with number
        let result = instantiate_type(
            &arena,
            &type_ref_t,
            &[type_param],
            std::slice::from_ref(&number_type),
        )
        .unwrap();

        // Result should be number
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_instantiate_array_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        // Type parameter T
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Array<T>
        let array_t = Type::new(
            TypeKind::Array(&*arena.alloc(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            ))),
            span,
        );

        // Type argument: string
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        // Instantiate Array<T> with string
        let result = instantiate_type(&arena, &array_t, &[type_param], &[string_type]).unwrap();

        // Result should be Array<string>
        match &result.kind {
            TypeKind::Array(elem) => {
                assert!(matches!(
                    elem.kind,
                    TypeKind::Primitive(PrimitiveType::String)
                ));
            }
            _ => panic!("Expected array type"),
        }
    }

    #[test]
    fn test_wrong_number_of_type_args() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        // Type parameter T
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let type_ref_t = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned::new(t_id, span),
                type_arguments: None,
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        // Try to instantiate with wrong number of type arguments
        let result = instantiate_type(
            &arena,
            &type_ref_t,
            &[type_param],
            &[number_type, string_type],
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_infer_type_arguments_simple() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let _x_id = interner.intern("x");

        // Type parameter T
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Function parameter: (value: T)
        let value_id = interner.intern("value");
        let func_param = Parameter {
            pattern: Pattern::Identifier(Spanned::new(value_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        // Argument type: number
        let arg_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Infer type arguments
        let result = infer_type_arguments(&[type_param], &[func_param], &[arg_type]);

        assert!(result.is_ok());
        let inferred = result.unwrap();
        assert_eq!(inferred.len(), 1);
        assert!(matches!(
            inferred[0].kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_type_arguments_array() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let values_id = interner.intern("values");

        // Type parameter T
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Function parameter: (values: Array<T>)
        let func_param = Parameter {
            pattern: Pattern::Identifier(Spanned::new(values_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Array(&*arena.alloc(Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ))),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        // Argument type: Array<string>
        let arg_type = Type::new(
            TypeKind::Array(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::String), span)),
            ),
            span,
        );

        // Infer type arguments
        let result = infer_type_arguments(&[type_param], &[func_param], &[arg_type]);

        assert!(result.is_ok());
        let inferred = result.unwrap();
        assert_eq!(inferred.len(), 1);
        assert!(matches!(
            inferred[0].kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_check_constraints_pass() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        // Type parameter T extends number
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            ),
            default: None,
            span,
        };

        // Type argument: number (should satisfy constraint)
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = check_type_constraints(&[type_param], &[number_type]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_constraints_fail() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        // Type parameter T extends number
        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            ),
            default: None,
            span,
        };

        // Type argument: string (should NOT satisfy constraint)
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = check_type_constraints(&[type_param], &[string_type]);
        assert!(result.is_err());
    }

    // ========================================================================
    // Additional Comprehensive Tests
    // ========================================================================

    #[test]
    fn test_build_substitutions_success() {
        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: None,
            default: None,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result =
            build_substitutions(&[type_param_t, type_param_u], &[number_type, string_type]);
        assert!(result.is_ok());

        let substitutions = result.unwrap();
        assert_eq!(substitutions.len(), 2);
        assert!(substitutions.contains_key(&t_id));
        assert!(substitutions.contains_key(&u_id));
    }

    #[test]
    fn test_build_substitutions_wrong_count() {
        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Provide wrong number of type arguments
        let result = build_substitutions(std::slice::from_ref(&type_param), &[]);
        assert!(result.is_err());

        let result = build_substitutions(&[type_param], &[number_type.clone(), number_type]);
        assert!(result.is_err());
    }

    #[test]
    fn test_instantiate_tuple_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Tuple<T, U>
        let tuple_type = Type::new(
            TypeKind::Tuple(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ),
                Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(u_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ),
            ])),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = instantiate_type(
            &arena,
            &tuple_type,
            &[type_param_t, type_param_u],
            &[number_type, string_type],
        )
        .unwrap();

        match &result.kind {
            TypeKind::Tuple(elems) => {
                assert_eq!(elems.len(), 2);
                assert!(matches!(
                    elems[0].kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                ));
                assert!(matches!(
                    elems[1].kind,
                    TypeKind::Primitive(PrimitiveType::String)
                ));
            }
            _ => panic!("Expected tuple type"),
        }
    }

    #[test]
    fn test_instantiate_union_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Union<T, nil>
        let union_type = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), span),
            ])),
            span,
        );

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = instantiate_type(&arena, &union_type, &[type_param], &[string_type]).unwrap();

        match &result.kind {
            TypeKind::Union(members) => {
                assert_eq!(members.len(), 2);
                assert!(matches!(
                    members[0].kind,
                    TypeKind::Primitive(PrimitiveType::String)
                ));
                assert!(matches!(
                    members[1].kind,
                    TypeKind::Primitive(PrimitiveType::Nil)
                ));
            }
            _ => panic!("Expected union type"),
        }
    }

    #[test]
    fn test_instantiate_function_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let param_id = interner.intern("x");
        let func_type = Type::new(
            TypeKind::Function(luanext_parser::ast::types::FunctionType {
                type_parameters: None,
                parameters: arena.alloc_slice_fill_iter([Parameter {
                    pattern: Pattern::Identifier(Spanned::new(param_id, span)),
                    type_annotation: Some(Type::new(
                        TypeKind::Reference(TypeReference {
                            name: Spanned::new(t_id, span),
                            type_arguments: None,
                            span,
                        }),
                        span,
                    )),
                    default: None,
                    is_rest: false,
                    is_optional: false,
                    span,
                }]),
                return_type: &*arena.alloc(Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                )),
                throws: None,
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &func_type, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Function(func) => {
                assert_eq!(func.parameters.len(), 1);
                assert!(func.type_parameters.is_none());
                // Parameter type should be number
                assert!(func.parameters[0].type_annotation.is_some());
                assert!(matches!(
                    func.parameters[0].type_annotation.as_ref().unwrap().kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                ));
                // Return type should be number
                assert!(matches!(
                    func.return_type.kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                ));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_instantiate_nullable_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Nullable<T>
        let nullable_type = Type::new(
            TypeKind::Nullable(&*arena.alloc(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            ))),
            span,
        );

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result =
            instantiate_type(&arena, &nullable_type, &[type_param], &[string_type]).unwrap();

        match &result.kind {
            TypeKind::Nullable(inner) => {
                assert!(matches!(
                    inner.kind,
                    TypeKind::Primitive(PrimitiveType::String)
                ));
            }
            _ => panic!("Expected nullable type"),
        }
    }

    #[test]
    fn test_instantiate_nested_generic() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Array<Array<T>>
        let nested_array = Type::new(
            TypeKind::Array(&*arena.alloc(Type::new(
                TypeKind::Array(&*arena.alloc(Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ))),
                span,
            ))),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result =
            instantiate_type(&arena, &nested_array, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Array(outer) => match &outer.kind {
                TypeKind::Array(inner) => {
                    assert!(matches!(
                        inner.kind,
                        TypeKind::Primitive(PrimitiveType::Number)
                    ));
                }
                _ => panic!("Expected nested array"),
            },
            _ => panic!("Expected array type"),
        }
    }

    #[test]
    fn test_infer_type_arguments_multiple_params() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Function parameters: (a: T, b: U)
        let a_id = interner.intern("a");
        let b_id = interner.intern("b");

        let param_a = Parameter {
            pattern: Pattern::Identifier(Spanned::new(a_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let param_b = Parameter {
            pattern: Pattern::Identifier(Spanned::new(b_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(u_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = infer_type_arguments(
            &[type_param_t, type_param_u],
            &[param_a, param_b],
            &[number_type, string_type],
        );

        assert!(result.is_ok());
        let inferred = result.unwrap();
        assert_eq!(inferred.len(), 2);
        assert!(matches!(
            inferred[0].kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
        assert!(matches!(
            inferred[1].kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_infer_type_arguments_with_default() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Type parameter U with default: string
        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: None,
            default: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::String), span)),
            ),
            span,
        };

        // Only one function parameter using T
        let a_id = interner.intern("a");
        let param_a = Parameter {
            pattern: Pattern::Identifier(Spanned::new(a_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Infer with only one argument - U should use default
        let result =
            infer_type_arguments(&[type_param_t, type_param_u], &[param_a], &[number_type]);

        assert!(result.is_ok());
        let inferred = result.unwrap();
        assert_eq!(inferred.len(), 2);
        assert!(matches!(
            inferred[0].kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
        assert!(matches!(
            inferred[1].kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_infer_type_arguments_wrong_arg_count() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let a_id = interner.intern("a");
        let param_a = Parameter {
            pattern: Pattern::Identifier(Spanned::new(a_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        // Wrong number of arguments
        let result = infer_type_arguments(
            std::slice::from_ref(&type_param),
            std::slice::from_ref(&param_a),
            &[],
        );
        assert!(result.is_err());

        let result = infer_type_arguments(
            &[type_param],
            &[param_a],
            &[number_type.clone(), number_type],
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_instantiate_block_empty() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let block = luanext_parser::ast::statement::Block {
            statements: &[],
            span,
        };

        let substitutions: FxHashMap<StringId, Type<'_>> = FxHashMap::default();
        let result = instantiate_block(&arena, &block, &substitutions);

        assert!(result.statements.is_empty());
    }

    #[test]
    fn test_instantiate_expression_literal() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let expr = luanext_parser::ast::expression::Expression {
            kind: luanext_parser::ast::expression::ExpressionKind::Literal(
                luanext_parser::ast::expression::Literal::Number(42.0),
            ),
            span,
            annotated_type: None,
            receiver_class: None,
        };

        let substitutions: FxHashMap<StringId, Type<'_>> = FxHashMap::default();
        let result = instantiate_expression(&arena, &expr, &substitutions);

        assert!(matches!(
            result.kind,
            luanext_parser::ast::expression::ExpressionKind::Literal(
                luanext_parser::ast::expression::Literal::Number(42.0)
            )
        ));
    }

    #[test]
    fn test_instantiate_parameter_with_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        use luanext_parser::ast::pattern::Pattern;

        let x_id = interner.intern("x");
        let param = luanext_parser::ast::statement::Parameter {
            pattern: Pattern::Identifier(Spanned::new(x_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let mut substitutions: FxHashMap<StringId, Type<'_>> = FxHashMap::default();
        substitutions.insert(t_id, number_type);

        let result = instantiate_parameter(&arena, &param, &substitutions);

        assert!(result.type_annotation.is_some());
        assert!(matches!(
            result.type_annotation.unwrap().kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_instantiate_parenthesized_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Parenthesized<T>
        let parenthesized_type = Type::new(
            TypeKind::Parenthesized(&*arena.alloc(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            ))),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result =
            instantiate_type(&arena, &parenthesized_type, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Parenthesized(inner) => {
                assert!(matches!(
                    inner.kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                ));
            }
            _ => panic!("Expected parenthesized type"),
        }
    }

    #[test]
    fn test_instantiate_intersection_type() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Intersection<T, U>
        let intersection_type = Type::new(
            TypeKind::Intersection(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(t_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ),
                Type::new(
                    TypeKind::Reference(TypeReference {
                        name: Spanned::new(u_id, span),
                        type_arguments: None,
                        span,
                    }),
                    span,
                ),
            ])),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = instantiate_type(
            &arena,
            &intersection_type,
            &[type_param_t, type_param_u],
            &[number_type, string_type],
        )
        .unwrap();

        match &result.kind {
            TypeKind::Intersection(members) => {
                assert_eq!(members.len(), 2);
                assert!(matches!(
                    members[0].kind,
                    TypeKind::Primitive(PrimitiveType::Number)
                ));
                assert!(matches!(
                    members[1].kind,
                    TypeKind::Primitive(PrimitiveType::String)
                ));
            }
            _ => panic!("Expected intersection type"),
        }
    }

    #[test]
    fn test_instantiate_object_type_with_property() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let value_id = interner.intern("value");

        let obj_type = Type::new(
            TypeKind::Object(luanext_parser::ast::types::ObjectType {
                members: arena.alloc_slice_fill_iter([
                    luanext_parser::ast::types::ObjectTypeMember::Property(
                        luanext_parser::ast::statement::PropertySignature {
                            name: Spanned::new(value_id, span),
                            type_annotation: Type::new(
                                TypeKind::Reference(TypeReference {
                                    name: Spanned::new(t_id, span),
                                    type_arguments: None,
                                    span,
                                }),
                                span,
                            ),
                            is_readonly: false,
                            is_optional: false,
                            span,
                        },
                    ),
                ]),
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &obj_type, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Object(obj) => {
                assert_eq!(obj.members.len(), 1);
                if let luanext_parser::ast::types::ObjectTypeMember::Property(prop) =
                    &obj.members[0]
                {
                    assert!(matches!(
                        prop.type_annotation.kind,
                        TypeKind::Primitive(PrimitiveType::Number)
                    ));
                } else {
                    panic!("Expected property member");
                }
            }
            _ => panic!("Expected object type"),
        }
    }

    #[test]
    fn test_instantiate_object_type_with_method() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let method_id = interner.intern("getValue");

        let obj_type = Type::new(
            TypeKind::Object(luanext_parser::ast::types::ObjectType {
                members: arena.alloc_slice_fill_iter([
                    luanext_parser::ast::types::ObjectTypeMember::Method(
                        luanext_parser::ast::statement::MethodSignature {
                            name: Spanned::new(method_id, span),
                            type_parameters: None,
                            parameters: &[],
                            return_type: Type::new(
                                TypeKind::Reference(TypeReference {
                                    name: Spanned::new(t_id, span),
                                    type_arguments: None,
                                    span,
                                }),
                                span,
                            ),
                            body: None,
                            span,
                        },
                    ),
                ]),
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &obj_type, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Object(obj) => {
                assert_eq!(obj.members.len(), 1);
                if let luanext_parser::ast::types::ObjectTypeMember::Method(method) =
                    &obj.members[0]
                {
                    assert!(matches!(
                        method.return_type.kind,
                        TypeKind::Primitive(PrimitiveType::Number)
                    ));
                } else {
                    panic!("Expected method member");
                }
            }
            _ => panic!("Expected object type"),
        }
    }

    #[test]
    fn test_instantiate_object_type_with_index_signature() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let key_id = interner.intern("key");

        let obj_type = Type::new(
            TypeKind::Object(luanext_parser::ast::types::ObjectType {
                members: arena.alloc_slice_fill_iter([
                    luanext_parser::ast::types::ObjectTypeMember::Index(
                        luanext_parser::ast::statement::IndexSignature {
                            key_name: Spanned::new(key_id, span),
                            key_type: luanext_parser::ast::statement::IndexKeyType::String,
                            value_type: Type::new(
                                TypeKind::Reference(TypeReference {
                                    name: Spanned::new(t_id, span),
                                    type_arguments: None,
                                    span,
                                }),
                                span,
                            ),
                            span,
                        },
                    ),
                ]),
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &obj_type, &[type_param], &[number_type]).unwrap();

        match &result.kind {
            TypeKind::Object(obj) => {
                assert_eq!(obj.members.len(), 1);
                if let luanext_parser::ast::types::ObjectTypeMember::Index(idx) = &obj.members[0] {
                    assert!(matches!(
                        idx.value_type.kind,
                        TypeKind::Primitive(PrimitiveType::Number)
                    ));
                } else {
                    panic!("Expected index member");
                }
            }
            _ => panic!("Expected object type"),
        }
    }

    #[test]
    fn test_substitute_type_with_type_args_error() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        // Type reference T with type arguments (should error)
        let type_ref_with_args = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned::new(t_id, span),
                type_arguments: Some(arena.alloc_slice_fill_iter([Type::new(
                    TypeKind::Primitive(PrimitiveType::Number),
                    span,
                )])),
                span,
            }),
            span,
        );

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &type_ref_with_args, &[type_param], &[number_type]);

        assert!(result.is_err());
    }

    #[test]
    fn test_instantiate_type_primitive() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);

        let primitive_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);

        let result = instantiate_type(&arena, &primitive_type, &[], &[]);

        assert!(result.is_ok());
        assert!(matches!(
            result.unwrap().kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_check_type_constraints_with_multiple_params() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            ),
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::String), span)),
            ),
            default: None,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result =
            check_type_constraints(&[type_param_t, type_param_u], &[number_type, string_type]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_type_constraints_second_param_fails() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let u_id = interner.intern("U");

        let type_param_t = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            ),
            default: None,
            span,
        };

        let type_param_u = TypeParameter {
            name: Spanned::new(u_id, span),
            constraint: Some(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::String), span)),
            ),
            default: None,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let boolean_type = Type::new(TypeKind::Primitive(PrimitiveType::Boolean), span);

        let result =
            check_type_constraints(&[type_param_t, type_param_u], &[number_type, boolean_type]);
        assert!(result.is_err());
    }

    #[test]
    fn test_infer_from_types_array_mismatch() {
        let arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);

        let param_type = Type::new(
            TypeKind::Array(
                &*arena.alloc(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
            ),
            span,
        );

        let arg_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let mut inferred: FxHashMap<StringId, Type<'_>> = FxHashMap::default();
        let result = infer_from_types(&param_type, &arg_type, &mut inferred);

        assert!(result.is_ok());
        assert!(inferred.is_empty());
    }

    #[test]
    fn test_types_equal_primitives() {
        let span = Span::new(0, 0, 0, 0);

        let num1 = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let num2 = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let str_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        assert!(types_equal(&num1, &num2));
        assert!(!types_equal(&num1, &str_type));
    }

    #[test]
    fn test_types_equal_references() {
        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");

        let ref1 = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned::new(t_id, span),
                type_arguments: None,
                span,
            }),
            span,
        );
        let ref2 = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned::new(t_id, span),
                type_arguments: None,
                span,
            }),
            span,
        );

        assert!(types_equal(&ref1, &ref2));
    }

    #[test]
    fn test_infer_type_arguments_conflict() {
        use luanext_parser::ast::pattern::Pattern;
        use luanext_parser::ast::statement::Parameter;

        let _arena = Bump::new();
        let span = Span::new(0, 0, 0, 0);
        let interner = luanext_parser::string_interner::StringInterner::new();
        let t_id = interner.intern("T");
        let x_id = interner.intern("x");

        let type_param = TypeParameter {
            name: Spanned::new(t_id, span),
            constraint: None,
            default: None,
            span,
        };

        let param = Parameter {
            pattern: Pattern::Identifier(Spanned::new(x_id, span)),
            type_annotation: Some(Type::new(
                TypeKind::Reference(TypeReference {
                    name: Spanned::new(t_id, span),
                    type_arguments: None,
                    span,
                }),
                span,
            )),
            default: None,
            is_rest: false,
            is_optional: false,
            span,
        };

        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), span);
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);

        let result = infer_type_arguments(&[type_param], &[param], &[number_type, string_type]);
        assert!(result.is_err());
    }
}
