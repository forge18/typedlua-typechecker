use rustc_hash::FxHashMap;
use typedlua_parser::ast::expression::Literal;
use typedlua_parser::ast::statement::{IndexKeyType, PropertySignature};
use typedlua_parser::ast::types::{
    MappedType, MappedTypeModifier, ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind,
};
use typedlua_parser::ast::Ident;
use typedlua_parser::span::Span;
use typedlua_parser::string_interner::StringInterner;

use crate::core::type_environment::TypeEnvironment;

/// Apply a utility type transformation
pub fn apply_utility_type<'arena>(
    arena: &'arena bumpalo::Bump,
    name: &str,
    type_args: &[Type<'arena>],
    span: Span,
    interner: &StringInterner,
    common_ids: &typedlua_parser::string_interner::CommonIdentifiers,
) -> Result<Type<'arena>, String> {
    match name {
        "Partial" => partial(arena, type_args, span),
        "Required" => required(arena, type_args, span),
        "Readonly" => readonly(arena, type_args, span),
        "Record" => record(arena, type_args, span, interner, common_ids),
        "Pick" => pick(arena, type_args, span, interner),
        "Omit" => omit(arena, type_args, span, interner),
        "Exclude" => exclude(arena, type_args, span),
        "Extract" => extract(arena, type_args, span),
        "NonNilable" => non_nilable(arena, type_args, span),
        "Nilable" => nilable(arena, type_args, span),
        "ReturnType" => return_type(type_args, span),
        "Parameters" => parameters(arena, type_args, span),
        _ => Err(format!("Unknown utility type: {}", name)),
    }
}

/// Partial<T> - Makes all properties in T optional
fn partial<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "Partial<T> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    match &typ.kind {
        TypeKind::Object(obj) => {
            let new_members: Vec<_> = obj
                .members
                .iter()
                .map(|member| {
                    match member {
                        ObjectTypeMember::Property(prop) => {
                            ObjectTypeMember::Property(PropertySignature {
                                is_readonly: prop.is_readonly,
                                name: prop.name.clone(),
                                is_optional: true, // Make optional
                                type_annotation: prop.type_annotation.clone(),
                                span: prop.span,
                            })
                        }
                        // Methods and index signatures remain unchanged
                        other => other.clone(),
                    }
                })
                .collect();

            Ok(Type::new(
                TypeKind::Object(ObjectType {
                    members: arena.alloc_slice_fill_iter(new_members),
                    span,
                }),
                span,
            ))
        }
        _ => Err("Partial<T> requires T to be an object type".to_string()),
    }
}

/// Required<T> - Makes all properties in T required (non-optional)
fn required<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "Required<T> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    match &typ.kind {
        TypeKind::Object(obj) => {
            let new_members: Vec<_> = obj
                .members
                .iter()
                .map(|member| {
                    match member {
                        ObjectTypeMember::Property(prop) => {
                            ObjectTypeMember::Property(PropertySignature {
                                is_readonly: prop.is_readonly,
                                name: prop.name.clone(),
                                is_optional: false, // Make required
                                type_annotation: prop.type_annotation.clone(),
                                span: prop.span,
                            })
                        }
                        other => other.clone(),
                    }
                })
                .collect();

            Ok(Type::new(
                TypeKind::Object(ObjectType {
                    members: arena.alloc_slice_fill_iter(new_members),
                    span,
                }),
                span,
            ))
        }
        _ => Err("Required<T> requires T to be an object type".to_string()),
    }
}

/// Readonly<T> - Makes all properties in T readonly
fn readonly<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "Readonly<T> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    match &typ.kind {
        TypeKind::Object(obj) => {
            let new_members: Vec<_> = obj
                .members
                .iter()
                .map(|member| {
                    match member {
                        ObjectTypeMember::Property(prop) => {
                            ObjectTypeMember::Property(PropertySignature {
                                is_readonly: true, // Make readonly
                                name: prop.name.clone(),
                                is_optional: prop.is_optional,
                                type_annotation: prop.type_annotation.clone(),
                                span: prop.span,
                            })
                        }
                        other => other.clone(),
                    }
                })
                .collect();

            Ok(Type::new(
                TypeKind::Object(ObjectType {
                    members: arena.alloc_slice_fill_iter(new_members),
                    span,
                }),
                span,
            ))
        }
        TypeKind::Array(_) => {
            // For arrays, we can wrap in a readonly wrapper
            // but for now, just return the same array (Lua doesn't enforce readonly)
            Ok(typ.clone())
        }
        _ => Err("Readonly<T> requires T to be an object or array type".to_string()),
    }
}

/// Record<K, V> - Constructs an object type with keys of type K and values of type V
fn record<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
    _interner: &StringInterner,
    common_ids: &typedlua_parser::string_interner::CommonIdentifiers,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 2 {
        return Err(format!(
            "Record<K, V> expects 2 type arguments, got {}",
            type_args.len()
        ));
    }

    let key_type = &type_args[0];
    let value_type = &type_args[1];

    // Validate key type is string or number and determine IndexKeyType
    let index_key_type = match &key_type.kind {
        TypeKind::Primitive(PrimitiveType::String) | TypeKind::Literal(Literal::String(_)) => {
            IndexKeyType::String
        }
        TypeKind::Primitive(PrimitiveType::Number)
        | TypeKind::Primitive(PrimitiveType::Integer)
        | TypeKind::Literal(Literal::Number(_)) => IndexKeyType::Number,
        TypeKind::Union(types) => {
            // Check if all union members are string literals
            if types
                .iter()
                .all(|t| matches!(t.kind, TypeKind::Literal(Literal::String(_))))
            {
                IndexKeyType::String
            } else {
                return Err(
                    "Record<K, V> requires K to be string, number, or a union of string literals"
                        .to_string(),
                );
            }
        }
        _ => {
            return Err(
                "Record<K, V> requires K to be string, number, or a union of string literals"
                    .to_string(),
            )
        }
    };

    // Create an object type with an index signature
    use typedlua_parser::ast::statement::IndexSignature;
    use typedlua_parser::ast::Ident;

    let key_id = common_ids.key;
    let index_sig = IndexSignature {
        key_name: Ident::new(key_id, span),
        key_type: index_key_type,
        value_type: value_type.clone(),
        span,
    };

    Ok(Type::new(
        TypeKind::Object(ObjectType {
            members: arena.alloc_slice_fill_iter([ObjectTypeMember::Index(index_sig)]),
            span,
        }),
        span,
    ))
}

/// Pick<T, K> - Picks a subset of properties from T
fn pick<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
    interner: &StringInterner,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 2 {
        return Err(format!(
            "Pick<T, K> expects 2 type arguments, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    let keys = &type_args[1];

    match &typ.kind {
        TypeKind::Object(obj) => {
            // Extract the property names to pick
            let keys_to_pick = extract_string_literal_keys(keys)?;

            let new_members: Vec<ObjectTypeMember<'arena>> = obj
                .members
                .iter()
                .filter_map(|member| {
                    match member {
                        ObjectTypeMember::Property(prop) => {
                            // Use interner to resolve StringId to actual string value
                            let prop_name = interner.resolve(prop.name.node);
                            if keys_to_pick.contains(&prop_name) {
                                Some(member.clone())
                            } else {
                                None
                            }
                        }
                        // Don't pick methods or index signatures
                        _ => None,
                    }
                })
                .collect();

            Ok(Type::new(
                TypeKind::Object(ObjectType {
                    members: arena.alloc_slice_fill_iter(new_members),
                    span,
                }),
                span,
            ))
        }
        _ => Err("Pick<T, K> requires T to be an object type".to_string()),
    }
}

/// Omit<T, K> - Omits properties from T
fn omit<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
    interner: &StringInterner,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 2 {
        return Err(format!(
            "Omit<T, K> expects 2 type arguments, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    let keys = &type_args[1];

    match &typ.kind {
        TypeKind::Object(obj) => {
            // Extract the property names to omit
            let keys_to_omit = extract_string_literal_keys(keys)?;

            let new_members: Vec<ObjectTypeMember<'arena>> = obj
                .members
                .iter()
                .filter_map(|member| {
                    match member {
                        ObjectTypeMember::Property(prop) => {
                            // Use interner to resolve StringId to actual string value
                            let prop_name = interner.resolve(prop.name.node);
                            if !keys_to_omit.contains(&prop_name) {
                                Some(member.clone())
                            } else {
                                None
                            }
                        }
                        // Keep methods and index signatures
                        other => Some(other.clone()),
                    }
                })
                .collect();

            Ok(Type::new(
                TypeKind::Object(ObjectType {
                    members: arena.alloc_slice_fill_iter(new_members),
                    span,
                }),
                span,
            ))
        }
        _ => Err("Omit<T, K> requires T to be an object type".to_string()),
    }
}

/// Exclude<T, U> - Excludes types from a union T that are assignable to U
fn exclude<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 2 {
        return Err(format!(
            "Exclude<T, U> expects 2 type arguments, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    let exclude_type = &type_args[1];

    match &typ.kind {
        TypeKind::Union(types) => {
            let remaining: Vec<Type<'arena>> = types
                .iter()
                .filter(|t| !is_assignable_to(t, exclude_type))
                .cloned()
                .collect();

            if remaining.is_empty() {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            } else if remaining.len() == 1 {
                Ok(remaining[0].clone())
            } else {
                Ok(Type::new(
                    TypeKind::Union(arena.alloc_slice_fill_iter(remaining)),
                    span,
                ))
            }
        }
        _ => {
            // If T is not a union, check if it's assignable to U
            if is_assignable_to(typ, exclude_type) {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            } else {
                Ok(typ.clone())
            }
        }
    }
}

/// Extract<T, U> - Extracts types from a union T that are assignable to U
fn extract<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 2 {
        return Err(format!(
            "Extract<T, U> expects 2 type arguments, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];
    let extract_type = &type_args[1];

    match &typ.kind {
        TypeKind::Union(types) => {
            let extracted: Vec<Type<'arena>> = types
                .iter()
                .filter(|t| is_assignable_to(t, extract_type))
                .cloned()
                .collect();

            if extracted.is_empty() {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            } else if extracted.len() == 1 {
                Ok(extracted[0].clone())
            } else {
                Ok(Type::new(
                    TypeKind::Union(arena.alloc_slice_fill_iter(extracted)),
                    span,
                ))
            }
        }
        _ => {
            // If T is not a union, check if it's assignable to U
            if is_assignable_to(typ, extract_type) {
                Ok(typ.clone())
            } else {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            }
        }
    }
}

/// NonNilable<T> - Removes nil and void from a type
fn non_nilable<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "NonNilable<T> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];

    match &typ.kind {
        TypeKind::Union(types) => {
            let non_nil: Vec<Type<'arena>> = types
                .iter()
                .filter(|t| !is_nil_or_void(t))
                .cloned()
                .collect();

            if non_nil.is_empty() {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            } else if non_nil.len() == 1 {
                Ok(non_nil[0].clone())
            } else {
                Ok(Type::new(
                    TypeKind::Union(arena.alloc_slice_fill_iter(non_nil)),
                    span,
                ))
            }
        }
        TypeKind::Nullable(inner) => Ok((**inner).clone()),
        _ => {
            if is_nil_or_void(typ) {
                Ok(Type::new(TypeKind::Primitive(PrimitiveType::Never), span))
            } else {
                Ok(typ.clone())
            }
        }
    }
}

/// Nilable<T> - Adds nil to a type (equivalent to T | nil)
fn nilable<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "Nilable<T> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];

    // Check if it's already nilable
    if is_nil_or_void(typ) {
        return Ok(typ.clone());
    }

    match &typ.kind {
        TypeKind::Union(types) => {
            // Check if nil is already in the union
            if types.iter().any(is_nil_or_void) {
                Ok(typ.clone())
            } else {
                let mut new_types: Vec<_> = types.to_vec();
                new_types.push(Type::new(TypeKind::Primitive(PrimitiveType::Nil), span));
                Ok(Type::new(
                    TypeKind::Union(arena.alloc_slice_fill_iter(new_types)),
                    span,
                ))
            }
        }
        TypeKind::Nullable(_) => {
            // Already nullable
            Ok(typ.clone())
        }
        _ => Ok(Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                typ.clone(),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), span),
            ])),
            span,
        )),
    }
}

/// ReturnType<F> - Extracts the return type from a function type
fn return_type<'arena>(type_args: &[Type<'arena>], _span: Span) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "ReturnType<F> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];

    match &typ.kind {
        TypeKind::Function(ref func) => Ok((*func.return_type).clone()),
        _ => Err("ReturnType<F> requires F to be a function type".to_string()),
    }
}

/// Parameters<F> - Extracts parameter types from a function as a tuple
fn parameters<'arena>(
    arena: &'arena bumpalo::Bump,
    type_args: &[Type<'arena>],
    span: Span,
) -> Result<Type<'arena>, String> {
    if type_args.len() != 1 {
        return Err(format!(
            "Parameters<F> expects 1 type argument, got {}",
            type_args.len()
        ));
    }

    let typ = &type_args[0];

    match &typ.kind {
        TypeKind::Function(ref func) => {
            let param_types: Vec<Type<'arena>> = func
                .parameters
                .iter()
                .filter_map(|p| p.type_annotation.clone())
                .collect();

            Ok(Type::new(
                TypeKind::Tuple(arena.alloc_slice_fill_iter(param_types)),
                span,
            ))
        }
        _ => Err("Parameters<F> requires F to be a function type".to_string()),
    }
}

/// Evaluate a mapped type: { [K in T]: V }
/// Transforms the mapped type into a concrete object type
pub fn evaluate_mapped_type<'arena>(
    arena: &'arena bumpalo::Bump,
    mapped: &MappedType<'arena>,
    type_env: &TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<Type<'arena>, String> {
    // Resolve the 'in' type if it's a KeyOf expression
    let in_type_resolved = match &mapped.in_type.kind {
        TypeKind::KeyOf(operand) => {
            // Evaluate keyof to get the union of string literals
            evaluate_keyof(arena, operand, type_env, interner)?
        }
        _ => (*mapped.in_type).clone(),
    };

    // Extract the keys from the resolved 'in' clause
    let keys = extract_keys_from_type(&in_type_resolved, type_env, interner)?;

    let members: Vec<_> = keys
        .iter()
        .map(|key| {
            let key_id = interner.intern(key);

            // Determine readonly status based on modifier
            let is_readonly = match mapped.readonly_modifier {
                MappedTypeModifier::Add => true,
                MappedTypeModifier::Remove => false,
                MappedTypeModifier::None => false,
            };

            // Determine optional status based on modifier
            let is_optional = match mapped.optional_modifier {
                MappedTypeModifier::Add => true,
                MappedTypeModifier::Remove => false,
                MappedTypeModifier::None => false,
            };

            ObjectTypeMember::Property(PropertySignature {
                is_readonly,
                name: Ident::new(key_id, mapped.span),
                is_optional,
                type_annotation: (*mapped.value_type).clone(),
                span: mapped.span,
            })
        })
        .collect();

    Ok(Type::new(
        TypeKind::Object(ObjectType {
            members: arena.alloc_slice_fill_iter(members),
            span: mapped.span,
        }),
        mapped.span,
    ))
}

/// Evaluate keyof operator - extracts property names from an object type
pub fn evaluate_keyof<'arena>(
    arena: &'arena bumpalo::Bump,
    typ: &Type<'arena>,
    type_env: &TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<Type<'arena>, String> {
    // Resolve type reference first
    let resolved_type = match &typ.kind {
        TypeKind::Reference(type_ref) => {
            let type_name = interner.resolve(type_ref.name.node);
            match type_env.lookup_type(&type_name) {
                Some(t) => t.clone(),
                None => return Err(format!("Type '{}' not found", type_name)),
            }
        }
        _ => typ.clone(),
    };

    match &resolved_type.kind {
        TypeKind::Object(obj) => {
            let keys: Vec<_> = obj
                .members
                .iter()
                .filter_map(|member| match member {
                    ObjectTypeMember::Property(prop) => Some(Type::new(
                        TypeKind::Literal(Literal::String(prop.name.node.to_string())),
                        prop.span,
                    )),
                    ObjectTypeMember::Method(method) => Some(Type::new(
                        TypeKind::Literal(Literal::String(method.name.node.to_string())),
                        method.span,
                    )),
                    // Index signatures don't contribute to keyof
                    ObjectTypeMember::Index(_) => None,
                })
                .collect();

            if keys.is_empty() {
                Ok(Type::new(
                    TypeKind::Primitive(PrimitiveType::Never),
                    typ.span,
                ))
            } else if keys.len() == 1 {
                Ok(keys.into_iter().next().unwrap())
            } else {
                Ok(Type::new(
                    TypeKind::Union(arena.alloc_slice_fill_iter(keys)),
                    resolved_type.span,
                ))
            }
        }
        _ => Err(format!(
            "keyof requires an object type, got {:?}",
            resolved_type.kind
        )),
    }
}

/// Evaluate a conditional type: T extends U ? X : Y
/// Also handles infer keyword: T extends Array<infer U> ? U : never
pub fn evaluate_conditional_type<'arena>(
    arena: &'arena bumpalo::Bump,
    conditional: &typedlua_parser::ast::types::ConditionalType<'arena>,
    type_env: &TypeEnvironment<'arena>,
) -> Result<Type<'arena>, String> {
    use crate::core::type_compat::TypeCompatibility;
    use rustc_hash::FxHashMap;

    // Check if check_type extends extends_type
    let check_type = &conditional.check_type;
    let extends_type = &conditional.extends_type;

    // Check if extends_type contains infer - if so, we need pattern matching
    let mut inferred_types: FxHashMap<String, Type<'arena>> = FxHashMap::default();
    let has_infer = contains_infer(extends_type);

    if has_infer {
        // Try to match check_type against extends_type pattern and extract inferred types
        if try_match_and_infer(check_type, extends_type, &mut inferred_types, type_env) {
            // Match succeeded - evaluate true branch with inferred types
            return substitute_inferred_types(arena, conditional.true_type, &inferred_types);
        } else {
            // Match failed - return false branch
            return Ok((*conditional.false_type).clone());
        }
    }

    // Handle distributive conditional types
    // If check_type is a union, distribute the conditional over each member
    if let TypeKind::Union(union_types) = &check_type.kind {
        let result_types: Vec<_> = union_types
            .iter()
            .map(|member_type| {
                // Create a new conditional for each union member
                let member_conditional = typedlua_parser::ast::types::ConditionalType {
                    check_type: arena.alloc(member_type.clone()),
                    extends_type: conditional.extends_type,
                    true_type: conditional.true_type,
                    false_type: conditional.false_type,
                    span: conditional.span,
                };

                evaluate_conditional_type(arena, &member_conditional, type_env)
            })
            .collect::<Result<Vec<_>, _>>()?;

        // If all results are the same, return just one
        // Otherwise, return a union
        if result_types.len() == 1 {
            return Ok(result_types.into_iter().next().unwrap());
        }

        // Check if all types are the same (simplified check)
        let all_same = result_types
            .windows(2)
            .all(|w| types_structurally_equal(&w[0], &w[1]));

        if all_same {
            return Ok(result_types.into_iter().next().unwrap());
        }

        return Ok(Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter(result_types)),
            conditional.span,
        ));
    }

    // Resolve type references for comparison
    let resolved_check = resolve_type_reference(check_type, type_env);
    let resolved_extends = resolve_type_reference(extends_type, type_env);

    // Check assignability: does check_type extend extends_type?
    if TypeCompatibility::is_assignable(&resolved_check, &resolved_extends) {
        Ok((*conditional.true_type).clone())
    } else {
        Ok((*conditional.false_type).clone())
    }
}

/// Helper to resolve type references
fn resolve_type_reference<'arena>(
    typ: &Type<'arena>,
    type_env: &TypeEnvironment<'arena>,
) -> Type<'arena> {
    match &typ.kind {
        TypeKind::Reference(type_ref) => {
            let type_name = type_ref.name.node.to_string();
            match type_env.lookup_type(&type_name) {
                Some(t) => t.clone(),
                None => typ.clone(), // Can't resolve, use as-is
            }
        }
        _ => typ.clone(),
    }
}

/// Helper to check if two types are structurally equal (simplified)
fn types_structurally_equal<'arena>(t1: &Type<'arena>, t2: &Type<'arena>) -> bool {
    match (&t1.kind, &t2.kind) {
        (TypeKind::Primitive(p1), TypeKind::Primitive(p2)) => p1 == p2,
        (TypeKind::Literal(l1), TypeKind::Literal(l2)) => l1 == l2,
        (TypeKind::Reference(r1), TypeKind::Reference(r2)) => r1.name.node == r2.name.node,
        (TypeKind::Array(a1), TypeKind::Array(a2)) => types_structurally_equal(a1, a2),
        _ => false,
    }
}

/// Check if a type contains an infer keyword
fn contains_infer<'arena>(typ: &Type<'arena>) -> bool {
    match &typ.kind {
        TypeKind::Infer(_) => true,
        TypeKind::Array(elem) => contains_infer(elem),
        TypeKind::Union(types) | TypeKind::Intersection(types) | TypeKind::Tuple(types) => {
            types.iter().any(contains_infer)
        }
        TypeKind::Function(func) => {
            func.parameters
                .iter()
                .any(|p| p.type_annotation.as_ref().is_some_and(contains_infer))
                || contains_infer(func.return_type)
        }
        TypeKind::Reference(type_ref) => type_ref
            .type_arguments
            .as_ref()
            .is_some_and(|args| args.iter().any(contains_infer)),
        _ => false,
    }
}

/// Try to match a check_type against a pattern (extends_type) and extract inferred types
fn try_match_and_infer<'arena>(
    check_type: &Type<'arena>,
    pattern: &Type<'arena>,
    inferred: &mut FxHashMap<String, Type<'arena>>,
    type_env: &TypeEnvironment<'arena>,
) -> bool {
    match &pattern.kind {
        // If pattern is `infer R`, capture the check_type as R
        TypeKind::Infer(name) => {
            inferred.insert(name.node.to_string(), check_type.clone());
            true
        }

        // Array pattern: T[] matches against Array<U>
        TypeKind::Array(pattern_elem) => {
            if let TypeKind::Array(check_elem) = &check_type.kind {
                try_match_and_infer(check_elem, pattern_elem, inferred, type_env)
            } else {
                false
            }
        }

        // Type reference with type arguments: Foo<infer R>
        TypeKind::Reference(pattern_ref) => {
            // Resolve check_type if it's a reference
            let resolved_check = resolve_type_reference(check_type, type_env);

            if let TypeKind::Reference(check_ref) = &resolved_check.kind {
                // Names must match
                if pattern_ref.name.node != check_ref.name.node {
                    return false;
                }

                // Match type arguments
                match (&pattern_ref.type_arguments, &check_ref.type_arguments) {
                    (Some(pattern_args), Some(check_args)) => {
                        if pattern_args.len() != check_args.len() {
                            return false;
                        }
                        pattern_args
                            .iter()
                            .zip(check_args.iter())
                            .all(|(p, c)| try_match_and_infer(c, p, inferred, type_env))
                    }
                    (None, None) => true,
                    _ => false,
                }
            } else {
                false
            }
        }

        // Function type pattern
        TypeKind::Function(pattern_func) => {
            if let TypeKind::Function(check_func) = &check_type.kind {
                // Match parameters
                if pattern_func.parameters.len() != check_func.parameters.len() {
                    return false;
                }

                let params_match = pattern_func
                    .parameters
                    .iter()
                    .zip(check_func.parameters.iter())
                    .all(|(p_param, c_param)| {
                        match (&p_param.type_annotation, &c_param.type_annotation) {
                            (Some(p_type), Some(c_type)) => {
                                try_match_and_infer(c_type, p_type, inferred, type_env)
                            }
                            _ => true,
                        }
                    });

                params_match
                    && try_match_and_infer(
                        check_func.return_type,
                        pattern_func.return_type,
                        inferred,
                        type_env,
                    )
            } else {
                false
            }
        }

        // Tuple pattern
        TypeKind::Tuple(pattern_types) => {
            if let TypeKind::Tuple(check_types) = &check_type.kind {
                if pattern_types.len() != check_types.len() {
                    return false;
                }
                pattern_types
                    .iter()
                    .zip(check_types.iter())
                    .all(|(p, c)| try_match_and_infer(c, p, inferred, type_env))
            } else {
                false
            }
        }

        // For other patterns, just check type equality
        _ => {
            use crate::core::type_compat::TypeCompatibility;
            TypeCompatibility::is_assignable(check_type, pattern)
        }
    }
}

/// Substitute inferred type variables in a type
fn substitute_inferred_types<'arena>(
    arena: &'arena bumpalo::Bump,
    typ: &Type<'arena>,
    inferred: &FxHashMap<String, Type<'arena>>,
) -> Result<Type<'arena>, String> {
    match &typ.kind {
        // If it's a reference to an inferred type variable, substitute it
        TypeKind::Reference(type_ref) if type_ref.type_arguments.is_none() => {
            let type_name = type_ref.name.node.to_string();
            if let Some(inferred_type) = inferred.get(&type_name) {
                Ok(inferred_type.clone())
            } else {
                Ok(typ.clone())
            }
        }

        // Recursively substitute in compound types
        TypeKind::Array(elem) => {
            let substituted_elem = substitute_inferred_types(arena, elem, inferred)?;
            Ok(Type::new(
                TypeKind::Array(arena.alloc(substituted_elem)),
                typ.span,
            ))
        }

        TypeKind::Union(types) => {
            let substituted: Result<Vec<_>, _> = types
                .iter()
                .map(|t| substitute_inferred_types(arena, t, inferred))
                .collect();
            Ok(Type::new(
                TypeKind::Union(arena.alloc_slice_fill_iter(substituted?)),
                typ.span,
            ))
        }

        TypeKind::Intersection(types) => {
            let substituted: Result<Vec<_>, _> = types
                .iter()
                .map(|t| substitute_inferred_types(arena, t, inferred))
                .collect();
            Ok(Type::new(
                TypeKind::Intersection(arena.alloc_slice_fill_iter(substituted?)),
                typ.span,
            ))
        }

        TypeKind::Tuple(types) => {
            let substituted: Result<Vec<_>, _> = types
                .iter()
                .map(|t| substitute_inferred_types(arena, t, inferred))
                .collect();
            Ok(Type::new(
                TypeKind::Tuple(arena.alloc_slice_fill_iter(substituted?)),
                typ.span,
            ))
        }

        // For other types, return as-is
        _ => Ok(typ.clone()),
    }
}

/// Extract keys from a type for mapped type iteration
/// Currently supports: string literal unions and type references to them
fn extract_keys_from_type<'arena>(
    typ: &Type<'arena>,
    type_env: &TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<Vec<String>, String> {
    match &typ.kind {
        TypeKind::Literal(Literal::String(s)) => Ok(vec![s.clone()]),
        TypeKind::Union(types) => {
            let mut keys = Vec::new();
            for t in types.iter() {
                match &t.kind {
                    TypeKind::Literal(Literal::String(s)) => {
                        keys.push(s.clone());
                    }
                    TypeKind::Reference(type_ref) => {
                        let type_name = interner.resolve(type_ref.name.node).to_string();
                        match type_env.lookup_type(&type_name) {
                            Some(resolved_type) => {
                                let resolved_keys =
                                    extract_keys_from_type(resolved_type, type_env, interner)?;
                                keys.extend(resolved_keys);
                            }
                            None => {
                                return Err(format!(
                                    "Type '{}' not found in type environment",
                                    type_name
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(
                            "Mapped type currently only supports string literal unions".to_string()
                        );
                    }
                }
            }
            Ok(keys)
        }
        // Type reference - resolve it using the type environment
        TypeKind::Reference(type_ref) => {
            let type_name = interner.resolve(type_ref.name.node).to_string();
            match type_env.lookup_type(&type_name) {
                Some(resolved_type) => extract_keys_from_type(resolved_type, type_env, interner),
                None => Err(format!(
                    "Type '{}' not found in type environment",
                    type_name
                )),
            }
        }
        // Future: support keyof T
        _ => Err(
            "Mapped type 'in' clause must be a string literal or union of string literals"
                .to_string(),
        ),
    }
}

// Helper functions

/// Extract string literal keys from a type (for Pick/Omit)
fn extract_string_literal_keys<'arena>(typ: &Type<'arena>) -> Result<Vec<String>, String> {
    match &typ.kind {
        TypeKind::Literal(Literal::String(s)) => Ok(vec![s.clone()]),
        TypeKind::Union(types) => types
            .iter()
            .map(|t| match &t.kind {
                TypeKind::Literal(Literal::String(s)) => Ok(s.clone()),
                _ => Err(
                    "Pick/Omit key type must be string literal or union of string literals"
                        .to_string(),
                ),
            })
            .collect(),
        _ => {
            Err("Pick/Omit key type must be string literal or union of string literals".to_string())
        }
    }
}

/// Check if a type is nil or void
fn is_nil_or_void<'arena>(typ: &Type<'arena>) -> bool {
    matches!(
        typ.kind,
        TypeKind::Primitive(PrimitiveType::Nil) | TypeKind::Primitive(PrimitiveType::Void)
    )
}

/// Simple type assignability check
fn is_assignable_to<'arena>(source: &Type<'arena>, target: &Type<'arena>) -> bool {
    use crate::core::type_compat::TypeCompatibility;
    TypeCompatibility::is_assignable(source, target)
}

/// Evaluate a template literal type to a union of string literals
/// For example: `Hello ${T}` where T = "World" | "Rust" becomes "Hello World" | "Hello Rust"
pub fn evaluate_template_literal_type<'arena>(
    arena: &'arena bumpalo::Bump,
    template: &typedlua_parser::ast::types::TemplateLiteralType<'arena>,
    type_env: &TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<Type<'arena>, String> {
    use typedlua_parser::ast::types::TemplateLiteralTypePart;

    // Extract all interpolated types and get their possible values
    let mut part_expansions: Vec<Vec<String>> = Vec::new();

    for part in template.parts.iter() {
        match part {
            TemplateLiteralTypePart::String(s) => {
                // Static string - single value
                part_expansions.push(vec![s.clone()]);
            }
            TemplateLiteralTypePart::Type(ty) => {
                // Type interpolation - expand to all possible string values
                let values = expand_type_to_strings(ty, type_env, interner)?;
                if values.is_empty() {
                    return Err(
                        "Template literal type interpolation produced no values".to_string()
                    );
                }
                part_expansions.push(values);
            }
        }
    }

    // Generate all combinations
    let combinations = cartesian_product(&part_expansions);

    // Limit the number of combinations to prevent exponential explosion
    // TypeScript uses 100,000 as the limit
    const MAX_TEMPLATE_LITERAL_COMBINATIONS: usize = 10000;

    if combinations.len() > MAX_TEMPLATE_LITERAL_COMBINATIONS {
        return Err(format!(
            "Template literal type expansion resulted in {} combinations, which exceeds the limit of {}. \
             Consider using a broader type like 'string' instead.",
            combinations.len(),
            MAX_TEMPLATE_LITERAL_COMBINATIONS
        ));
    }

    // If there's only one combination, return a single string literal
    // Otherwise, return a union of string literals
    if combinations.len() == 1 {
        Ok(Type::new(
            TypeKind::Literal(Literal::String(combinations[0].clone())),
            template.span,
        ))
    } else {
        let literal_types: Vec<Type<'arena>> = combinations
            .into_iter()
            .map(|s| Type::new(TypeKind::Literal(Literal::String(s)), template.span))
            .collect();

        Ok(Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter(literal_types)),
            template.span,
        ))
    }
}

/// Expand a type to all possible string literal values
fn expand_type_to_strings<'arena>(
    ty: &Type<'arena>,
    type_env: &TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<Vec<String>, String> {
    // First resolve any type references
    let resolved = match &ty.kind {
        TypeKind::Reference(type_ref) => {
            let type_name = interner.resolve(type_ref.name.node).to_string();
            if let Some(resolved) = type_env.lookup_type(&type_name) {
                resolved
            } else {
                ty
            }
        }
        _ => ty,
    };

    match &resolved.kind {
        TypeKind::Literal(Literal::String(s)) => Ok(vec![s.clone()]),
        TypeKind::Literal(Literal::Number(n)) => Ok(vec![n.to_string()]),
        TypeKind::Literal(Literal::Boolean(b)) => Ok(vec![b.to_string()]),
        TypeKind::Literal(Literal::Nil) => Ok(vec!["nil".to_string()]),
        TypeKind::Primitive(PrimitiveType::String) => {
            Err("Cannot interpolate primitive string type in template literal - use string literal union instead".to_string())
        }
        TypeKind::Primitive(PrimitiveType::Number) => {
            Err("Cannot interpolate primitive number type in template literal - use number literal union instead".to_string())
        }
        TypeKind::Union(types) => types
            .iter()
            .map(|t| expand_type_to_strings(t, type_env, interner))
            .collect::<Result<Vec<_>, _>>()
            .map(|v| v.into_iter().flatten().collect()),
        _ => Err(format!(
            "Cannot interpolate type {:?} in template literal - only string/number/boolean literals and unions are supported",
            resolved.kind
        )),
    }
}

/// Generate cartesian product of string vectors
/// For example: [["a", "b"], ["1", "2"]] -> ["a1", "a2", "b1", "b2"]
fn cartesian_product(vecs: &[Vec<String>]) -> Vec<String> {
    if vecs.is_empty() {
        return vec![String::new()];
    }

    if vecs.len() == 1 {
        return vecs[0].clone();
    }

    vecs.iter().fold(vec![String::new()], |acc, v| {
        acc.iter()
            .flat_map(|existing| {
                v.iter().map(move |item| {
                    let mut new_item = existing.clone();
                    new_item.push_str(item);
                    new_item
                })
            })
            .collect()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;
    use typedlua_parser::ast::Ident;

    fn make_span() -> Span {
        Span::new(0, 0, 0, 0)
    }

    fn make_object_type<'arena>(
        arena: &'arena Bump,
        properties: Vec<(&str, Type<'arena>, bool, bool)>,
    ) -> Type<'arena> {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        make_object_type_with_interner(arena, &interner, properties)
    }

    fn make_object_type_with_interner<'arena>(
        arena: &'arena Bump,
        interner: &typedlua_parser::string_interner::StringInterner,
        properties: Vec<(&str, Type<'arena>, bool, bool)>,
    ) -> Type<'arena> {
        let members: Vec<_> = properties
            .into_iter()
            .map(|(name, typ, optional, readonly)| {
                let name_id = interner.intern(name);
                ObjectTypeMember::Property(PropertySignature {
                    is_readonly: readonly,
                    name: Ident::new(name_id, make_span()),
                    is_optional: optional,
                    type_annotation: typ,
                    span: make_span(),
                })
            })
            .collect();

        Type::new(
            TypeKind::Object(ObjectType {
                members: arena.alloc_slice_fill_iter(members),
                span: make_span(),
            }),
            make_span(),
        )
    }

    #[test]
    fn test_partial() {
        let arena = Bump::new();
        let obj = make_object_type(
            &arena,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
            ],
        );

        let result = partial(&arena, &[obj], make_span()).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 2);
            for member in obj_type.members.iter() {
                if let ObjectTypeMember::Property(prop) = member {
                    assert!(
                        prop.is_optional,
                        "Property {} should be optional",
                        prop.name.node
                    );
                }
            }
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_required() {
        let arena = Bump::new();
        let obj = make_object_type(
            &arena,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    true,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    true,
                    false,
                ),
            ],
        );

        let result = required(&arena, &[obj], make_span()).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 2);
            for member in obj_type.members.iter() {
                if let ObjectTypeMember::Property(prop) = member {
                    assert!(
                        !prop.is_optional,
                        "Property {} should be required",
                        prop.name.node
                    );
                }
            }
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_readonly() {
        let arena = Bump::new();
        let obj = make_object_type(
            &arena,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
            ],
        );

        let result = readonly(&arena, &[obj], make_span()).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 2);
            for member in obj_type.members.iter() {
                if let ObjectTypeMember::Property(prop) = member {
                    assert!(
                        prop.is_readonly,
                        "Property {} should be readonly",
                        prop.name.node
                    );
                }
            }
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_record() {
        let arena = Bump::new();
        let key_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let value_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = record(
            &arena,
            &[key_type, value_type],
            make_span(),
            &interner,
            &common_ids,
        )
        .unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
            assert!(matches!(obj_type.members[0], ObjectTypeMember::Index(_)));
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_exclude() {
        let arena = Bump::new();
        let union = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span()),
            ])),
            make_span(),
        );
        let exclude = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = self::exclude(&arena, &[union, exclude], make_span()).unwrap();

        if let TypeKind::Union(types) = &result.kind {
            assert_eq!(types.len(), 2);
            assert!(types
                .iter()
                .all(|t| !matches!(t.kind, TypeKind::Primitive(PrimitiveType::String))));
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_non_nilable() {
        let arena = Bump::new();
        let union = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
            ])),
            make_span(),
        );

        let result = non_nilable(&arena, &[union], make_span()).unwrap();

        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_nilable() {
        let arena = Bump::new();
        let typ = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let result = nilable(&arena, &[typ], make_span()).unwrap();

        if let TypeKind::Union(types) = &result.kind {
            assert_eq!(types.len(), 2);
            assert!(types
                .iter()
                .any(|t| matches!(t.kind, TypeKind::Primitive(PrimitiveType::String))));
            assert!(types
                .iter()
                .any(|t| matches!(t.kind, TypeKind::Primitive(PrimitiveType::Nil))));
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_return_type() {
        use typedlua_parser::ast::types::FunctionType;

        let arena = Bump::new();
        let func = Type::new(
            TypeKind::Function(FunctionType {
                type_parameters: None,
                parameters: &[],
                return_type: &*arena.alloc(Type::new(
                    TypeKind::Primitive(PrimitiveType::Number),
                    make_span(),
                )),
                throws: None,
                span: make_span(),
            }),
            make_span(),
        );

        let result = return_type(&[func], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_pick() {
        let arena = Bump::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let obj = make_object_type_with_interner(
            &arena,
            &interner,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
                (
                    "email",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
            ],
        );

        // Pick<Obj, "name" | "age">
        let keys = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Literal(Literal::String("name".to_string())),
                    make_span(),
                ),
                Type::new(
                    TypeKind::Literal(Literal::String("age".to_string())),
                    make_span(),
                ),
            ])),
            make_span(),
        );

        let result = pick(&arena, &[obj, keys], make_span(), &interner).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 2);
            // Should have name and age, but not email
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_pick_single_key() {
        let arena = Bump::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let obj = make_object_type_with_interner(
            &arena,
            &interner,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
            ],
        );

        // Pick<Obj, "name">
        let keys = Type::new(
            TypeKind::Literal(Literal::String("name".to_string())),
            make_span(),
        );

        let result = pick(&arena, &[obj, keys], make_span(), &interner).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_omit() {
        let arena = Bump::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let obj = make_object_type_with_interner(
            &arena,
            &interner,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
                (
                    "email",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
            ],
        );

        // Omit<Obj, "email">
        let keys = Type::new(
            TypeKind::Literal(Literal::String("email".to_string())),
            make_span(),
        );

        let result = omit(&arena, &[obj, keys], make_span(), &interner).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 2);
            // Should have name and age, but not email
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_omit_multiple_keys() {
        let arena = Bump::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let obj = make_object_type_with_interner(
            &arena,
            &interner,
            vec![
                (
                    "name",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
                (
                    "age",
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    false,
                    false,
                ),
                (
                    "email",
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    false,
                    false,
                ),
            ],
        );

        // Omit<Obj, "name" | "age">
        let keys = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Literal(Literal::String("name".to_string())),
                    make_span(),
                ),
                Type::new(
                    TypeKind::Literal(Literal::String("age".to_string())),
                    make_span(),
                ),
            ])),
            make_span(),
        );

        let result = omit(&arena, &[obj, keys], make_span(), &interner).unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
            // Should only have email
        } else {
            panic!("Expected object type");
        }
    }

    // ========================================================================
    // Additional Comprehensive Tests
    // ========================================================================

    #[test]
    fn test_extract() {
        let arena = Bump::new();
        let union = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span()),
            ])),
            make_span(),
        );
        let extract_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = extract(&arena, &[union, extract_type], make_span()).unwrap();

        // Should extract just string
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_extract_multiple() {
        let arena = Bump::new();
        let union = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span()),
            ])),
            make_span(),
        );

        // Extract string | number
        let extract_type = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
            ])),
            make_span(),
        );

        let result = extract(&arena, &[union, extract_type], make_span()).unwrap();

        if let TypeKind::Union(types) = &result.kind {
            assert_eq!(types.len(), 2);
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_parameters() {
        use typedlua_parser::ast::pattern::Pattern;
        use typedlua_parser::ast::statement::Parameter;
        use typedlua_parser::ast::types::FunctionType;

        let arena = Bump::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let x_id = interner.intern("x");
        let y_id = interner.intern("y");

        let func = Type::new(
            TypeKind::Function(FunctionType {
                type_parameters: None,
                parameters: arena.alloc_slice_fill_iter([
                    Parameter {
                        pattern: Pattern::Identifier(Ident::new(x_id, make_span())),
                        type_annotation: Some(Type::new(
                            TypeKind::Primitive(PrimitiveType::String),
                            make_span(),
                        )),
                        default: None,
                        is_rest: false,
                        is_optional: false,
                        span: make_span(),
                    },
                    Parameter {
                        pattern: Pattern::Identifier(Ident::new(y_id, make_span())),
                        type_annotation: Some(Type::new(
                            TypeKind::Primitive(PrimitiveType::Number),
                            make_span(),
                        )),
                        default: None,
                        is_rest: false,
                        is_optional: false,
                        span: make_span(),
                    },
                ]),
                return_type: &*arena.alloc(Type::new(
                    TypeKind::Primitive(PrimitiveType::Void),
                    make_span(),
                )),
                throws: None,
                span: make_span(),
            }),
            make_span(),
        );

        let result = parameters(&arena, &[func], make_span()).unwrap();

        if let TypeKind::Tuple(types) = &result.kind {
            assert_eq!(types.len(), 2);
            assert!(matches!(
                types[0].kind,
                TypeKind::Primitive(PrimitiveType::String)
            ));
            assert!(matches!(
                types[1].kind,
                TypeKind::Primitive(PrimitiveType::Number)
            ));
        } else {
            panic!("Expected tuple type");
        }
    }

    #[test]
    fn test_apply_utility_type_partial() {
        let arena = Bump::new();
        let obj = make_object_type(
            &arena,
            vec![(
                "name",
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                false,
                false,
            )],
        );

        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = apply_utility_type(
            &arena,
            "Partial",
            &[obj],
            make_span(),
            &interner,
            &common_ids,
        )
        .unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
            if let ObjectTypeMember::Property(prop) = &obj_type.members[0] {
                assert!(prop.is_optional);
            }
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_apply_utility_type_unknown() {
        let arena = Bump::new();
        let obj = make_object_type(&arena, vec![]);
        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = apply_utility_type(
            &arena,
            "UnknownType",
            &[obj],
            make_span(),
            &interner,
            &common_ids,
        );

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown utility type"));
    }

    #[test]
    fn test_partial_wrong_arg_count() {
        let arena = Bump::new();
        let obj = make_object_type(&arena, vec![]);
        let result = partial(&arena, &[], make_span());
        assert!(result.is_err());

        let result = partial(&arena, &[obj.clone(), obj], make_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_partial_non_object() {
        let arena = Bump::new();
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let result = partial(&arena, &[string_type], make_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_required_wrong_arg_count() {
        let arena = Bump::new();
        let _obj = make_object_type(&arena, vec![]);
        let result = required(&arena, &[], make_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_readonly_array() {
        let arena = Bump::new();
        let array_type = Type::new(
            TypeKind::Array(&*arena.alloc(Type::new(
                TypeKind::Primitive(PrimitiveType::String),
                make_span(),
            ))),
            make_span(),
        );

        let result = readonly(&arena, std::slice::from_ref(&array_type), make_span()).unwrap();
        // Arrays are returned as-is for now
        assert!(matches!(result.kind, TypeKind::Array(_)));
    }

    #[test]
    fn test_record_number_keys() {
        let arena = Bump::new();
        let key_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        let value_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = record(
            &arena,
            &[key_type, value_type],
            make_span(),
            &interner,
            &common_ids,
        )
        .unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
            if let ObjectTypeMember::Index(idx) = &obj_type.members[0] {
                assert!(matches!(idx.key_type, IndexKeyType::Number));
            }
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_record_union_string_literals() {
        let arena = Bump::new();
        // Record<"a" | "b", number>
        let key_type = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Literal(Literal::String("a".to_string())),
                    make_span(),
                ),
                Type::new(
                    TypeKind::Literal(Literal::String("b".to_string())),
                    make_span(),
                ),
            ])),
            make_span(),
        );
        let value_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = record(
            &arena,
            &[key_type, value_type],
            make_span(),
            &interner,
            &common_ids,
        )
        .unwrap();

        if let TypeKind::Object(obj_type) = &result.kind {
            assert_eq!(obj_type.members.len(), 1);
            assert!(matches!(obj_type.members[0], ObjectTypeMember::Index(_)));
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_record_invalid_key_type() {
        let arena = Bump::new();
        let key_type = Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span());
        let value_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let (interner, common_ids) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
        let result = record(
            &arena,
            &[key_type, value_type],
            make_span(),
            &interner,
            &common_ids,
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_exclude_non_union() {
        let arena = Bump::new();
        // Exclude<string, number> should return string (since string is not assignable to number)
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let result = exclude(&arena, &[string_type.clone(), number_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_exclude_all_types() {
        let arena = Bump::new();
        // Exclude<string, string> should return never
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = exclude(&arena, &[string_type.clone(), string_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_extract_non_union_match() {
        let arena = Bump::new();
        // Extract<string, string> should return string
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = extract(&arena, &[string_type.clone(), string_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_extract_non_union_no_match() {
        let arena = Bump::new();
        // Extract<string, number> should return never
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let result = extract(&arena, &[string_type, number_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_non_nilable_nullable_type() {
        let arena = Bump::new();
        let nullable = Type::new(
            TypeKind::Nullable(&*arena.alloc(Type::new(
                TypeKind::Primitive(PrimitiveType::String),
                make_span(),
            ))),
            make_span(),
        );

        let result = non_nilable(&arena, &[nullable], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_non_nilable_non_union() {
        let arena = Bump::new();
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = non_nilable(&arena, &[string_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_non_nilable_only_nil() {
        let arena = Bump::new();
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());

        let result = non_nilable(&arena, &[nil_type], make_span()).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_nilable_already_nilable() {
        let arena = Bump::new();
        let union = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
            ])),
            make_span(),
        );

        let result = nilable(&arena, std::slice::from_ref(&union), make_span()).unwrap();
        // Should return the same type since it already has nil
        if let TypeKind::Union(types) = &result.kind {
            assert_eq!(types.len(), 2);
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_nilable_nullable() {
        let arena = Bump::new();
        let nullable = Type::new(
            TypeKind::Nullable(&*arena.alloc(Type::new(
                TypeKind::Primitive(PrimitiveType::String),
                make_span(),
            ))),
            make_span(),
        );

        let result = nilable(&arena, std::slice::from_ref(&nullable), make_span()).unwrap();
        // Should return the same nullable type
        assert!(matches!(result.kind, TypeKind::Nullable(_)));
    }

    #[test]
    fn test_return_type_non_function() {
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = return_type(&[string_type], make_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_parameters_non_function() {
        let arena = Bump::new();
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        let result = parameters(&arena, &[string_type], make_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_is_nil_or_void() {
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());
        let void_type = Type::new(TypeKind::Primitive(PrimitiveType::Void), make_span());
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        assert!(is_nil_or_void(&nil_type));
        assert!(is_nil_or_void(&void_type));
        assert!(!is_nil_or_void(&string_type));
    }

    #[test]
    fn test_extract_string_literal_keys() {
        let arena = Bump::new();
        let single_key = Type::new(
            TypeKind::Literal(Literal::String("name".to_string())),
            make_span(),
        );
        let keys = extract_string_literal_keys(&single_key).unwrap();
        assert_eq!(keys, vec!["name"]);

        let union_keys = Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter([
                Type::new(
                    TypeKind::Literal(Literal::String("a".to_string())),
                    make_span(),
                ),
                Type::new(
                    TypeKind::Literal(Literal::String("b".to_string())),
                    make_span(),
                ),
            ])),
            make_span(),
        );
        let keys = extract_string_literal_keys(&union_keys).unwrap();
        assert_eq!(keys.len(), 2);
    }

    #[test]
    fn test_extract_string_literal_keys_invalid() {
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        let result = extract_string_literal_keys(&number_type);
        assert!(result.is_err());
    }

    #[test]
    fn test_cartesian_product() {
        let vecs = vec![
            vec!["a".to_string(), "b".to_string()],
            vec!["1".to_string(), "2".to_string()],
        ];

        let result = cartesian_product(&vecs);
        assert_eq!(result.len(), 4);
        assert!(result.contains(&"a1".to_string()));
        assert!(result.contains(&"a2".to_string()));
        assert!(result.contains(&"b1".to_string()));
        assert!(result.contains(&"b2".to_string()));
    }

    #[test]
    fn test_cartesian_product_empty() {
        let vecs: Vec<Vec<String>> = vec![];
        let result = cartesian_product(&vecs);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], "");
    }

    #[test]
    fn test_cartesian_product_single() {
        let vecs = vec![vec!["a".to_string(), "b".to_string()]];
        let result = cartesian_product(&vecs);
        assert_eq!(result.len(), 2);
        assert!(result.contains(&"a".to_string()));
        assert!(result.contains(&"b".to_string()));
    }
}
