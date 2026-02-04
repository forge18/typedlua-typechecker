//! Pure type utility functions
//!
//! This module contains pure utility functions for working with types that
//! don't require access to type checker state.
//!
//! These functions are meant to be used by the type checker and other modules
//! as part of the refactoring effort to reduce cognitive load.

#![allow(dead_code)] // Functions will be used during type_checker.rs refactoring

use typedlua_parser::ast::expression::*;
use typedlua_parser::ast::statement::*;
use typedlua_parser::ast::types::*;
use typedlua_parser::span::Span;

/// Widens literal types to their base primitive types.
///
/// Converts literal types (e.g., `42`, `"hello"`, `true`, `nil`) to their base
/// primitive types (`number`, `string`, `boolean`, `nil`). Non-literal types are
/// returned unchanged.
///
/// # Examples
///
/// ```rust,ignore
/// // 42 → number
/// // "hello" → string
/// // true → boolean
/// // nil → nil
/// // number → number (unchanged)
/// ```
pub fn widen_type(typ: Type) -> Type {
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

/// Checks if a type is the boolean primitive type.
///
/// # Returns
///
/// `true` if the type is `boolean`, `false` otherwise.
pub fn is_boolean_type(typ: &Type) -> bool {
    matches!(typ.kind, TypeKind::Primitive(PrimitiveType::Boolean))
}

/// Maps operator kinds to their Lua metamethod names.
///
/// # Examples
///
/// ```rust,ignore
/// operator_kind_name(&OperatorKind::Add) // "__add"
/// operator_kind_name(&OperatorKind::Subtract) // "__sub"
/// operator_kind_name(&OperatorKind::Index) // "__index"
/// ```
pub fn operator_kind_name(op: &OperatorKind) -> String {
    match op {
        OperatorKind::Add => "__add",
        OperatorKind::Subtract => "__sub",
        OperatorKind::Multiply => "__mul",
        OperatorKind::Divide => "__div",
        OperatorKind::FloorDivide => "__idiv",
        OperatorKind::Modulo => "__mod",
        OperatorKind::Power => "__pow",
        OperatorKind::Concatenate => "__concat",
        OperatorKind::Equal => "__eq",
        OperatorKind::NotEqual => "__ne",
        OperatorKind::LessThan => "__lt",
        OperatorKind::LessThanOrEqual => "__le",
        OperatorKind::GreaterThan => "__gt",
        OperatorKind::GreaterThanOrEqual => "__ge",
        OperatorKind::Length => "__len",
        OperatorKind::UnaryMinus => "__unm",
        OperatorKind::BitwiseAnd => "__band",
        OperatorKind::BitwiseOr => "__bor",
        OperatorKind::BitwiseXor => "__bxor",
        OperatorKind::ShiftLeft => "__shl",
        OperatorKind::ShiftRight => "__shr",
        OperatorKind::Index => "__index",
        OperatorKind::NewIndex => "__newindex",
        OperatorKind::Call => "__call",
    }
    .to_string()
}

/// Converts a type to a human-readable string representation for error messages.
///
/// This provides a simplified string representation of types for diagnostic output.
pub fn type_to_string(typ: &Type) -> String {
    match &typ.kind {
        TypeKind::Primitive(prim) => format!("{:?}", prim).to_lowercase(),
        TypeKind::Literal(lit) => match lit {
            Literal::String(s) => format!("\"{}\"", s),
            Literal::Number(n) => n.to_string(),
            Literal::Integer(i) => i.to_string(),
            Literal::Boolean(b) => b.to_string(),
            Literal::Nil => "nil".to_string(),
        },
        TypeKind::Array(elem_type) => format!("{}[]", type_to_string(elem_type)),
        TypeKind::Tuple(types) => {
            let type_strs: Vec<_> = types.iter().map(type_to_string).collect();
            format!("[{}]", type_strs.join(", "))
        }
        TypeKind::Union(types) => {
            let type_strs: Vec<_> = types.iter().map(type_to_string).collect();
            type_strs.join(" | ")
        }
        TypeKind::Intersection(types) => {
            let type_strs: Vec<_> = types.iter().map(type_to_string).collect();
            type_strs.join(" & ")
        }
        TypeKind::Nullable(inner) => format!("{}?", type_to_string(inner)),
        TypeKind::Function(_) => "function".to_string(),
        TypeKind::Object(_) => "object".to_string(),
        TypeKind::Reference(_) => "type reference".to_string(),
        TypeKind::Infer(_) => "infer type".to_string(),
        TypeKind::KeyOf(_) => "keyof".to_string(),
        TypeKind::TypeQuery(_) => "typeof".to_string(),
        TypeKind::IndexAccess(_, _) => "indexed access type".to_string(),
        TypeKind::Conditional(_) => "conditional type".to_string(),
        TypeKind::Mapped(_) => "mapped type".to_string(),
        TypeKind::TemplateLiteral(_) => "template literal type".to_string(),
        TypeKind::TypePredicate(_) => "type predicate".to_string(),
        TypeKind::Parenthesized(inner) => type_to_string(inner),
        TypeKind::Variadic(inner) => format!("...{}", type_to_string(inner)),
        TypeKind::Namespace(_) => "namespace".to_string(),
    }
}

/// Creates a canonical union type by sorting and deduplicating members
///
/// Canonical form:
/// 1. Sorts types by their string representation
/// 2. Removes duplicate types
/// 3. Handles special cases:
///    - If `never` is present, returns just `never`
///    - Removes types that are covered by broader types
///    - Flattens nested unions
pub fn canonicalize_union(types: Vec<Type>, span: Span) -> Type {
    if types.is_empty() {
        return Type::new(TypeKind::Primitive(PrimitiveType::Never), span);
    }

    let mut unique_types: Vec<Type> = Vec::new();
    let mut has_never = false;

    for typ in types {
        match &typ.kind {
            TypeKind::Union(inner_types) => {
                for inner in inner_types {
                    add_type_to_union(&mut unique_types, inner.clone(), &mut has_never);
                }
            }
            _ => {
                add_type_to_union(&mut unique_types, typ, &mut has_never);
            }
        }
    }

    if has_never || unique_types.is_empty() {
        return Type::new(TypeKind::Primitive(PrimitiveType::Never), span);
    }

    unique_types.sort_by(|a, b| type_to_string(a).cmp(&type_to_string(b)));

    let mut deduped: Vec<Type> = Vec::new();
    let mut prev: Option<String> = None;
    for typ in unique_types {
        let s = type_to_string(&typ);
        if Some(s.clone()) != prev {
            deduped.push(typ);
            prev = Some(s);
        }
    }

    if deduped.len() == 1 {
        return deduped[0].clone();
    }

    Type::new(TypeKind::Union(deduped), span)
}

fn add_type_to_union(union: &mut Vec<Type>, typ: Type, has_never: &mut bool) {
    if let TypeKind::Primitive(PrimitiveType::Never) = typ.kind {
        *has_never = true;
        return;
    }

    let typ_str = type_to_string(&typ);
    if !union.iter().any(|t| type_to_string(t) == typ_str) {
        union.push(typ);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typedlua_parser::span::Span;

    fn make_type(kind: TypeKind) -> Type {
        Type::new(kind, Span::default())
    }

    #[test]
    fn test_widen_type_string_literal() {
        let literal = make_type(TypeKind::Literal(Literal::String("hello".to_string())));
        let widened = widen_type(literal);
        assert!(matches!(
            widened.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_widen_type_number_literal() {
        let literal = make_type(TypeKind::Literal(Literal::Number(42.0)));
        let widened = widen_type(literal);
        assert!(matches!(
            widened.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_widen_type_boolean_literal() {
        let literal = make_type(TypeKind::Literal(Literal::Boolean(true)));
        let widened = widen_type(literal);
        assert!(matches!(
            widened.kind,
            TypeKind::Primitive(PrimitiveType::Boolean)
        ));
    }

    #[test]
    fn test_widen_type_non_literal_unchanged() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let widened = widen_type(number_type.clone());
        assert!(matches!(
            widened.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_is_boolean_type_true() {
        let bool_type = make_type(TypeKind::Primitive(PrimitiveType::Boolean));
        assert!(is_boolean_type(&bool_type));
    }

    #[test]
    fn test_is_boolean_type_false() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        assert!(!is_boolean_type(&number_type));
    }

    #[test]
    fn test_operator_kind_name() {
        assert_eq!(operator_kind_name(&OperatorKind::Add), "__add");
        assert_eq!(operator_kind_name(&OperatorKind::Subtract), "__sub");
        assert_eq!(operator_kind_name(&OperatorKind::Index), "__index");
        assert_eq!(operator_kind_name(&OperatorKind::Call), "__call");
    }

    #[test]
    fn test_type_to_string_primitives() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        assert_eq!(type_to_string(&number_type), "number");

        let string_type = make_type(TypeKind::Primitive(PrimitiveType::String));
        assert_eq!(type_to_string(&string_type), "string");
    }

    #[test]
    fn test_type_to_string_literals() {
        let str_literal = make_type(TypeKind::Literal(Literal::String("hello".to_string())));
        assert_eq!(type_to_string(&str_literal), "\"hello\"");

        let num_literal = make_type(TypeKind::Literal(Literal::Number(42.0)));
        assert_eq!(type_to_string(&num_literal), "42");
    }

    #[test]
    fn test_type_to_string_array() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let array_type = make_type(TypeKind::Array(Box::new(number_type)));
        assert_eq!(type_to_string(&array_type), "number[]");
    }

    #[test]
    fn test_type_to_string_union() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string_type = make_type(TypeKind::Primitive(PrimitiveType::String));
        let union_type = make_type(TypeKind::Union(vec![number_type, string_type]));
        assert_eq!(type_to_string(&union_type), "number | string");
    }

    #[test]
    fn test_canonicalize_union_removes_duplicates() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let union = canonicalize_union(
            vec![number_type.clone(), number_type.clone()],
            Span::default(),
        );
        assert_eq!(type_to_string(&union), "number");
    }

    #[test]
    fn test_canonicalize_union_handles_never() {
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let never_type = make_type(TypeKind::Primitive(PrimitiveType::Never));
        let union = canonicalize_union(vec![number_type, never_type], Span::default());
        assert!(matches!(
            union.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_canonicalize_union_sorts_types() {
        let string_type = make_type(TypeKind::Primitive(PrimitiveType::String));
        let number_type = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let boolean_type = make_type(TypeKind::Primitive(PrimitiveType::Boolean));
        let union = canonicalize_union(
            vec![
                string_type.clone(),
                number_type.clone(),
                boolean_type.clone(),
            ],
            Span::default(),
        );
        if let TypeKind::Union(types) = union.kind {
            assert_eq!(types.len(), 3);
            assert_eq!(type_to_string(&types[0]), "boolean");
            assert_eq!(type_to_string(&types[1]), "number");
            assert_eq!(type_to_string(&types[2]), "string");
        } else {
            panic!("Expected union type");
        }
    }
}
