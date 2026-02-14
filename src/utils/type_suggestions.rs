use crate::cli::diagnostics::DiagnosticSuggestion;
/// Type conversion suggestions for error messages
///
/// This module provides contextual suggestions for type mismatches, helping users
/// fix type errors with actionable recommendations.
use luanext_parser::ast::types::{PrimitiveType, Type, TypeKind};
use luanext_parser::span::Span;

/// Suggest type conversions for common type mismatches
///
/// Returns a list of suggestions that can be applied to fix the type mismatch.
///
/// # Arguments
/// * `actual` - The actual type that was provided
/// * `expected` - The expected type
/// * `expr_span` - The span of the expression causing the mismatch
///
/// # Examples
/// - `string` → `number`: Suggests `tonumber(value)`
/// - `number` → `string`: Suggests `tostring(value)`
/// - Non-optional → Optional: Suggests nil check
pub fn suggest_type_conversion(
    actual: &Type,
    expected: &Type,
    expr_span: Span,
) -> Vec<DiagnosticSuggestion> {
    let mut suggestions = Vec::new();

    // Handle primitive conversions
    if let (TypeKind::Primitive(actual_prim), TypeKind::Primitive(expected_prim)) =
        (&actual.kind, &expected.kind)
    {
        if let Some(suggestion) =
            suggest_primitive_conversion(*actual_prim, *expected_prim, expr_span)
        {
            suggestions.push(suggestion);
        }
    }

    // Handle union type narrowing
    if let TypeKind::Union(union_types) = &expected.kind {
        if is_contained_in_union(&actual.kind, union_types) {
            // Actual type is already in the union, suggest type guard
            suggestions.push(DiagnosticSuggestion {
                span: expr_span,
                replacement: "value".to_string(), // Placeholder - would need expression text
                message: "Consider using a type guard to narrow the type".to_string(),
            });
        }
    }

    // Handle optional types (T | nil)
    if is_optional_type(expected) && !is_optional_type(actual) {
        suggestions.push(DiagnosticSuggestion {
            span: expr_span,
            replacement: String::new(), // No direct replacement
            message: "Consider adding a nil check or making the source type optional".to_string(),
        });
    }

    suggestions
}

/// Suggest primitive type conversions
fn suggest_primitive_conversion(
    actual: PrimitiveType,
    expected: PrimitiveType,
    expr_span: Span,
) -> Option<DiagnosticSuggestion> {
    match (actual, expected) {
        (PrimitiveType::String, PrimitiveType::Number) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "tonumber(value)".to_string(),
            message: "Use tonumber() to convert string to number".to_string(),
        }),
        (PrimitiveType::String, PrimitiveType::Integer) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "tonumber(value)".to_string(),
            message: "Use tonumber() to convert string to integer".to_string(),
        }),
        (PrimitiveType::Number, PrimitiveType::String) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "tostring(value)".to_string(),
            message: "Use tostring() to convert number to string".to_string(),
        }),
        (PrimitiveType::Integer, PrimitiveType::String) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "tostring(value)".to_string(),
            message: "Use tostring() to convert integer to string".to_string(),
        }),
        (PrimitiveType::Number, PrimitiveType::Integer) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "math.floor(value)".to_string(),
            message: "Use math.floor() or math.ceil() to convert to integer".to_string(),
        }),
        (PrimitiveType::Integer, PrimitiveType::Number) => {
            // Integer is assignable to number, no suggestion needed
            None
        }
        (PrimitiveType::Boolean, PrimitiveType::String) => Some(DiagnosticSuggestion {
            span: expr_span,
            replacement: "tostring(value)".to_string(),
            message: "Use tostring() to convert boolean to string".to_string(),
        }),
        _ => None,
    }
}

/// Check if a type is contained in a union
fn is_contained_in_union(actual: &TypeKind, union_types: &[Type]) -> bool {
    union_types.iter().any(|t| types_match(actual, &t.kind))
}

/// Simple type matching (exact match only)
fn types_match(a: &TypeKind, b: &TypeKind) -> bool {
    match (a, b) {
        (TypeKind::Primitive(p1), TypeKind::Primitive(p2)) => p1 == p2,
        _ => false, // Simplified - full type equivalence would be more complex
    }
}

/// Check if a type is optional (T | nil)
fn is_optional_type(ty: &Type) -> bool {
    if let TypeKind::Union(types) = &ty.kind {
        types
            .iter()
            .any(|t| matches!(t.kind, TypeKind::Primitive(PrimitiveType::Nil)))
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use luanext_parser::span::Span;

    fn make_span() -> Span {
        Span::new(0, 10, 1, 1)
    }

    fn make_type(kind: TypeKind) -> Type {
        Type::new(kind, make_span())
    }

    #[test]
    fn test_string_to_number_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::String));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::Number));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].replacement.contains("tonumber"));
        assert!(suggestions[0].message.contains("convert string to number"));
    }

    #[test]
    fn test_number_to_string_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::String));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].replacement.contains("tostring"));
        assert!(suggestions[0].message.contains("convert number to string"));
    }

    #[test]
    fn test_integer_to_string_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::Integer));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::String));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].replacement.contains("tostring"));
    }

    #[test]
    fn test_number_to_integer_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::Integer));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].replacement.contains("math.floor"));
    }

    #[test]
    fn test_integer_to_number_no_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::Integer));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::Number));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        // Integer is assignable to number, so no conversion needed
        assert_eq!(suggestions.len(), 0);
    }

    #[test]
    fn test_optional_type_suggestion() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::String));

        // Create optional type: string | nil
        let union_types = vec![
            make_type(TypeKind::Primitive(PrimitiveType::String)),
            make_type(TypeKind::Primitive(PrimitiveType::Nil)),
        ];
        let leaked_types = Box::leak(union_types.into_boxed_slice());
        let expected = make_type(TypeKind::Union(leaked_types));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert!(suggestions.iter().any(|s| s.message.contains("nil check")));
    }

    #[test]
    fn test_is_optional_type() {
        // string | nil
        let union_types = vec![
            make_type(TypeKind::Primitive(PrimitiveType::String)),
            make_type(TypeKind::Primitive(PrimitiveType::Nil)),
        ];
        let leaked_types = Box::leak(union_types.into_boxed_slice());
        let optional = make_type(TypeKind::Union(leaked_types));
        assert!(is_optional_type(&optional));

        // Just string
        let non_optional = make_type(TypeKind::Primitive(PrimitiveType::String));
        assert!(!is_optional_type(&non_optional));
    }

    #[test]
    fn test_no_suggestion_for_same_type() {
        let actual = make_type(TypeKind::Primitive(PrimitiveType::String));
        let expected = make_type(TypeKind::Primitive(PrimitiveType::String));

        let suggestions = suggest_type_conversion(&actual, &expected, make_span());
        assert_eq!(suggestions.len(), 0);
    }
}
