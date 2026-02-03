use std::collections::HashSet;
use typedlua_parser::ast::expression::Literal;
use typedlua_parser::ast::types::{
    FunctionType, ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind,
};

fn type_ptr(ty: &Type) -> usize {
    ty as *const Type as usize
}

/// Type compatibility checker
pub struct TypeCompatibility;

impl TypeCompatibility {
    /// Check if `source` is assignable to `target`
    pub fn is_assignable(source: &Type, target: &Type) -> bool {
        let mut visited: HashSet<(usize, usize)> = HashSet::new();
        Self::is_assignable_recursive(source, target, &mut visited)
    }

    fn is_assignable_recursive(
        source: &Type,
        target: &Type,
        visited: &mut HashSet<(usize, usize)>,
    ) -> bool {
        let source_ptr = type_ptr(source);
        let target_ptr = type_ptr(target);

        if visited.contains(&(source_ptr, target_ptr)) {
            return true;
        }
        visited.insert((source_ptr, target_ptr));

        // Unknown is assignable to/from anything
        if matches!(source.kind, TypeKind::Primitive(PrimitiveType::Unknown))
            || matches!(target.kind, TypeKind::Primitive(PrimitiveType::Unknown))
        {
            return true;
        }

        // Never is assignable to anything
        if matches!(source.kind, TypeKind::Primitive(PrimitiveType::Never)) {
            return true;
        }

        // Nothing is assignable to Never
        if matches!(target.kind, TypeKind::Primitive(PrimitiveType::Never)) {
            return false;
        }

        match (&source.kind, &target.kind) {
            // Primitive types
            (TypeKind::Primitive(s), TypeKind::Primitive(t)) => {
                Self::is_primitive_assignable(*s, *t)
            }

            // Literal types
            (TypeKind::Literal(s_lit), TypeKind::Literal(t_lit)) => s_lit == t_lit,

            // Literal to primitive
            (TypeKind::Literal(lit), TypeKind::Primitive(prim)) => {
                Self::is_literal_assignable_to_primitive(lit, *prim)
            }

            // Primitive to literal (reverse direction - primitive nil can satisfy literal nil)
            (TypeKind::Primitive(PrimitiveType::Nil), TypeKind::Literal(Literal::Nil)) => true,

            // Also handle the case where source is a union containing nil and target expects literal nil
            (TypeKind::Union(sources), TypeKind::Literal(Literal::Nil)) => {
                // Check if any source member is nil
                sources
                    .iter()
                    .any(|s| Self::is_assignable_recursive(s, target, visited))
            }

            // Union types
            (_, TypeKind::Union(targets)) => {
                // Source is assignable to union if assignable to any member
                targets
                    .iter()
                    .any(|t| Self::is_assignable_recursive(source, t, visited))
            }
            (TypeKind::Union(sources), _) => {
                // Union is assignable to target if all members are assignable
                sources
                    .iter()
                    .all(|s| Self::is_assignable_recursive(s, target, visited))
            }

            // Intersection types
            (TypeKind::Intersection(sources), _) => {
                // Intersection is assignable to target if any member is assignable
                sources
                    .iter()
                    .any(|s| Self::is_assignable_recursive(s, target, visited))
            }
            (_, TypeKind::Intersection(targets)) => {
                // Source is assignable to intersection if assignable to all members
                targets
                    .iter()
                    .all(|t| Self::is_assignable_recursive(source, t, visited))
            }

            // Array types
            (TypeKind::Array(s_elem), TypeKind::Array(t_elem)) => {
                Self::is_assignable_recursive(s_elem, t_elem, visited)
            }

            // Tuple types
            (TypeKind::Tuple(s_elems), TypeKind::Tuple(t_elems)) => {
                if s_elems.len() != t_elems.len() {
                    return false;
                }
                s_elems
                    .iter()
                    .zip(t_elems.iter())
                    .all(|(s, t)| Self::is_assignable_recursive(s, t, visited))
            }

            // Function types
            (TypeKind::Function(s_func), TypeKind::Function(t_func)) => {
                Self::is_function_assignable(s_func, t_func, visited)
            }

            // Object types
            (TypeKind::Object(s_obj), TypeKind::Object(t_obj)) => {
                Self::is_object_assignable(s_obj, t_obj, visited)
            }

            // Nullable types
            (TypeKind::Nullable(s_inner), TypeKind::Nullable(t_inner)) => {
                Self::is_assignable_recursive(s_inner, t_inner, visited)
            }
            (TypeKind::Primitive(PrimitiveType::Nil), TypeKind::Nullable(_)) => true,
            (_, TypeKind::Nullable(t_inner)) => {
                Self::is_assignable_recursive(source, t_inner, visited)
            }

            // Parenthesized types
            (TypeKind::Parenthesized(s_inner), _) => {
                Self::is_assignable_recursive(s_inner, target, visited)
            }
            (_, TypeKind::Parenthesized(t_inner)) => {
                Self::is_assignable_recursive(source, t_inner, visited)
            }

            // Type references
            // NOTE: Ideally we would resolve type aliases to their underlying types
            // and check structural compatibility. For now, we use name-based matching.
            // This means:
            //   type A = number; type B = number;
            //   A and B are NOT compatible (should be, but requires type resolution)
            //
            // Future enhancement: Pass TypeEnvironment to resolve_type_reference() and
            // recursively check is_assignable on the resolved types.
            (TypeKind::Reference(s_ref), TypeKind::Reference(t_ref)) => {
                // Check if names match exactly
                if s_ref.name.node == t_ref.name.node {
                    // Same type reference name - check type arguments if present
                    match (&s_ref.type_arguments, &t_ref.type_arguments) {
                        (None, None) => true,
                        (Some(s_args), Some(t_args)) if s_args.len() == t_args.len() => {
                            // Check all type arguments are compatible
                            s_args.iter().zip(t_args.iter()).all(|(s_arg, t_arg)| {
                                Self::is_assignable_recursive(s_arg, t_arg, visited)
                            })
                        }
                        _ => false,
                    }
                } else {
                    // Different names - could still be compatible if they resolve to
                    // the same underlying type, but we don't have type environment here
                    false
                }
            }

            // Type reference vs concrete type - would need type resolution
            (TypeKind::Reference(_), _) => {
                // We can't resolve the reference without a type environment
                // Conservative: assume incompatible
                false
            }
            (_, TypeKind::Reference(_)) => {
                // We can't resolve the reference without a type environment
                // Conservative: assume incompatible
                false
            }

            _ => false,
        }
    }

    /// Check if primitive types are compatible
    fn is_primitive_assignable(source: PrimitiveType, target: PrimitiveType) -> bool {
        if source == target {
            return true;
        }

        match (source, target) {
            // Integer is assignable to number
            (PrimitiveType::Integer, PrimitiveType::Number) => true,
            _ => false,
        }
    }

    /// Check if a literal is assignable to a primitive type
    fn is_literal_assignable_to_primitive(lit: &Literal, prim: PrimitiveType) -> bool {
        matches!(
            (lit, prim),
            (Literal::Number(_), PrimitiveType::Number)
                | (Literal::String(_), PrimitiveType::String)
                | (Literal::Boolean(_), PrimitiveType::Boolean)
                | (Literal::Nil, PrimitiveType::Nil)
        )
    }

    /// Check function type compatibility (contravariant parameters, covariant return)
    fn is_function_assignable(
        source: &FunctionType,
        target: &FunctionType,
        visited: &mut HashSet<(usize, usize)>,
    ) -> bool {
        // Check parameter count
        if source.parameters.len() != target.parameters.len() {
            return false;
        }

        // Parameters are contravariant: target params must be assignable to source params
        for (s_param, t_param) in source.parameters.iter().zip(target.parameters.iter()) {
            if let (Some(s_type), Some(t_type)) =
                (&s_param.type_annotation, &t_param.type_annotation)
            {
                if !Self::is_assignable_recursive(t_type, s_type, visited) {
                    return false;
                }
            }
        }

        // Return type is covariant: source return must be assignable to target return
        Self::is_assignable_recursive(&source.return_type, &target.return_type, visited)
    }

    /// Check object type structural compatibility
    fn is_object_assignable(
        source: &ObjectType,
        target: &ObjectType,
        visited: &mut HashSet<(usize, usize)>,
    ) -> bool {
        // For each property in target, source must have a compatible property
        for t_member in &target.members {
            match t_member {
                ObjectTypeMember::Property(t_prop) => {
                    // Find corresponding property in source
                    let found = source.members.iter().any(|s_member| {
                        if let ObjectTypeMember::Property(s_prop) = s_member {
                            s_prop.name.node == t_prop.name.node
                                && Self::is_assignable_recursive(
                                    &s_prop.type_annotation,
                                    &t_prop.type_annotation,
                                    visited,
                                )
                        } else {
                            false
                        }
                    });

                    if !found && !t_prop.is_optional {
                        return false;
                    }
                }
                ObjectTypeMember::Method(t_method) => {
                    // Find corresponding method in source
                    let found = source.members.iter().any(|s_member| {
                        if let ObjectTypeMember::Method(s_method) = s_member {
                            s_method.name.node == t_method.name.node
                        } else {
                            false
                        }
                    });

                    if !found {
                        return false;
                    }
                }
                ObjectTypeMember::Index(_) => {}
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typedlua_parser::span::Span;

    fn make_type(kind: TypeKind) -> Type {
        Type::new(kind, Span::new(0, 0, 0, 0))
    }

    #[test]
    fn test_primitive_assignability() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string = make_type(TypeKind::Primitive(PrimitiveType::String));
        let integer = make_type(TypeKind::Primitive(PrimitiveType::Integer));

        assert!(TypeCompatibility::is_assignable(&number, &number));
        assert!(!TypeCompatibility::is_assignable(&number, &string));
        assert!(TypeCompatibility::is_assignable(&integer, &number));
        assert!(!TypeCompatibility::is_assignable(&number, &integer));
    }

    #[test]
    fn test_literal_assignability() {
        let num_lit = make_type(TypeKind::Literal(Literal::Number(42.0)));
        let str_lit = make_type(TypeKind::Literal(Literal::String("hello".to_string())));
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string = make_type(TypeKind::Primitive(PrimitiveType::String));

        assert!(TypeCompatibility::is_assignable(&num_lit, &number));
        assert!(!TypeCompatibility::is_assignable(&num_lit, &string));
        assert!(TypeCompatibility::is_assignable(&str_lit, &string));
        assert!(!TypeCompatibility::is_assignable(&str_lit, &number));
    }

    #[test]
    fn test_union_assignability() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string = make_type(TypeKind::Primitive(PrimitiveType::String));
        let number_or_string = make_type(TypeKind::Union(vec![number.clone(), string.clone()]));

        // number is assignable to number | string
        assert!(TypeCompatibility::is_assignable(&number, &number_or_string));
        // string is assignable to number | string
        assert!(TypeCompatibility::is_assignable(&string, &number_or_string));
    }

    #[test]
    fn test_array_assignability() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string = make_type(TypeKind::Primitive(PrimitiveType::String));
        let number_array = make_type(TypeKind::Array(Box::new(number.clone())));
        let string_array = make_type(TypeKind::Array(Box::new(string.clone())));

        assert!(TypeCompatibility::is_assignable(
            &number_array,
            &number_array
        ));
        assert!(!TypeCompatibility::is_assignable(
            &number_array,
            &string_array
        ));
    }

    #[test]
    fn test_nullable_assignability() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let nullable_number = make_type(TypeKind::Nullable(Box::new(number.clone())));
        let nil = make_type(TypeKind::Primitive(PrimitiveType::Nil));

        // nil is assignable to number?
        assert!(TypeCompatibility::is_assignable(&nil, &nullable_number));
        // number is assignable to number?
        assert!(TypeCompatibility::is_assignable(&number, &nullable_number));
    }

    #[test]
    fn test_unknown_assignability() {
        let unknown = make_type(TypeKind::Primitive(PrimitiveType::Unknown));
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));

        // unknown is assignable to/from anything
        assert!(TypeCompatibility::is_assignable(&unknown, &number));
        assert!(TypeCompatibility::is_assignable(&number, &unknown));
    }

    #[test]
    fn test_parenthesized_type() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let parenthesized = make_type(TypeKind::Parenthesized(Box::new(number.clone())));

        // Parenthesized type should be same as inner type
        assert!(TypeCompatibility::is_assignable(&parenthesized, &number));
        assert!(TypeCompatibility::is_assignable(&number, &parenthesized));
    }

    #[test]
    fn test_literal_nil_to_nullable() {
        let nil_type = make_type(TypeKind::Primitive(PrimitiveType::Nil));
        let nullable_string = make_type(TypeKind::Nullable(Box::new(make_type(
            TypeKind::Primitive(PrimitiveType::String),
        ))));

        // nil is assignable to nullable string
        assert!(TypeCompatibility::is_assignable(
            &nil_type,
            &nullable_string
        ));
    }

    #[test]
    fn test_tuple_assignability() {
        let number = make_type(TypeKind::Primitive(PrimitiveType::Number));
        let string = make_type(TypeKind::Primitive(PrimitiveType::String));

        let tuple1 = make_type(TypeKind::Tuple(vec![number.clone(), string.clone()]));
        let tuple2 = make_type(TypeKind::Tuple(vec![number.clone(), string.clone()]));

        // Same tuples should be assignable
        assert!(TypeCompatibility::is_assignable(&tuple1, &tuple2));

        let tuple_diff = make_type(TypeKind::Tuple(vec![number.clone(), number.clone()]));
        assert!(!TypeCompatibility::is_assignable(&tuple_diff, &tuple1));
    }

    #[test]
    fn test_function_with_throws() {
        let func1 = make_type(TypeKind::Function(FunctionType {
            parameters: vec![],
            return_type: Box::new(make_type(TypeKind::Primitive(PrimitiveType::Number))),
            throws: None,
            span: Span::new(0, 0, 0, 0),
            type_parameters: None,
        }));
        let func2 = make_type(TypeKind::Function(FunctionType {
            parameters: vec![],
            return_type: Box::new(make_type(TypeKind::Primitive(PrimitiveType::Number))),
            throws: None,
            span: Span::new(0, 0, 0, 0),
            type_parameters: None,
        }));

        // Functions should be compatible
        assert!(TypeCompatibility::is_assignable(&func1, &func2));
    }
}
