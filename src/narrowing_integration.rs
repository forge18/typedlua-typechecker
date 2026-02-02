/// Integration module for type narrowing with the type checker
/// This provides the scaffolding for how narrowing will be used during type checking
use super::narrowing::{narrow_type_from_condition, NarrowingContext};
use rustc_hash::FxHashMap;
use typedlua_parser::ast::expression::Expression;
use typedlua_parser::ast::types::Type;
use typedlua_parser::string_interner::{StringId, StringInterner};

/// Demonstration of how type narrowing integrates with if statement checking
///
/// This is a template/example showing how the type checker would use narrowing
/// when checking if statements. Full integration requires statement type checking
/// which is not yet implemented.
pub struct IfStatementNarrowingExample;

impl IfStatementNarrowingExample {
    /// Example: How to narrow types when type checking an if statement
    ///
    /// ```text
    /// // Given code:
    /// local x: string | nil = getValue()
    /// if x != nil then
    ///     -- In this branch, x is narrowed to string
    ///     print(x.upper(x))  // Valid: x is string here
    /// else
    ///     -- In this branch, x is nil
    ///     print("x is nil")
    /// end
    /// ```
    #[allow(dead_code)]
    pub fn check_if_statement_with_narrowing(
        condition: &Expression,
        base_context: &NarrowingContext,
        variable_types: &FxHashMap<StringId, Type>,
        interner: &StringInterner,
    ) -> (NarrowingContext, NarrowingContext) {
        // Step 1: Analyze the condition to produce narrowed contexts
        let (then_context, else_context) =
            narrow_type_from_condition(condition, base_context, variable_types, interner);

        (then_context, else_context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typedlua_parser::ast::expression::{BinaryOp, ExpressionKind, Literal};
    use typedlua_parser::ast::types::{PrimitiveType, TypeKind};
    use typedlua_parser::ast::Spanned;
    use typedlua_parser::span::Span;
    use typedlua_parser::string_interner::StringId;

    fn make_span() -> Span {
        Span::new(0, 0, 0, 0)
    }

    fn get_string_id(s: &str, interner: &StringInterner) -> StringId {
        interner.intern(s)
    }

    #[test]
    fn test_if_statement_narrowing_example() {
        let (interner, _) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

        // Setup: x: string | nil
        let mut variable_types = FxHashMap::default();
        let x_id = get_string_id("x", &interner);
        variable_types.insert(
            x_id,
            Type::new(
                TypeKind::Union(vec![
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
                ]),
                make_span(),
            ),
        );

        // Condition: x != nil
        let condition = Expression::new(
            ExpressionKind::Binary(
                BinaryOp::NotEqual,
                Box::new(Expression::new(
                    ExpressionKind::Identifier(x_id),
                    make_span(),
                )),
                Box::new(Expression::new(
                    ExpressionKind::Literal(Literal::Nil),
                    make_span(),
                )),
            ),
            make_span(),
        );

        let base_context = NarrowingContext::new();

        // Apply narrowing
        let (then_ctx, else_ctx) = IfStatementNarrowingExample::check_if_statement_with_narrowing(
            &condition,
            &base_context,
            &variable_types,
            &interner,
        );

        // In then branch: x should be narrowed to string
        let then_type = then_ctx.get_narrowed_type(x_id).unwrap();
        assert!(matches!(
            then_type.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // In else branch: x should be nil
        let else_type = else_ctx
            .get_narrowed_type(x_id)
            .unwrap_or_else(|| variable_types.get(&x_id).unwrap());
        assert!(matches!(
            else_type.kind,
            TypeKind::Primitive(PrimitiveType::Nil)
        ));
    }

    #[test]
    fn test_typeof_narrowing_example() {
        let (interner, _) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

        let mut variable_types = FxHashMap::default();
        let x_id = get_string_id("x", &interner);
        let typeof_id = get_string_id("typeof", &interner);
        variable_types.insert(
            x_id,
            Type::new(
                TypeKind::Union(vec![
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                ]),
                make_span(),
            ),
        );

        // Condition: typeof(x) == "string"
        let condition = Expression::new(
            ExpressionKind::Binary(
                BinaryOp::Equal,
                Box::new(Expression::new(
                    ExpressionKind::Call(
                        Box::new(Expression::new(
                            ExpressionKind::Identifier(typeof_id),
                            make_span(),
                        )),
                        vec![typedlua_parser::ast::expression::Argument {
                            value: Expression::new(ExpressionKind::Identifier(x_id), make_span()),
                            is_spread: false,
                            span: make_span(),
                        }],
                        None,
                    ),
                    make_span(),
                )),
                Box::new(Expression::new(
                    ExpressionKind::Literal(Literal::String("string".to_string())),
                    make_span(),
                )),
            ),
            make_span(),
        );

        let base_context = NarrowingContext::new();

        // Apply narrowing
        let (then_ctx, else_ctx) = IfStatementNarrowingExample::check_if_statement_with_narrowing(
            &condition,
            &base_context,
            &variable_types,
            &interner,
        );

        // In then branch: x should be string
        let then_type = then_ctx.get_narrowed_type(x_id).unwrap();
        assert!(matches!(
            then_type.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // In else branch: x should be number
        let else_type = else_ctx.get_narrowed_type(x_id).unwrap();
        assert!(matches!(
            else_type.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_type_guard_narrowing() {
        use typedlua_parser::ast::types::{FunctionType, TypePredicate};

        let (interner, _) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

        // Setup: x: string | number | nil
        let mut variable_types = FxHashMap::default();
        let x_id = get_string_id("x", &interner);
        let is_string_id = get_string_id("isString", &interner);

        // Register the variable type
        variable_types.insert(
            x_id,
            Type::new(
                TypeKind::Union(vec![
                    Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                    Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                    Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
                ]),
                make_span(),
            ),
        );

        // Register isString as a type guard function: (x: any) => x is string
        let type_predicate = TypePredicate {
            parameter_name: Spanned::new(x_id, make_span()),
            type_annotation: Box::new(Type::new(
                TypeKind::Primitive(PrimitiveType::String),
                make_span(),
            )),
            span: make_span(),
        };
        let func_type = FunctionType {
            type_parameters: None,
            parameters: vec![],
            return_type: Box::new(Type::new(
                TypeKind::TypePredicate(type_predicate),
                make_span(),
            )),
            throws: None,
            span: make_span(),
        };
        variable_types.insert(
            is_string_id,
            Type::new(TypeKind::Function(func_type), make_span()),
        );

        // Condition: isString(x)
        let condition = Expression::new(
            ExpressionKind::Call(
                Box::new(Expression::new(
                    ExpressionKind::Identifier(is_string_id),
                    make_span(),
                )),
                vec![typedlua_parser::ast::expression::Argument {
                    value: Expression::new(ExpressionKind::Identifier(x_id), make_span()),
                    is_spread: false,
                    span: make_span(),
                }],
                None,
            ),
            make_span(),
        );

        let base_context = NarrowingContext::new();

        // Apply narrowing
        let (then_ctx, else_ctx) = IfStatementNarrowingExample::check_if_statement_with_narrowing(
            &condition,
            &base_context,
            &variable_types,
            &interner,
        );

        // In then branch: x should be narrowed to string
        let then_type = then_ctx.get_narrowed_type(x_id).unwrap();
        assert!(matches!(
            then_type.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // In else branch: x should be number | nil
        let else_type = else_ctx.get_narrowed_type(x_id).unwrap();
        if let TypeKind::Union(types) = &else_type.kind {
            assert_eq!(types.len(), 2);
            assert!(types
                .iter()
                .any(|t| matches!(t.kind, TypeKind::Primitive(PrimitiveType::Number))));
            assert!(types
                .iter()
                .any(|t| matches!(t.kind, TypeKind::Primitive(PrimitiveType::Nil))));
        } else {
            panic!("Expected union type for else branch");
        }
    }

    #[test]
    fn test_instanceof_narrowing() {
        use typedlua_parser::ast::expression::ExpressionKind;
        use typedlua_parser::ast::types::TypeReference;

        let (interner, _) =
            typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

        let mut variable_types = FxHashMap::default();
        let pet_id = get_string_id("pet", &interner);
        let animal_id = get_string_id("Animal", &interner);
        let dog_id = get_string_id("Dog", &interner);
        variable_types.insert(
            pet_id,
            Type::new(
                TypeKind::Union(vec![
                    Type::new(
                        TypeKind::Reference(TypeReference {
                            name: Spanned::new(animal_id, make_span()),
                            type_arguments: None,
                            span: make_span(),
                        }),
                        make_span(),
                    ),
                    Type::new(
                        TypeKind::Reference(TypeReference {
                            name: Spanned::new(dog_id, make_span()),
                            type_arguments: None,
                            span: make_span(),
                        }),
                        make_span(),
                    ),
                ]),
                make_span(),
            ),
        );

        // Condition: pet instanceof Dog
        let condition = Expression::new(
            ExpressionKind::Binary(
                BinaryOp::Instanceof,
                Box::new(Expression::new(
                    ExpressionKind::Identifier(pet_id),
                    make_span(),
                )),
                Box::new(Expression::new(
                    ExpressionKind::Identifier(dog_id),
                    make_span(),
                )),
            ),
            make_span(),
        );

        let base_context = NarrowingContext::new();

        // Apply narrowing
        let (then_ctx, _else_ctx) = IfStatementNarrowingExample::check_if_statement_with_narrowing(
            &condition,
            &base_context,
            &variable_types,
            &interner,
        );

        // In then branch: pet should be narrowed to Dog
        let then_type = then_ctx.get_narrowed_type(pet_id).unwrap();
        if let TypeKind::Reference(type_ref) = &then_type.kind {
            assert_eq!(type_ref.name.node, dog_id);
        } else {
            panic!("Expected reference type for then branch");
        }
    }
}
