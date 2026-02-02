#[cfg(test)]
mod tests {
    use super::super::super::super::symbol_table::SymbolTable;
    use super::super::super::super::type_environment::TypeEnvironment;
    use super::super::super::super::visitors::{
        AccessControl, TypeCheckVisitor, TypeInferenceVisitor, TypeInferrer,
    };
    use crate::diagnostics::{CollectingDiagnosticHandler, DiagnosticHandler};
    use std::sync::Arc;
    use typedlua_parser::ast::expression::*;
    use typedlua_parser::ast::types::*;
    use typedlua_parser::ast::Ident;
    use typedlua_parser::prelude::*;
    use typedlua_parser::span::Span;
    use typedlua_parser::string_interner::StringInterner;

    fn create_test_inferrer<'a>(
        symbol_table: &'a mut SymbolTable,
        type_env: &'a mut TypeEnvironment,
        narrowing_context: &'a mut super::super::super::super::narrowing::NarrowingContext,
        access_control: &'a AccessControl,
        interner: &'a StringInterner,
        diagnostic_handler: &'a Arc<dyn DiagnosticHandler>,
    ) -> TypeInferrer<'a> {
        TypeInferrer::new(
            symbol_table,
            type_env,
            narrowing_context,
            access_control,
            interner,
            diagnostic_handler,
        )
    }

    #[test]
    fn test_infer_literal_number() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();
        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Literal(Literal::Number(42.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Literal(Literal::Number(n)) if n == 42.0));
    }

    #[test]
    fn test_infer_literal_string() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Literal(Literal::String("hello".to_string())),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Literal(Literal::String(_))));
    }

    #[test]
    fn test_infer_literal_boolean() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Literal(Literal::Boolean(true))
        ));
    }

    #[test]
    fn test_infer_binary_op_add() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(1.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Add, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_concat() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::String("hello".to_string())),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::String(" world".to_string())),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Concatenate, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_infer_unary_op_negate() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let operand = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Unary(UnaryOp::Negate, operand),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_unary_op_not() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let operand = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Unary(UnaryOp::Not, operand),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Boolean)
        ));
    }

    #[test]
    fn test_infer_array() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let elements = vec![
            ArrayElement::Expression(Expression {
                kind: ExpressionKind::Literal(Literal::Number(1.0)),
                span: Span::default(),
                annotated_type: None,
                receiver_class: None,
            }),
            ArrayElement::Expression(Expression {
                kind: ExpressionKind::Literal(Literal::Number(2.0)),
                span: Span::default(),
                annotated_type: None,
                receiver_class: None,
            }),
        ];

        let mut expr = Expression {
            kind: ExpressionKind::Array(elements),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Array(_)));
    }

    #[test]
    fn test_infer_empty_array() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Array(vec![]),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Array(_)));
    }

    #[test]
    fn test_infer_conditional() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let cond = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let then_expr = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(1.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let else_expr = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Conditional(cond, then_expr, else_expr),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Conditional with different literal numbers returns a union
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_binary_op_comparison() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(1.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::LessThan, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Boolean)
        ));
    }

    #[test]
    fn test_visitor_name() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();
        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        assert_eq!(inferrer.name(), "TypeInferrer");
    }

    // ========================================================================
    // Additional Comprehensive Type Inference Tests
    // ========================================================================

    #[test]
    fn test_infer_literal_nil() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Literal(Literal::Nil),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Literal(Literal::Nil)));
    }

    #[test]
    fn test_infer_array_expression() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        // Array of numbers: [1, 2, 3]
        let mut expr = Expression {
            kind: ExpressionKind::Array(vec![
                ArrayElement::Expression(Expression {
                    kind: ExpressionKind::Literal(Literal::Number(1.0)),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                }),
                ArrayElement::Expression(Expression {
                    kind: ExpressionKind::Literal(Literal::Number(2.0)),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                }),
                ArrayElement::Expression(Expression {
                    kind: ExpressionKind::Literal(Literal::Number(3.0)),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                }),
            ]),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Should infer as Array<number>
        assert!(matches!(typ.kind, TypeKind::Array(_)));
    }

    #[test]
    fn test_infer_array_empty() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        // Empty array: []
        let mut expr = Expression {
            kind: ExpressionKind::Array(vec![]),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Should infer as Array<unknown>
        assert!(matches!(typ.kind, TypeKind::Array(_)));
    }

    #[test]
    fn test_infer_binary_op_sub() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(10.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(3.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Subtract, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_mul() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(6.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(7.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Multiply, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_div() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(10.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Divide, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_mod() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(10.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(3.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Modulo, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_eq() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Equal, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Boolean)
        ));
    }

    #[test]
    fn test_infer_binary_op_and() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(false)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::And, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // In Lua, 'and' returns one of its operands, so type is Unknown
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Unknown)
        ));
    }

    #[test]
    fn test_infer_binary_op_or() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(false)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Or, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // In Lua, 'or' returns one of its operands, so type is Unknown
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Unknown)
        ));
    }

    #[test]
    fn test_infer_unary_op_len() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let operand = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::String("hello".to_string())),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Unary(UnaryOp::Length, operand),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Length operator returns number
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_parenthesized() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let inner = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(42.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Parenthesized(inner),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Parenthesized expressions now correctly infer the type of their inner expression
        assert!(
            matches!(typ.kind, TypeKind::Literal(Literal::Number(n)) if (n - 42.0).abs() < f64::EPSILON)
        );
    }

    #[test]
    fn test_infer_type_assertion() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let inner = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(42.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let assert_type = Type {
            kind: TypeKind::Primitive(PrimitiveType::Number),
            span: Span::default(),
        };

        let mut expr = Expression {
            kind: ExpressionKind::TypeAssertion(inner, assert_type),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Type assertions currently return Unknown (not yet fully implemented)
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Unknown)
        ));
    }

    #[test]
    fn test_infer_object_expression() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        // Object literal: { x: 1, y: 2 }
        let name_id = interner.intern("x");
        let y_id = interner.intern("y");

        let mut expr = Expression {
            kind: ExpressionKind::Object(vec![
                ObjectProperty::Property {
                    key: Ident::new(name_id, Span::default()),
                    value: Box::new(Expression {
                        kind: ExpressionKind::Literal(Literal::Number(1.0)),
                        span: Span::default(),
                        annotated_type: None,
                        receiver_class: None,
                    }),
                    span: Span::default(),
                },
                ObjectProperty::Property {
                    key: Ident::new(y_id, Span::default()),
                    value: Box::new(Expression {
                        kind: ExpressionKind::Literal(Literal::Number(2.0)),
                        span: Span::default(),
                        annotated_type: None,
                        receiver_class: None,
                    }),
                    span: Span::default(),
                },
            ]),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Should infer as object type
        assert!(matches!(typ.kind, TypeKind::Object(_)));
    }

    #[test]
    fn test_infer_identifier_not_found() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let x_id = interner.intern("x");
        let mut expr = Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        // Should fail because x is not defined
        assert!(result.is_err());
    }

    #[test]
    fn test_infer_identifier_with_type() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();
        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        // Register a variable with a type
        let x_id = interner.intern("x");
        let x_type = Type {
            kind: TypeKind::Primitive(PrimitiveType::Number),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "x".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                x_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_power() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(3.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::Power, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_integer_divide() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(10.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(3.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::IntegerDivide, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_bitwise() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(3.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::BitwiseAnd, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_shift() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(1.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::ShiftLeft, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_binary_op_not_equal() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(1.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(2.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::NotEqual, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Boolean)
        ));
    }

    #[test]
    fn test_infer_null_coalesce() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Nil),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(42.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Binary(BinaryOp::NullCoalesce, left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // null ?? number should return number
        assert!(matches!(
            typ.kind,
            TypeKind::Literal(Literal::Number(n)) if n == 42.0
        ));
    }

    #[test]
    fn test_infer_optional_member() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let obj_id = interner.intern("obj");
        let obj_type = Type {
            kind: TypeKind::Object(ObjectType {
                members: vec![ObjectTypeMember::Property(PropertySignature {
                    is_readonly: false,
                    name: Ident::new(interner.intern("prop"), Span::default()),
                    is_optional: false,
                    type_annotation: Type::new(
                        TypeKind::Primitive(PrimitiveType::Number),
                        Span::default(),
                    ),
                    span: Span::default(),
                })],
                span: Span::default(),
            }),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "obj".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                obj_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let obj = Box::new(Expression {
            kind: ExpressionKind::Identifier(obj_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let member = typedlua_parser::ast::Spanned::new(interner.intern("prop"), Span::default());

        let mut expr = Expression {
            kind: ExpressionKind::OptionalMember(obj, member),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        // Should return an optional type (T | nil)
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_optional_index() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let arr_id = interner.intern("arr");
        let arr_type = Type {
            kind: TypeKind::Array(Box::new(Type::new(
                TypeKind::Primitive(PrimitiveType::Number),
                Span::default(),
            ))),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "arr".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                arr_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let obj = Box::new(Expression {
            kind: ExpressionKind::Identifier(arr_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let index = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(0.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::OptionalIndex(obj, index),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Should return an optional type (T | nil)
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_optional_call() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let func_id = interner.intern("maybeFunc");
        let func_type = Type {
            kind: TypeKind::Function(FunctionType {
                type_parameters: None,
                parameters: vec![],
                return_type: Box::new(Type::new(
                    TypeKind::Primitive(PrimitiveType::Number),
                    Span::default(),
                )),
                throws: None,
                span: Span::default(),
            }),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "maybeFunc".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                func_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let callee = Box::new(Expression {
            kind: ExpressionKind::Identifier(func_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::OptionalCall(callee, vec![], None),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Should return an optional type
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_function_expression() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Function(FunctionExpression {
                type_parameters: None,
                parameters: vec![],
                return_type: None,
                body: Block {
                    statements: vec![],
                    span: Span::default(),
                },
                span: Span::default(),
            }),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Function(_)));
    }

    #[test]
    fn test_infer_function_expression_with_return() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Function(FunctionExpression {
                type_parameters: None,
                parameters: vec![],
                return_type: None,
                body: Block {
                    statements: vec![],
                    span: Span::default(),
                },
                span: Span::default(),
            }),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Function(_)));
    }

    #[test]
    fn test_infer_arrow_function_basic() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Arrow(ArrowFunction {
                parameters: vec![],
                body: ArrowBody::Expression(Box::new(Expression {
                    kind: ExpressionKind::Literal(Literal::Number(1.0)),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                })),
                return_type: None,
                span: Span::default(),
            }),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_infer_object_spread() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let other_id = interner.intern("other");
        let other_type = Type {
            kind: TypeKind::Object(ObjectType {
                members: vec![ObjectTypeMember::Property(PropertySignature {
                    is_readonly: false,
                    name: Ident::new(interner.intern("a"), Span::default()),
                    is_optional: false,
                    type_annotation: Type::new(
                        TypeKind::Primitive(PrimitiveType::String),
                        Span::default(),
                    ),
                    span: Span::default(),
                })],
                span: Span::default(),
            }),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "other".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                other_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let obj_x = interner.intern("x");

        let mut expr = Expression {
            kind: ExpressionKind::Object(vec![
                ObjectProperty::Spread {
                    value: Box::new(Expression {
                        kind: ExpressionKind::Identifier(other_id),
                        span: Span::default(),
                        annotated_type: None,
                        receiver_class: None,
                    }),
                    span: Span::default(),
                },
                ObjectProperty::Property {
                    key: Ident::new(obj_x, Span::default()),
                    value: Box::new(Expression {
                        kind: ExpressionKind::Literal(Literal::Number(42.0)),
                        span: Span::default(),
                        annotated_type: None,
                        receiver_class: None,
                    }),
                    span: Span::default(),
                },
            ]),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(typ.kind, TypeKind::Object(_)));
    }

    #[test]
    fn test_infer_try_expression() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let mut expr = Expression {
            kind: ExpressionKind::Try(TryExpression {
                expression: Box::new(Expression {
                    kind: ExpressionKind::Literal(Literal::Number(1.0)),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                }),
                catch_variable: Ident::new(interner.intern("e"), Span::default()),
                catch_expression: Box::new(Expression {
                    kind: ExpressionKind::Literal(Literal::String("error".to_string())),
                    span: Span::default(),
                    annotated_type: None,
                    receiver_class: None,
                }),
                span: Span::default(),
            }),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Try should return union of both types
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_error_chain() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let result_id = interner.intern("result");
        let result_type = Type {
            kind: TypeKind::Primitive(PrimitiveType::Number),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "result".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                result_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Identifier(result_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Nil),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::ErrorChain(left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_infer_pipe_expression() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let double_id = interner.intern("double");
        let double_type = Type {
            kind: TypeKind::Function(FunctionType {
                type_parameters: None,
                parameters: vec![],
                return_type: Box::new(Type::new(
                    TypeKind::Primitive(PrimitiveType::Number),
                    Span::default(),
                )),
                throws: None,
                span: Span::default(),
            }),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "double".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                double_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let left = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let right = Box::new(Expression {
            kind: ExpressionKind::Identifier(double_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Pipe(left, right),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_infer_index_on_tuple() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let tuple_id = interner.intern("tuple");
        let tuple_type = Type {
            kind: TypeKind::Tuple(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), Span::default()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default()),
            ]),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "tuple".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                tuple_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let obj = Box::new(Expression {
            kind: ExpressionKind::Identifier(tuple_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let index = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(0.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Index(obj, index),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // Index on tuple should return union of element types
        assert!(matches!(typ.kind, TypeKind::Union(_)));
    }

    #[test]
    fn test_infer_unary_op_bitwise_not() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let operand = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Number(5.0)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Unary(UnaryOp::BitwiseNot, operand),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }

    #[test]
    fn test_infer_conditional_same_types() {
        let interner = StringInterner::new();
        let mut symbol_table = SymbolTable::new();
        let mut type_env = TypeEnvironment::new();
        let mut narrowing_context = super::super::super::super::narrowing::NarrowingContext::new();
        let access_control = AccessControl::new();

        let diagnostic_handler: Arc<dyn DiagnosticHandler> =
            Arc::new(CollectingDiagnosticHandler::new());

        let x_id = interner.intern("x");
        let y_id = interner.intern("y");
        let num_type = Type {
            kind: TypeKind::Primitive(PrimitiveType::Number),
            span: Span::default(),
        };

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "x".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                num_type.clone(),
                Span::default(),
            ))
            .unwrap();

        symbol_table
            .declare(super::super::super::super::symbol_table::Symbol::new(
                "y".to_string(),
                super::super::super::super::symbol_table::SymbolKind::Variable,
                num_type.clone(),
                Span::default(),
            ))
            .unwrap();

        let mut inferrer = create_test_inferrer(
            &mut symbol_table,
            &mut type_env,
            &mut narrowing_context,
            &access_control,
            &interner,
            &diagnostic_handler,
        );

        let cond = Box::new(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(true)),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let then_expr = Box::new(Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });
        let else_expr = Box::new(Expression {
            kind: ExpressionKind::Identifier(y_id),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        });

        let mut expr = Expression {
            kind: ExpressionKind::Conditional(cond, then_expr, else_expr),
            span: Span::default(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = inferrer.infer_expression(&mut expr);
        assert!(result.is_ok());
        let typ = result.unwrap();
        // When both branches have the same type, should return that type directly (not union)
        assert!(matches!(
            typ.kind,
            TypeKind::Primitive(PrimitiveType::Number)
        ));
    }
}
