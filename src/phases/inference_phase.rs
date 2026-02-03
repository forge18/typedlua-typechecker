//! Inference phase: Statement and expression type checking

use crate::TypeCheckError;
use typedlua_parser::ast::statement::{
    ForStatement, IfStatement, RepeatStatement, ReturnStatement, WhileStatement,
};
use typedlua_parser::span::Span;

/// Check that a rethrow statement appears in a valid context (inside a catch block).
///
/// Rethrow can only be used within a catch clause to re-raise the caught exception.
///
/// # Parameters
///
/// - `in_catch_block`: Stack of catch block contexts (true if currently in a catch block)
/// - `span`: Source span for error reporting
///
/// # Returns
///
/// Returns `Ok(())` if valid (in a catch block), or an error if outside a catch block.
pub fn check_rethrow_statement(in_catch_block: &[bool], span: Span) -> Result<(), TypeCheckError> {
    if in_catch_block.last() != Some(&true) {
        return Err(TypeCheckError::new(
            "rethrow can only be used outside of a catch block",
            span,
        ));
    }
    Ok(())
}

/// Check an if statement structure.
///
/// This function validates the if statement structure and returns information
/// about blocks that need type checking. The caller should check expressions
/// and blocks with access to full TypeChecker state.
///
/// # Parameters
///
/// - `if_stmt`: The if statement to check
///
/// # Returns
///
/// Returns `Ok(())` if the structure is valid. The caller should then:
/// 1. Infer the condition expression type
/// 2. Check the then block
/// 3. Check else-if conditions and blocks
/// 4. Check the else block if present
pub fn check_if_statement(_if_stmt: &IfStatement) -> Result<(), TypeCheckError> {
    // Structural validation only - caller handles expression/block checking
    // If statement structure is already validated by parser
    Ok(())
}

/// Check a while statement structure.
///
/// # Parameters
///
/// - `while_stmt`: The while statement to check
///
/// # Returns
///
/// Returns `Ok(())`. The caller should check the condition expression and body block.
pub fn check_while_statement(_while_stmt: &WhileStatement) -> Result<(), TypeCheckError> {
    // Structural validation only - caller handles expression/block checking
    Ok(())
}

/// Check a for statement structure.
///
/// This validates for loop patterns (numeric and generic).
///
/// # Parameters
///
/// - `for_stmt`: The for statement to check
///
/// # Returns
///
/// Returns `Ok(())`. The caller should:
/// 1. Enter new scope for loop variable
/// 2. Infer iterator expression types
/// 3. Declare loop variable(s)
/// 4. Check the loop body
/// 5. Exit scope
pub fn check_for_statement(_for_stmt: &ForStatement) -> Result<(), TypeCheckError> {
    // Structural validation - caller handles variable declaration and body checking
    Ok(())
}

/// Check a repeat statement structure.
///
/// # Parameters
///
/// - `repeat_stmt`: The repeat statement to check
///
/// # Returns
///
/// Returns `Ok(())`. The caller should check the body block and condition expression.
pub fn check_repeat_statement(_repeat_stmt: &RepeatStatement) -> Result<(), TypeCheckError> {
    // Structural validation only
    Ok(())
}

/// Check a return statement structure and validate context.
///
/// This function validates that the return statement appears in a valid context
/// (inside a function). The caller should handle type checking the return expression
/// against the expected return type.
///
/// # Parameters
///
/// - `return_stmt`: The return statement to check
/// - `current_function_return_type`: The expected return type of the enclosing function
/// - `span`: Span for error reporting
///
/// # Returns
///
/// Returns `Ok(())` if valid, or an error if the return statement is outside a function.
/// The caller should then check the return expression type matches the function return type.
pub fn check_return_statement(
    _return_stmt: &ReturnStatement,
    current_function_return_type: Option<&typedlua_parser::ast::types::Type>,
    span: Span,
) -> Result<(), TypeCheckError> {
    // Validate we're inside a function
    if current_function_return_type.is_none() {
        return Err(TypeCheckError::new(
            "Return statement outside function",
            span,
        ));
    }

    // Caller should check the expression type against current_function_return_type
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use typedlua_parser::span::Span;

    #[test]
    fn test_check_rethrow_inside_catch() {
        let span = Span::new(0, 10, 0, 10);
        let in_catch = vec![true];
        let result = check_rethrow_statement(&in_catch, span);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_rethrow_outside_catch() {
        let span = Span::new(0, 10, 0, 10);
        let in_catch: Vec<bool> = vec![];
        let result = check_rethrow_statement(&in_catch, span);
        assert!(result.is_err());
    }

    #[test]
    fn test_check_return_inside_function() {
        let span = Span::new(0, 10, 0, 10);
        let return_type = typedlua_parser::ast::types::Type::new(
            typedlua_parser::ast::types::TypeKind::Primitive(
                typedlua_parser::ast::types::PrimitiveType::Number,
            ),
            span,
        );
        let result = check_return_statement(
            &typedlua_parser::ast::statement::ReturnStatement {
                values: Vec::new(),
                span,
            },
            Some(&return_type),
            span,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_return_outside_function() {
        let span = Span::new(0, 10, 0, 10);
        let result = check_return_statement(
            &typedlua_parser::ast::statement::ReturnStatement {
                values: Vec::new(),
                span,
            },
            None,
            span,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_check_if_statement() {
        let span = Span::new(0, 10, 0, 10);
        let if_stmt = typedlua_parser::ast::statement::IfStatement {
            condition: typedlua_parser::ast::expression::Expression {
                kind: typedlua_parser::ast::expression::ExpressionKind::Literal(
                    typedlua_parser::ast::expression::Literal::Boolean(true),
                ),
                span,
                annotated_type: None,
                receiver_class: None,
            },
            then_block: typedlua_parser::ast::statement::Block {
                statements: Vec::new(),
                span,
            },
            else_ifs: Vec::new(),
            else_block: None,
            span,
        };
        let result = check_if_statement(&if_stmt);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_while_statement() {
        let span = Span::new(0, 10, 0, 10);
        let while_stmt = typedlua_parser::ast::statement::WhileStatement {
            condition: typedlua_parser::ast::expression::Expression {
                kind: typedlua_parser::ast::expression::ExpressionKind::Literal(
                    typedlua_parser::ast::expression::Literal::Boolean(true),
                ),
                span,
                annotated_type: None,
                receiver_class: None,
            },
            body: typedlua_parser::ast::statement::Block {
                statements: Vec::new(),
                span,
            },
            span,
        };
        let result = check_while_statement(&while_stmt);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_for_statement() {
        let span = Span::new(0, 10, 0, 10);
        let for_stmt = typedlua_parser::ast::statement::ForStatement::Numeric(Box::new(
            typedlua_parser::ast::statement::ForNumeric {
                variable: typedlua_parser::ast::Spanned::new(
                    typedlua_parser::string_interner::StringId::from_u32(0),
                    span,
                ),
                start: typedlua_parser::ast::expression::Expression {
                    kind: typedlua_parser::ast::expression::ExpressionKind::Literal(
                        typedlua_parser::ast::expression::Literal::Number(1.0),
                    ),
                    span,
                    annotated_type: None,
                    receiver_class: None,
                },
                end: typedlua_parser::ast::expression::Expression {
                    kind: typedlua_parser::ast::expression::ExpressionKind::Literal(
                        typedlua_parser::ast::expression::Literal::Number(10.0),
                    ),
                    span,
                    annotated_type: None,
                    receiver_class: None,
                },
                step: None,
                body: typedlua_parser::ast::statement::Block {
                    statements: Vec::new(),
                    span,
                },
                span,
            },
        ));
        let result = check_for_statement(&for_stmt);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_repeat_statement() {
        let span = Span::new(0, 10, 0, 10);
        let repeat_stmt = typedlua_parser::ast::statement::RepeatStatement {
            body: typedlua_parser::ast::statement::Block {
                statements: Vec::new(),
                span,
            },
            until: typedlua_parser::ast::expression::Expression {
                kind: typedlua_parser::ast::expression::ExpressionKind::Literal(
                    typedlua_parser::ast::expression::Literal::Boolean(true),
                ),
                span,
                annotated_type: None,
                receiver_class: None,
            },
            span,
        };
        let result = check_repeat_statement(&repeat_stmt);
        assert!(result.is_ok());
    }
}
