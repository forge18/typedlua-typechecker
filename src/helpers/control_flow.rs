//! Control flow analysis utilities
//!
//! This module provides utilities for analyzing control flow in TypedLua programs,
//! including checking whether code paths always return or terminate.

use typedlua_parser::ast::expression::ExpressionKind;
use typedlua_parser::ast::statement::{Block, Statement};
use typedlua_parser::string_interner::StringInterner;

/// Check if a block always returns (has a return statement on all code paths).
///
/// This function recursively analyzes statements in a block to determine if
/// every possible execution path ends with a return statement or other terminating
/// statement (like throw).
///
/// # Parameters
///
/// - `block`: The block to analyze
/// - `interner`: String interner for resolving function names
///
/// # Returns
///
/// Returns `true` if the block always returns on all code paths, `false` otherwise.
pub fn block_always_returns(block: &Block, interner: &StringInterner) -> bool {
    for stmt in &block.statements {
        if statement_always_returns(stmt, interner) {
            return true;
        }
    }
    false
}

/// Check if a statement always returns.
///
/// This function analyzes whether a statement will definitely result in a return
/// or termination on all possible execution paths.
///
/// # Parameters
///
/// - `stmt`: The statement to analyze
/// - `interner`: String interner for resolving function names
///
/// # Returns
///
/// Returns `true` if the statement always returns/terminates, `false` otherwise.
///
/// # Analyzed Statement Types
///
/// - **Return**: Always returns
/// - **Throw**: Always terminates
/// - **If**: Returns if both then and else branches return
/// - **Try-catch**: Returns if finally returns, OR if try + all catches return
/// - **Expression**: Returns if calling a known non-returning function (unreachable, error, throw)
pub fn statement_always_returns(stmt: &Statement, interner: &StringInterner) -> bool {
    match stmt {
        Statement::Return(_) => true,
        Statement::If(if_stmt) => {
            // If statement always returns if both branches always return
            let then_returns = block_always_returns(&if_stmt.then_block, interner);
            let else_returns = if_stmt
                .else_block
                .as_ref()
                .map(|b| block_always_returns(b, interner))
                .unwrap_or(false);
            then_returns && else_returns
        }
        Statement::Try(try_stmt) => {
            // Try-catch always returns if:
            // 1. Finally block always returns (catches all paths), OR
            // 2. Try block always returns AND all catch blocks always return
            if let Some(ref finally) = try_stmt.finally_block {
                if block_always_returns(finally, interner) {
                    return true;
                }
            }

            // Check try block and all catch blocks
            let try_returns = block_always_returns(&try_stmt.try_block, interner);
            let all_catches_return = try_stmt
                .catch_clauses
                .iter()
                .all(|catch| block_always_returns(&catch.body, interner));

            try_returns && all_catches_return && !try_stmt.catch_clauses.is_empty()
        }
        Statement::Throw(_) => true,
        Statement::Expression(expr) => {
            // Check if the expression is a call to a function that never returns
            // (like unreachable(), error(), throw)
            if let ExpressionKind::Call(callee, _, _) = &expr.kind {
                if let ExpressionKind::Identifier(string_id) = &callee.kind {
                    let name = interner.resolve(*string_id);
                    name == "unreachable" || name == "error" || name == "throw"
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}
