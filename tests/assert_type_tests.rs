use luanext_parser::lexer::Lexer;
use luanext_parser::parser::Parser;
use luanext_typechecker::cli::diagnostics::CollectingDiagnosticHandler;
use luanext_typechecker::{TypeCheckError, TypeChecker};
use std::sync::Arc;

fn parse_and_check(source: &str) -> (Result<(), TypeCheckError>, Arc<CollectingDiagnosticHandler>) {
    let arena = bumpalo::Bump::new();
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(source, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common, &arena);
    let program = parser.parse().expect("Parsing failed");
    let mut type_checker = TypeChecker::new(handler.clone(), &interner, &common, &arena);
    let result = type_checker.check_program(&program);
    (result, handler)
}

#[test]
fn test_assert_type_requires_type_argument() {
    let source = "const x = assertType(42);";

    let (result, _handler) = parse_and_check(source);

    assert!(
        result.is_err(),
        "Expected error for missing type argument"
    );
    if let Err(err) = result {
        assert!(
            err.to_string().contains("assertType requires exactly one type argument"),
            "Expected specific error message, got: {}",
            err
        );
    }
}

#[test]
fn test_assert_type_requires_value_argument() {
    let source = "const x = assertType<string>();";

    let (result, _handler) = parse_and_check(source);

    assert!(
        result.is_err(),
        "Expected error for missing value argument"
    );
    if let Err(err) = result {
        assert!(
            err.to_string().contains("assertType requires exactly one argument"),
            "Expected specific error message, got: {}",
            err
        );
    }
}

#[test]
fn test_assert_type_too_many_type_arguments() {
    let source = "const x = assertType<string, number>(42);";

    let (result, _handler) = parse_and_check(source);

    assert!(
        result.is_err(),
        "Expected error for too many type arguments"
    );
    if let Err(err) = result {
        assert!(
            err.to_string().contains("assertType expects exactly one type argument but received 2"),
            "Expected specific error message, got: {}",
            err
        );
    }
}

#[test]
fn test_assert_type_primitive_string() {
    let source = "const input: unknown = \"hello\";\nconst name = assertType<string>(input);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_primitive_number() {
    let source = "const input: unknown = 42;\nconst num = assertType<number>(input);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_primitive_boolean() {
    let source = "const input: unknown = true;\nconst flag = assertType<boolean>(input);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_in_function() {
    let source = "function parseData(raw: unknown): string {\n    return assertType<string>(raw);\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_union() {
    let source = "const input: unknown = \"hello\";\nconst id = assertType<string | number>(input);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_nullable() {
    let source = "const input: unknown = \"hello\";\nconst name = assertType<string?>(input);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_literal_string() {
    let source = "const status = assertType<\"success\">(\"success\");";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

#[test]
fn test_assert_type_literal_number() {
    let source = "const code = assertType<404>(404);";

    let (result, _handler) = parse_and_check(source);
    assert!(result.is_ok(), "Type checking should succeed: {:?}", result.err());
}

// ============================================================================
// Phase 4: Type Narrowing Integration Tests
// ============================================================================

#[test]
fn test_super_simple_function() {
    let source = "function example(x: number): number {\n    return x;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Simplest possible function should work: {:?}",
        result.err()
    );
}

#[test]
fn test_unknown_parameter() {
    let source = "function example(x: unknown): unknown {\n    return x;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Unknown parameter should work: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_called_on_unknown() {
    let source = "function example(x: unknown): string { return assertType<string>(x); }";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "assertType on unknown parameter should work: {:?}",
        result.err()
    );
}

#[test]
fn test_simple_function_parameter_access_string() {
    // Baseline test: can we even access a typed parameter?
    let source = "function example(input: string): number {\n    return input.length;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Basic string parameter access should work: {:?}",
        result.err()
    );
}

#[test]
fn test_simple_function_parameter_access_unknown() {
    // LuaNext uses gradual typing - accessing members on unknown returns unknown (no error)
    let source = "function example(input: unknown): unknown {\n    return input.anything;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Gradual typing allows member access on unknown"
    );
}

#[test]
fn test_existing_narrowing_with_typeof() {
    // First, verify that existing typeof narrowing works
    let source = "function example(input: unknown): string {\n    if typeof(input) == \"string\" {\n        return input;\n    }\n    return \"\";\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Existing typeof narrowing should work: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_narrows_variable_return_type() {
    let source = "function example(input: unknown): string {\n    assertType<string>(input);\n    return input;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Should be able to return narrowed variable as string: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_narrows_from_unknown_to_number() {
    let source = "function processData(data: unknown): number {\n    assertType<number>(data);\n    // data is now number, can return it as number\n    return data;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Should return narrowed unknown as number: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_narrows_from_union_to_specific_type() {
    let source = "function handleValue(value: string | number): string {\n    assertType<string>(value);\n    // value is now narrowed to string\n    return value;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Should return narrowed union as string: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_narrows_nullable_to_non_null() {
    let source = "function getString(input: string?): string {\n    assertType<string>(input);\n    // input is now string (not string?)\n    return input;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Should return narrowed nullable as non-null: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_narrowing_persists_across_statements() {
    let source = "function multi(input: unknown): string {\n    assertType<string>(input);\n    const temp = input;  // temp should be string\n    return temp;         // should succeed\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Narrowing should persist across multiple statements: {:?}",
        result.err()
    );
}

#[test]
fn test_assert_type_return_value_and_narrowing_both_work() {
    let source = "function test(input: unknown): string {\n    // Both the return value and the argument should be narrowed\n    const validated = assertType<string>(input);\n\n    // Both validated and input should be string\n    // We can return either one\n    return input;\n}";

    let (result, _handler) = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Both return value typing and argument narrowing should work: {:?}",
        result.err()
    );
}
