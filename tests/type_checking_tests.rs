use luanext_parser::lexer::Lexer;
use luanext_parser::parser::Parser;
use luanext_typechecker::cli::diagnostics::CollectingDiagnosticHandler;
use luanext_typechecker::{TypeCheckError, TypeChecker};
use std::sync::Arc;

fn parse_and_check(source: &str) -> Result<(), TypeCheckError> {
    let arena = bumpalo::Bump::new();
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(source, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common, &arena);
    let program = parser.parse().expect("Parsing failed");
    let mut type_checker = TypeChecker::new(handler, &interner, &common, &arena);
    type_checker.check_program(&program)
}

#[test]
fn test_empty_program() {
    let result = parse_and_check("");
    assert!(result.is_ok());
}

#[test]
fn test_simple_variable_declaration() {
    let source = r#"
        local x: number = 42
    "#;
    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Simple variable declaration should type check"
    );
}

#[test]
fn test_type_annotation_number() {
    let source = r#"
        local num: number = 10
        local num2: number = 20.5
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Number type annotation should work");
}

#[test]
fn test_type_annotation_string() {
    let source = r#"
        local str: string = "hello"
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "String type annotation should work");
}

#[test]
fn test_type_annotation_boolean() {
    let source = r#"
        local flag: boolean = true
        local flag2: boolean = false
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Boolean type annotation should work");
}

#[test]
fn test_type_annotation_nil() {
    let source = r#"
        local n: nil = nil
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Nil type annotation should work");
}

#[test]
fn test_table_literal() {
    let source = r#"
        local t = { a = 1, b = "hello" }
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Table literal should type check");
}

#[test]
fn test_typed_table_literal() {
    let source = r#"
        local t: { name: string, age: number } = { name = "test", age = 25 }
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Typed table literal should type check");
}

#[test]
fn test_if_statement() {
    let source = r#"
        local x: number = 10
        if x > 5 then
            x = 5
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "If statement should type check");
}

#[test]
fn test_while_loop() {
    let source = r#"
        local i: number = 0
        while i < 10 do
            i = i + 1
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "While loop should type check");
}

#[test]
fn test_for_loop() {
    let source = r#"
        for i = 1, 10 do
            local x: number = i
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "For loop should type check");
}

#[test]
fn test_binary_expression_number() {
    let source = r#"
        local a: number = 10 + 5
        local b: number = 20 * 3
        local c: number = 100 / 4
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Binary expressions should type check");
}

#[test]
fn test_string_concatenation() {
    let source = r#"
        local s: string = "hello" .. " " .. "world"
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "String concatenation should type check");
}

#[test]
fn test_relational_operators() {
    let source = r#"
        local a: boolean = 10 > 5
        local b: boolean = 3 <= 4
        local c: boolean = "a" < "b"
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Relational operators should type check");
}

#[test]
fn test_logical_operators() {
    let source = r#"
        local a: boolean = true and false
        local b: boolean = true or false
        local c: boolean = not true
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Logical operators should type check");
}

#[test]
fn test_type_inference() {
    let source = r#"
        local x = 42
        local y = "hello"
        local z = true
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Type inference should work");
}

#[test]
fn test_multiple_local_declarations() {
    let source = r#"
        local a: number, b: number, c: number = 1, 2, 3
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Multiple declarations should type check");
}

#[test]
fn test_nil_coalescing() {
    let source = r#"
        local a: number? = nil
        local b: number = a or 0
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Nil coalescing should type check");
}

#[test]
fn test_block_comment() {
    let source = r#"
        --[[ This is a block comment
        that spans multiple lines
        --]]
        local x: number = 42
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Block comments should be ignored");
}

#[test]
fn test_line_comment() {
    let source = r#"
        -- This is a line comment
        local x: number = 42 -- end of line comment
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Line comments should be ignored");
}

#[test]
fn test_repeat_until_loop() {
    let source = r#"
        local i: number = 0
        repeat
            i = i + 1
        until i >= 10
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Repeat-until loop should type check");
}

#[test]
fn test_nested_if() {
    let source = r#"
        local x: number = 5
        if x > 0 then
            if x > 10 then
                x = 10
            else
                x = 0
            end
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Nested if statements should type check");
}

#[test]
fn test_elseif_chain() {
    let source = r#"
        local x: number = 5
        if x == 1 then
            x = 10
        elseif x == 2 then
            x = 20
        elseif x == 3 then
            x = 30
        else
            x = 0
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Else-if chain should type check");
}

#[test]
fn test_table_access() {
    let source = r#"
        local t = { a = 1, b = 2 }
        local x: number = t.a
        local y: number = t.b
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Table access should type check");
}

#[test]
fn test_table_assignment() {
    let source = r#"
        local t: { a: number, b: number } = { a = 1, b = 2 }
        t.a = 10
        t.b = 20
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Table assignment should type check");
}

#[test]
fn test_function_param_access_do_end() {
    // Function body with do/end syntax
    let source = r#"
        function add(a: number, b: number): number do
            return a + b
        end
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Function params should be accessible in do/end body: {:?}", result);
}

#[test]
fn test_function_param_access_braces() {
    // Function body with { } brace syntax
    let source = r#"
        function add(a: number, b: number): number {
            return a + b
        }
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Function params should be accessible in brace body: {:?}", result);
}

#[test]
fn test_function_param_access_braces_with_if() {
    // Function body with { } brace syntax containing if/then/else
    let source = r#"
        function process(value: number): string {
            if value == 0 then
                return "zero"
            else
                return "nonzero"
            end
        }
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "Function params should be accessible in brace body with if: {:?}", result);
}

#[test]
fn test_all_variable_declaration_forms() {
    // Test all 6 variable declaration/assignment forms
    let source = r#"
        global x: number = 0
        x = x + 1

        y: number = 0
        y = y + 1

        global z: number = 0
        z = z + 1

        global w = 0
        w = w + 1

        local a: number = 0
        a = a + 1

        local b = 0
        b = b + 1
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok(), "All variable forms should type check: {:?}", result);
}
