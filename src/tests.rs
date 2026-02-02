use super::*;
use crate::diagnostics::CollectingDiagnosticHandler;
use std::sync::Arc;
use typedlua_parser::lexer::Lexer;
use typedlua_parser::parser::Parser;

fn parse_and_check(source: &str) -> Result<(), TypeCheckError> {
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) =
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(source, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common);
    let mut program = parser.parse().expect("Parsing failed");
    let mut type_checker = TypeChecker::new(handler, &interner, &common);
    type_checker.check_program(&mut program)
}

#[test]
fn test_generic_function_declaration() {
    let source = r#"
        function identity<T>(value: T): T
            return value
        end
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Generic function should type check");
}

#[test]
fn test_generic_function_with_constraint() {
    let source = r#"
        function process<T extends string>(value: T): T
            return value
        end
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Generic function with constraint should type check"
    );
}

#[test]
fn test_generic_function_multiple_params() {
    let source = r#"
        function map<T, U>(value: T, mapper: (item: T) -> U): U
            return mapper(value)
        end
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Generic function with multiple type params should type check"
    );
}

#[test]
fn test_generic_type_alias() {
    let source = r#"
        type Result<T, E = string> = { ok: T } | { error: E }
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Generic type alias should type check");
}

#[test]
fn test_generic_interface() {
    let source = r#"
        interface Container<T> {
            value: T,
            get(): T,
        }
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Generic interface should type check");
}

#[test]
fn test_generic_class() {
    let source = r#"
        class Box<T> {
        }
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Generic class should type check");
}

#[test]
fn test_non_generic_function() {
    let source = r#"
        function add(a: number, b: number): number
            return a + b
        end
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Non-generic function should still work");
}

#[test]
fn test_non_generic_interface() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
        }
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Non-generic interface should still work");
}

#[test]
fn test_generic_function_usage_in_body() {
    let source = r#"
        function identity<T>(value: T): T
            const result: T = value
            return result
        end
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Type parameter should be usable in function body"
    );
}

#[test]
fn test_multiple_generic_functions() {
    let source = r#"
        function first<T>(value: T): T
            return value
        end

        function second<U>(value: U): U
            return value
        end
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Multiple generic functions should work");
}

// Utility Types Tests

#[test]
fn test_utility_type_partial() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
            email: string,
        }

        type PartialPerson = Partial<Person>
    "#;

    let result = parse_and_check(source);
    if let Err(ref e) = result {
        eprintln!("Error: {:?}", e);
    }
    assert!(result.is_ok(), "Partial<T> utility type should work");
}

#[test]
fn test_utility_type_required() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
        }

        type RequiredPerson = Required<Person>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Required<T> utility type should work");
}

#[test]
fn test_utility_type_readonly() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
        }

        type ReadonlyPerson = Readonly<Person>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Readonly<T> utility type should work");
}

#[test]
fn test_utility_type_record() {
    let source = r#"
        type StringToNumber = Record<string, number>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Record<K, V> utility type should work");
}

#[test]
fn test_utility_type_pick() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
            email: string,
        }

        type NameAndAge = Pick<Person, "name" | "age">
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Pick<T, K> utility type should work");
}

#[test]
fn test_utility_type_omit() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
            email: string,
        }

        type PersonWithoutEmail = Omit<Person, "email">
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Omit<T, K> utility type should work");
}

#[test]
fn test_utility_type_exclude() {
    let source = r#"
        type StringOrNumber = string | number | boolean
        type OnlyStringOrNumber = Exclude<StringOrNumber, boolean>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Exclude<T, U> utility type should work");
}

#[test]
fn test_utility_type_extract() {
    let source = r#"
        type StringOrNumber = string | number | boolean
        type OnlyString = Extract<StringOrNumber, string>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Extract<T, U> utility type should work");
}

#[test]
fn test_utility_type_non_nilable() {
    let source = r#"
        type MaybeString = string | nil
        type DefinitelyString = NonNilable<MaybeString>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "NonNilable<T> utility type should work");
}

#[test]
fn test_utility_type_nilable() {
    let source = r#"
        type MaybeString = Nilable<string>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Nilable<T> utility type should work");
}

#[test]
fn test_utility_type_return_type() {
    let source = r#"
        type Func = () -> number
        type Result = ReturnType<Func>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "ReturnType<F> utility type should work");
}

#[test]
fn test_utility_type_parameters() {
    let source = r#"
        type Func = (a: string, b: number) -> void
        type Params = Parameters<Func>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Parameters<F> utility type should work");
}

#[test]
fn test_utility_types_composition() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
            email: string,
        }

        type PartialReadonlyPerson = Partial<Readonly<Person>>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Composed utility types should work");
}

#[test]
fn test_utility_types_with_generics() {
    let source = r#"
        interface Container<T> {
            value: T,
            optional: string,
        }

        type PartialContainer<T> = Partial<Container<T>>
    "#;

    let result = parse_and_check(source);
    assert!(result.is_ok(), "Utility types with generics should work");
}

// Mapped Types Tests

#[test]
fn test_mapped_type_basic() {
    let source = r#"
        type StringRecord = { [K in "name" | "age"]: string }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Basic mapped type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_with_readonly() {
    let source = r#"
        type ReadonlyPoint = { readonly [K in "x" | "y"]: number }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with readonly should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_with_optional() {
    let source = r#"
        type OptionalRecord = { [K in "foo" | "bar"]?: boolean }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with optional should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_with_both_modifiers() {
    let source = r#"
        type FrozenPartial = { readonly [K in "a" | "b" | "c"]?: string }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with both modifiers should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_single_key() {
    let source = r#"
        type SingleKey = { [K in "value"]: number }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with single key should type check: {:?}",
        result.err()
    );
}

// keyof Operator Tests

#[test]
fn test_keyof_basic_interface() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
        }

        type PersonKeys = keyof Person
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "keyof with basic interface should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_keyof_with_methods() {
    let source = r#"
        interface Calculator {
            value: number,
            add(): number,
            subtract(): number,
        }

        type CalculatorKeys = keyof Calculator
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "keyof with methods should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_keyof_empty_interface() {
    let source = r#"
        interface Empty {
        }

        type EmptyKeys = keyof Empty
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "keyof with empty interface should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_keyof_inline_object() {
    let source = r#"
        type Keys = keyof { x: number, y: number }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "keyof with inline object type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_keyof_with_mapped_type() {
    let source = r#"
        interface Point {
            x: number,
            y: number,
        }

        type ReadonlyPoint = { readonly [K in keyof Point]: Point[K] }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "keyof with mapped type should type check: {:?}",
        result.err()
    );
}

// Mapped Types with Type References Tests

#[test]
fn test_mapped_type_with_keyof() {
    let source = r#"
        interface Point {
            x: number,
            y: number,
        }

        type ReadonlyPoint = { readonly [K in keyof Point]: number }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with keyof should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_keyof_complex() {
    let source = r#"
        interface User {
            name: string,
            age: number,
            email: string,
        }

        type OptionalUser = { [K in keyof User]?: User[K] }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with keyof and index access should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_readonly_and_optional() {
    let source = r#"
        interface Config {
            host: string,
            port: number,
        }

        type FrozenConfig = { readonly [K in keyof Config]?: Config[K] }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with readonly and optional should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_with_type_reference() {
    let source = r#"
        type Keys = "a" | "b" | "c"
        type Mapped = { [K in Keys]: number }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with type reference should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_mapped_type_with_nested_type_reference() {
    let source = r#"
        type BaseKeys = "x" | "y"
        type Keys = BaseKeys | "z"
        type Mapped = { [K in Keys]: string }
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Mapped type with nested type reference should type check: {:?}",
        result.err()
    );
}

// Conditional Types Tests

#[test]
fn test_conditional_type_basic() {
    let source = r#"
        type IsString<T> = T extends string ? "yes" : "no"
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Basic conditional type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_true_branch() {
    let source = r#"
        type Result = string extends string ? number : boolean
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Conditional type true branch should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_false_branch() {
    let source = r#"
        type Result = string extends number ? boolean : string
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Conditional type false branch should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_with_primitives() {
    let source = r#"
        type TypeName<T> = T extends string ? "string" :
                           T extends number ? "number" :
                           T extends boolean ? "boolean" :
                           "other"
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Nested conditional types should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_distributive() {
    let source = r#"
        type ToArray<T> = T extends unknown ? T[] : never
        type Result = ToArray<string | number>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Distributive conditional type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_exclude_like() {
    let source = r#"
        type MyExclude<T, U> = T extends U ? never : T
        type Result = MyExclude<string | number | boolean, string>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Exclude-like conditional type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_extract_like() {
    let source = r#"
        type MyExtract<T, U> = T extends U ? T : never
        type Result = MyExtract<string | number | boolean, string>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Extract-like conditional type should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_with_interface() {
    let source = r#"
        interface Person {
            name: string,
            age: number,
        }

        type IsObject<T> = T extends Person ? "person" : "not person"
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Conditional type with interface should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_conditional_type_never() {
    let source = r#"
        type OnlyStrings<T> = T extends string ? T : never
        type Result = OnlyStrings<string>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Conditional type with never should type check: {:?}",
        result.err()
    );
}

// Infer Keyword Tests

#[test]
fn test_infer_array_element() {
    let source = r#"
        type ElementType<T> = T extends (infer U)[] ? U : never
        type Result = ElementType<string[]>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with array element should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_function_return() {
    let source = r#"
        type ReturnTypeInfer<T> = T extends (...args: unknown[]) -> infer R ? R : never
        type Result = ReturnTypeInfer<() -> number>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with function return should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_function_params() {
    let source = r#"
        type FirstParam<T> = T extends (arg: infer P) -> unknown ? P : never
        type Result = FirstParam<(x: string) -> void>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with function parameter should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_tuple_element() {
    let source = r#"
        type FirstElement<T> = T extends [infer F, ...unknown[]] ? F : never
        type Result = FirstElement<[string, number]>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with tuple element should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_multiple_positions() {
    let source = r#"
        type Swap<T> = T extends [infer A, infer B] ? [B, A] : never
        type Result = Swap<[string, number]>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with multiple positions should type check: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_no_match() {
    let source = r#"
        type ElementType<T> = T extends (infer U)[] ? U : string
        type Result = ElementType<number>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer no match should return false branch: {:?}",
        result.err()
    );
}

#[test]
fn test_infer_nested_array() {
    let source = r#"
        type Unwrap<T> = T extends (infer U)[] ? Unwrap<U> : T
        type Result = Unwrap<string[][][]>
    "#;

    let result = parse_and_check(source);
    assert!(
        result.is_ok(),
        "Infer with nested recursion should type check: {:?}",
        result.err()
    );
}

// Template Literal Types Tests

#[test]
fn test_template_literal_simple() {
    let source = r#"
        type Greeting = `Hello`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_single_interpolation() {
    let source = r#"
        type Name = "World"
        type Greeting = `Hello ${Name}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_multiple_interpolations() {
    let source = r#"
        type First = "John"
        type Last = "Doe"
        type FullName = `${First} ${Last}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_union_expansion() {
    let source = r#"
        type Color = "red" | "blue" | "green"
        type ColorClass = `color-${Color}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_multiple_unions() {
    let source = r#"
        type Size = "sm" | "md" | "lg"
        type Color = "red" | "blue"
        type Class = `btn-${Size}-${Color}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_number_interpolation() {
    let source = r#"
        type Version = 1 | 2 | 3
        type VersionString = `v${Version}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_boolean_interpolation() {
    let source = r#"
        type Bool = true | false
        type BoolString = `is-${Bool}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_complex() {
    let source = r#"
        type Prefix = "http" | "https"
        type Domain = "example.com"
        type Url = `${Prefix}://${Domain}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_in_object() {
    let source = r#"
        type EventName = "click" | "hover"
        type EventHandler = `on${EventName}`

        interface Component {
            onclick: () -> void,
            onhover: () -> void
        }
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}

#[test]
fn test_template_literal_nested() {
    let source = r#"
        type Inner = "a" | "b"
        type Middle = `x${Inner}`
        type Outer = `y${Middle}`
    "#;
    let result = parse_and_check(source);
    assert!(result.is_ok());
}
