use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::sync::Arc;
use typedlua_parser::lexer::Lexer;
use typedlua_parser::parser::Parser;
use typedlua_parser::string_interner::StringInterner;

use typedlua_typechecker::{cli::diagnostics::CollectingDiagnosticHandler, TypeChecker};

fn parse_and_check(code: &str) {
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) = StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(code, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common);
    let mut program = parser.parse().expect("Parsing failed");
    let mut checker = TypeChecker::new(handler.clone(), &interner, &common)
        .with_stdlib()
        .unwrap();
    black_box(checker.check_program(&mut program).unwrap());
}

fn generate_generic_chain(depth: usize) -> String {
    let mut code = String::new();
    code.push_str("type T1 = number\n");
    for i in 2..=depth {
        code.push_str(&format!("type T{} = T{} | nil\n", i, i - 1));
    }
    code.push_str("function identity<T>(x: T): T return x end\n");
    for i in 0..50 {
        code.push_str(&format!(
            "local v{}: T{} = identity<T{}>(nil)\n",
            i, depth, depth
        ));
    }
    code
}

fn generate_generic_instantiation(count: usize, depth: usize) -> String {
    let mut code = String::new();

    for i in 0..count {
        code.push_str(&format!(
            "class Container{}<T> {{\n    value: T\n\n    constructor(v: T)\n        self.value = v\n    end\n\n    get(): T\n        return self.value\n    end\n\n    map<U>(f: (T) => U): U\n        return f(self.value)\n    end\n}}\n\n",
            i
        ));
    }

    for i in 0..depth {
        code.push_str(&format!("local c{} = Container{}(42)\n", i, i % count));
        code.push_str(&format!("local r{} = c{}:get()\n", i, i));
        code.push_str(&format!(
            "local m{} = c{}:map(function(x: number): string return tostring(x) end)\n",
            i, i
        ));
    }

    code
}

fn generate_generic_constraints(count: usize) -> String {
    let mut code = String::new();

    code.push_str("interface Loggable { __tostring: () => string }\n");
    code.push_str("interface Serializable { serialize: () => string }\n");
    code.push_str("interface Comparable<T> { compare: (T) => number }\n");

    for i in 0..count {
        code.push_str(&format!(
            "function process{}<T extends Loggable>(value: T): string\n    return tostring(value)\nend\n",
            i
        ));
        code.push_str(&format!(
            "function compare{}<T extends Comparable<T>>(a: T, b: T): number\n    return a:compare(b)\nend\n",
            i
        ));
        code.push_str(&format!(
            "function chain{}<T, U, V>(a: T, b: U, f: (T) => U, g: (U) => V): V\n    return g(f(a))\nend\n",
            i
        ));
    }

    code.push_str("local x: number = 42\n");
    for i in 0..count {
        code.push_str(&format!(
            "local p{} = process{}<string>(tostring(x))\n",
            i, i
        ));
    }

    code
}

fn generate_polymorphic_functions(count: usize) -> String {
    let mut code = String::new();

    for i in 0..count {
        code.push_str(&format!(
            "function map{}<T, U>(arr: T[], f: (T) => U): U[]\n    local result = {{}}\n    for _, v in ipairs(arr) do\n        table.insert(result, f(v))\n    end\n    return result\nend\n\n",
            i
        ));

        code.push_str(&format!(
            "function filter{}<T>(arr: T[], pred: (T) => boolean): T[]\n    local result = {{}}\n    for _, v in ipairs(arr) do\n        if pred(v) then\n            table.insert(result, v)\n        end\n    end\n    return result\nend\n\n",
            i
        ));

        code.push_str(&format!(
            "function reduce{}<T, U>(arr: T[], init: U, f: (U, T) => U): U\n    local acc = init\n    for _, v in ipairs(arr) do\n        acc = f(acc, v)\n    end\n    return acc\nend\n\n",
            i
        ));
    }

    code.push_str("local nums = {1, 2, 3, 4, 5}\n");
    for i in 0..count {
        code.push_str(&format!(
            "local mapped{} = map{}(nums, function(x: number): number return x * 2 end)\n",
            i, i
        ));
        code.push_str(&format!(
            "local filtered{} = filter{}(nums, function(x: number): boolean return x > 2 end)\n",
            i, i
        ));
        code.push_str(&format!("local sum{} = reduce{}(nums, 0, function(acc: number, x: number): number return acc + x end)\n", i, i));
    }

    code
}

fn generate_generic_method_chains(count: usize) -> String {
    let mut code = String::new();

    for i in 0..count {
        code.push_str(&format!(
            "class Builder{}<T> {{\n    private _value: T\n\n    constructor(value: T)\n        self._value = value\n    end\n\n    with<U>(f: (T) => U): Builder{}<U>\n        return Builder{}<U>(f(self._value))\n    end\n\n    get(): T\n        return self._value\n    end\n\n    transform<U>(f: (T) => U): Builder{}<U>\n        return self:with(f)\n    end\n\n    static create<U>(value: U): Builder{}<U>\n        return Builder{}<U>(value)\n    end\n}}\n\n",
            i, i, i, i, i, i
        ));
    }

    code.push_str("local result = Builder{}:create(42)\n");
    for i in 0..count {
        code.push_str(&format!(
            "    :transform(function(x: number): number return x + {} end)\n",
            i
        ));
    }
    code.push_str("    :get()\n");

    code
}

fn generate_conditional_types(count: usize) -> String {
    let mut code = String::new();

    code.push_str("type A = { a: number }\n");
    code.push_str("type B = { b: string }\n");
    code.push_str("type C = { c: boolean }\n");

    for i in 0..count {
        code.push_str(&format!("type AB{} = A | B\n", i));
        code.push_str(&format!("type ABC{} = AB{} | C\n", i, i));
        code.push_str(&format!("type OnlyA{}<T> = T extends A ? A : never\n", i));
        code.push_str(&format!("type OnlyB{}<T> = T extends B ? B : never\n", i));
        code.push_str(&format!("type NotC{}<T> = T extends C ? never : T\n", i));
    }

    for i in 0..count {
        code.push_str(&format!(
            "local v{}: OnlyA{}<AB{}> = {{ a = 1 }}\n",
            i, i, i
        ));
    }

    code
}

fn benchmark_generic_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_chain");

    for depth in [5, 10, 20, 50] {
        group.bench_with_input(BenchmarkId::new("chain", depth), &depth, |b, &depth| {
            let code = generate_generic_chain(depth);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_generic_instantiation(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_instantiation");

    for count in [5, 10, 20] {
        for depth in [3, 5, 10] {
            group.bench_with_input(
                BenchmarkId::new(format!("{}_containers_{}_depth", count, depth), count),
                &(count, depth),
                |b, &(count, depth)| {
                    let code = generate_generic_instantiation(count, depth);
                    b.iter(|| parse_and_check(black_box(&code)))
                },
            );
        }
    }

    group.finish();
}

fn benchmark_generic_constraints(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_constraints");

    for count in [5, 10, 20, 50] {
        group.bench_with_input(
            BenchmarkId::new("constraints", count),
            &count,
            |b, &count| {
                let code = generate_generic_constraints(count);
                b.iter(|| parse_and_check(black_box(&code)))
            },
        );
    }

    group.finish();
}

fn benchmark_polymorphic_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("polymorphic_functions");

    for count in [5, 10, 20, 50] {
        group.bench_with_input(BenchmarkId::new("poly", count), &count, |b, &count| {
            let code = generate_polymorphic_functions(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_generic_method_chains(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_method_chains");

    for count in [5, 10, 20, 50] {
        group.bench_with_input(BenchmarkId::new("chains", count), &count, |b, &count| {
            let code = generate_generic_method_chains(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_conditional_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("conditional_types");

    for count in [5, 10, 20, 50] {
        group.bench_with_input(
            BenchmarkId::new("conditional", count),
            &count,
            |b, &count| {
                let code = generate_conditional_types(count);
                b.iter(|| parse_and_check(black_box(&code)))
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_generic_chain,
    benchmark_generic_instantiation,
    benchmark_generic_constraints,
    benchmark_polymorphic_functions,
    benchmark_generic_method_chains,
    benchmark_conditional_types,
);

criterion_main!(benches);
