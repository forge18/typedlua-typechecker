use bumpalo::Bump;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use luanext_parser::{Lexer, Parser, StringInterner};
use std::sync::Arc;

use luanext_typechecker::{cli::diagnostics::CollectingDiagnosticHandler, TypeChecker};

fn parse_and_check(code: &str) {
    let arena = Bump::new();
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) = StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(code, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common, &arena);
    let program = parser.parse().expect("Parsing failed");
    let mut checker = TypeChecker::new(handler.clone(), &interner, &common, &arena)
        .with_stdlib()
        .unwrap();
    checker.check_program(&program).unwrap();
    black_box(());
}

fn generate_synthetic_exprs(count: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!("local x{}: number = 1 + 2 * 3\n", i));
        code.push_str(&format!(
            "local y{}: string = \"test\" .. tostring({})\n",
            i, i
        ));
        code.push_str(&format!(
            "local z{}: boolean = x{} and y{} ~= nil\n",
            i, i, i
        ));
    }
    code
}

fn generate_synthetic_types(depth: usize) -> String {
    let mut code = String::from("type Alias1 = number\n");
    for i in 2..=depth {
        code.push_str(&format!("type Alias{} = Alias{} | nil\n", i, i - 1));
    }
    for i in 1..=depth {
        code.push_str(&format!("local v{}: Alias{} = nil\n", i, depth));
    }
    code
}

fn generate_many_variables(count: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!(
            "local v{}: number | string | boolean | nil = nil\n",
            i
        ));
    }
    code
}

fn generate_nested_functions(depth: usize) -> String {
    let mut code = String::new();
    for i in 0..depth {
        code.push_str(&format!("local f{} = function():\n", i));
    }
    code.push_str("return 1\n");
    for _ in 0..depth {
        code.push_str("end\n");
    }
    code
}

fn generate_generic_functions(count: usize, depth: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!(
            "function identity{}<T>(value: T): T return value end\n",
            i
        ));
    }
    for _ in 0..depth {
        code.push_str("identity0(identity0(identity0(1)))\n");
    }
    code
}

fn generate_method_calls(count: usize) -> String {
    let mut code = String::from("local obj = {\n");
    for i in 0..count {
        code.push_str(&format!("    m{} = function(self): return {} end,\n", i, i));
    }
    code.push_str("}\n");
    for i in 0..count {
        code.push_str(&format!("obj:m{}()\n", i));
    }
    code
}

fn generate_union_types(count: usize) -> String {
    let mut code = String::new();
    let types = ["number", "string", "boolean", "nil", "table", "function"];
    for i in 0..count {
        let mut union = String::new();
        for t in &types[..((i % 6) + 1)] {
            if !union.is_empty() {
                union.push_str(" | ");
            }
            union.push_str(t);
        }
        code.push_str(&format!("local v{}: {} = nil\n", i, union));
    }
    code
}

fn generate_table_literals(count: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!(
            "local t{} = {{ x = {}, y = {}, name = \"test\" }}\n",
            i,
            i,
            i * 2
        ));
    }
    for i in 0..count {
        code.push_str(&format!("local a{} = t{}.x + t{}.y\n", i, i, i));
    }
    code
}

fn generate_interface_heavy(count: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!(
            "interface Point{} {{ x: number, y: number, label?: string }}\n",
            i
        ));
        code.push_str(&format!(
            "function getPoint{}(): Point{} return {{ x = 1, y = 2 }} end\n",
            i, i
        ));
    }
    for i in 0..count {
        code.push_str(&format!("local p{} = getPoint{}()\n", i, i));
    }
    code
}

fn generate_class_heavy(count: usize) -> String {
    let mut code = String::new();
    for i in 0..count {
        code.push_str(&format!(
            "class Animal{} {{\n    name: string\n    constructor(name: string) self.name = name end\n    speak(): string return \"\" end\n}}\n",
            i
        ));
        code.push_str(&format!(
            "class Dog{} extends Animal{} {{\n    breed: string\n    constructor(name: string, breed: string) super(name) self.breed = breed end\n    override speak(): string return self.name .. \" barks\" end\n}}\n",
            i, i
        ));
        code.push_str(&format!("local d{} = Dog{}(\"rex\", \"labrador\")\n", i, i));
        code.push_str(&format!("d{}:speak()\n", i));
    }
    code
}

fn benchmark_synthetic_exprs(c: &mut Criterion) {
    let mut group = c.benchmark_group("synthetic_expressions");

    for count in [100, 500, 1000, 5000] {
        group.bench_with_input(BenchmarkId::new("exprs", count), &count, |b, &count| {
            let code = generate_synthetic_exprs(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_synthetic_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("synthetic_types");

    for depth in [5, 10, 20, 50] {
        group.bench_with_input(BenchmarkId::new("types", depth), &depth, |b, &depth| {
            let code = generate_synthetic_types(depth);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_many_variables(c: &mut Criterion) {
    let mut group = c.benchmark_group("many_variables");

    for count in [100, 500, 1000, 5000] {
        group.bench_with_input(BenchmarkId::new("vars", count), &count, |b, &count| {
            let code = generate_many_variables(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_nested_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("nested_functions");

    for depth in [5, 10, 20, 50, 100] {
        group.bench_with_input(BenchmarkId::new("nested", depth), &depth, |b, &depth| {
            let code = generate_nested_functions(depth);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_generic_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_functions");

    for count in [10, 50, 100, 500] {
        group.bench_with_input(BenchmarkId::new("generics", count), &count, |b, &count| {
            let code = generate_generic_functions(count, 3);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_method_calls(c: &mut Criterion) {
    let mut group = c.benchmark_group("method_calls");

    for count in [10, 50, 100, 500, 1000] {
        group.bench_with_input(BenchmarkId::new("methods", count), &count, |b, &count| {
            let code = generate_method_calls(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_union_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("union_types");

    for count in [100, 500, 1000, 5000] {
        group.bench_with_input(BenchmarkId::new("unions", count), &count, |b, &count| {
            let code = generate_union_types(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_table_literals(c: &mut Criterion) {
    let mut group = c.benchmark_group("table_literals");

    for count in [100, 500, 1000, 5000] {
        group.bench_with_input(BenchmarkId::new("tables", count), &count, |b, &count| {
            let code = generate_table_literals(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

fn benchmark_interface_heavy(c: &mut Criterion) {
    let mut group = c.benchmark_group("interface_heavy");

    for count in [10, 50, 100, 500] {
        group.bench_with_input(
            BenchmarkId::new("interfaces", count),
            &count,
            |b, &count| {
                let code = generate_interface_heavy(count);
                b.iter(|| parse_and_check(black_box(&code)))
            },
        );
    }

    group.finish();
}

fn benchmark_class_heavy(c: &mut Criterion) {
    let mut group = c.benchmark_group("class_heavy");

    for count in [10, 50, 100, 200] {
        group.bench_with_input(BenchmarkId::new("classes", count), &count, |b, &count| {
            let code = generate_class_heavy(count);
            b.iter(|| parse_and_check(black_box(&code)))
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_synthetic_exprs,
    benchmark_synthetic_types,
    benchmark_many_variables,
    benchmark_nested_functions,
    benchmark_generic_functions,
    benchmark_method_calls,
    benchmark_union_types,
    benchmark_table_literals,
    benchmark_interface_heavy,
    benchmark_class_heavy,
);

criterion_main!(benches);
