use std::path::PathBuf;
use std::sync::Arc;
use typedlua_parser::lexer::Lexer;
use typedlua_parser::parser::Parser;
use typedlua_typechecker::cli::diagnostics::CollectingDiagnosticHandler;
use typedlua_typechecker::incremental::{
    compute_invalidated_decls, CompilationCache, DependencyGraph,
};
use typedlua_typechecker::{DeclarationId, TypeCheckError, TypeChecker};

fn compute_hashes(
    source: &str,
    module_path: PathBuf,
) -> Result<rustc_hash::FxHashMap<String, u64>, TypeCheckError> {
    let handler = Arc::new(CollectingDiagnosticHandler::new());
    let (interner, common) =
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();
    let mut lexer = Lexer::new(source, handler.clone(), &interner);
    let tokens = lexer.tokenize().expect("Lexing failed");
    let mut parser = Parser::new(tokens, handler.clone(), &interner, &common);
    let program = parser.parse().expect("Parsing failed");

    let type_checker = TypeChecker::new(handler, &interner, &common);
    let hashes = type_checker.compute_declaration_hashes(&program, module_path, &interner);

    Ok(hashes)
}

#[test]
fn test_signature_hash_stability() {
    let source = r#"
        function add(a: number, b: number): number
            return a + b
        end

        function multiply(x: number): number
            return x * 2
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes1 =
        compute_hashes(source, module_path.clone()).expect("First hash computation failed");
    let hashes2 =
        compute_hashes(source, module_path.clone()).expect("Second hash computation failed");

    assert_eq!(hashes1.len(), hashes2.len());
    for (name, hash1) in &hashes1 {
        let hash2 = hashes2
            .get(name)
            .expect("Missing declaration in second computation");
        assert_eq!(
            hash1, hash2,
            "Hash should be stable for same source: {}",
            name
        );
    }
}

#[test]
fn test_signature_change_detected() {
    let source_v1 = r#"
        function process(value: number): number
            return value * 2
        end
    "#;

    let source_v2 = r#"
        function process(value: number, extra: number): number
            return value * extra
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    assert_eq!(hashes_v1.len(), hashes_v2.len());

    let hash_v1 = hashes_v1.get("process").expect("Missing process in v1");
    let hash_v2 = hashes_v2.get("process").expect("Missing process in v2");

    assert_ne!(
        hash_v1, hash_v2,
        "Signature change should produce different hash"
    );
}

#[test]
fn test_body_change_preserves_signature_hash() {
    let source_v1 = r#"
        function calculate(x: number): number
            return x + 1
        end
    "#;

    let source_v2 = r#"
        function calculate(x: number): number
            return x * 2 + 1 - x
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    let hash_v1 = hashes_v1.get("calculate").expect("Missing calculate in v1");
    let hash_v2 = hashes_v2.get("calculate").expect("Missing calculate in v2");

    assert_eq!(
        hash_v1, hash_v2,
        "Body-only change should NOT change signature hash"
    );
}

#[test]
fn test_new_declaration_adds_hash() {
    let source_v1 = r#"
        function existing(): number
            return 42
        end
    "#;

    let source_v2 = r#"
        function existing(): number
            return 42
        end

        function newFunction(x: number): number
            return x * 2
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    assert_eq!(hashes_v1.len(), 1);
    assert_eq!(hashes_v2.len(), 2);

    assert!(hashes_v1.contains_key("existing"));
    assert!(hashes_v2.contains_key("existing"));
    assert!(hashes_v2.contains_key("newFunction"));
}

#[test]
fn test_deletion_removes_hash() {
    let source_v1 = r#"
        function keep(): number
            return 1
        end

        function deleteMe(): number
            return 2
        end
    "#;

    let source_v2 = r#"
        function keep(): number
            return 1
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    assert_eq!(hashes_v1.len(), 2);
    assert_eq!(hashes_v2.len(), 1);

    assert!(hashes_v2.contains_key("keep"));
    assert!(!hashes_v2.contains_key("deleteMe"));
}

#[test]
fn test_class_declaration_hash() {
    let source = r#"
        class MyClass<T>
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes = compute_hashes(source, module_path.clone()).expect("Hash computation failed");

    assert!(
        hashes.contains_key("MyClass"),
        "Class declaration should produce hash"
    );
}

#[test]
#[ignore]
fn test_interface_declaration_hash() {
    let source = r#"
        interface MyInterface
            x: number
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes = compute_hashes(source, module_path.clone()).expect("Hash computation failed");

    assert!(
        hashes.contains_key("MyInterface"),
        "Interface declaration should produce hash"
    );
}

#[test]
fn test_type_alias_declaration_hash() {
    let source = r#"
        type MyAlias = number
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes = compute_hashes(source, module_path.clone()).expect("Hash computation failed");

    assert!(
        hashes.contains_key("MyAlias"),
        "Type alias should produce hash"
    );
}

#[test]
fn test_enum_declaration_hash() {
    let source = r#"
        enum Status { Ok = 200, Error = 500 }
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes = compute_hashes(source, module_path.clone()).expect("Hash computation failed");

    assert!(
        hashes.contains_key("Status"),
        "Enum declaration should produce hash"
    );
}

#[test]
fn test_invalidation_signature_change() {
    let mut old_cache = CompilationCache::default();
    let old_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "func".to_string()),
        100,
    )]
    .iter()
    .cloned()
    .collect();
    old_cache.declaration_hashes = old_hashes;

    let new_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "func".to_string()),
        200,
    )]
    .iter()
    .cloned()
    .collect();

    let result = compute_invalidated_decls(&old_cache, &new_hashes, &[]);

    assert!(
        result.cache_dirty,
        "Cache should be dirty when signature changes"
    );
    assert!(
        !result.invalidated_declarations.is_empty(),
        "Should invalidate changed declaration"
    );
}

#[test]
fn test_invalidation_body_only_change() {
    let mut old_cache = CompilationCache::default();
    let old_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "func".to_string()),
        100,
    )]
    .iter()
    .cloned()
    .collect();
    old_cache.declaration_hashes = old_hashes;

    let new_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "func".to_string()),
        100,
    )]
    .iter()
    .cloned()
    .collect();

    let result = compute_invalidated_decls(&old_cache, &new_hashes, &[]);

    assert!(
        !result.cache_dirty,
        "Cache should NOT be dirty for body-only changes"
    );
    assert!(
        result.invalidated_declarations.is_empty(),
        "Should not invalidate anything"
    );
}

#[test]
fn test_invalidation_new_function() {
    let mut old_cache = CompilationCache::default();
    let old_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "existing".to_string()),
        100,
    )]
    .iter()
    .cloned()
    .collect();
    old_cache.declaration_hashes = old_hashes;

    let new_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [
        (
            DeclarationId::new(PathBuf::from("/a.tl"), "existing".to_string()),
            100,
        ),
        (
            DeclarationId::new(PathBuf::from("/a.tl"), "newFunc".to_string()),
            200,
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let result = compute_invalidated_decls(&old_cache, &new_hashes, &[]);

    assert!(
        result.cache_dirty,
        "Cache should be dirty when new functions added"
    );
}

#[test]
fn test_invalidation_deleted_function() {
    let mut old_cache = CompilationCache::default();
    let old_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [
        (
            DeclarationId::new(PathBuf::from("/a.tl"), "keep".to_string()),
            100,
        ),
        (
            DeclarationId::new(PathBuf::from("/a.tl"), "delete".to_string()),
            200,
        ),
    ]
    .iter()
    .cloned()
    .collect();
    old_cache.declaration_hashes = old_hashes;

    let new_hashes: rustc_hash::FxHashMap<DeclarationId, u64> = [(
        DeclarationId::new(PathBuf::from("/a.tl"), "keep".to_string()),
        100,
    )]
    .iter()
    .cloned()
    .collect();

    let deleted = vec![DeclarationId::new(
        PathBuf::from("/a.tl"),
        "delete".to_string(),
    )];
    let result = compute_invalidated_decls(&old_cache, &new_hashes, &deleted);

    assert!(
        result.cache_dirty,
        "Cache should be dirty when functions deleted"
    );
}

#[test]
fn test_dependency_graph_add_dependency() {
    let mut graph = DependencyGraph::new();

    let a = DeclarationId::new(PathBuf::from("a.lua"), "caller".to_string());
    let b = DeclarationId::new(PathBuf::from("b.lua"), "callee".to_string());

    graph.add_dependency(a.clone(), b.clone());

    let a_deps = graph.get_dependencies(&a);
    assert_eq!(a_deps.len(), 1);
    assert_eq!(a_deps[0], b);

    let b_deps = graph.get_dependents(&b);
    assert_eq!(b_deps.len(), 1);
    assert_eq!(b_deps[0], a);
}

#[test]
fn test_dependency_graph_transitive() {
    let mut graph = DependencyGraph::new();

    let main = DeclarationId::new(PathBuf::from("main.lua"), "main".to_string());
    let util = DeclarationId::new(PathBuf::from("util.lua"), "util".to_string());
    let base = DeclarationId::new(PathBuf::from("base.lua"), "base".to_string());

    graph.add_dependency(main.clone(), util.clone());
    graph.add_dependency(util.clone(), base.clone());

    let dependents = graph.get_dependents(&base);
    assert_eq!(dependents.len(), 1);
    assert!(dependents.contains(&util));

    let dependents_of_base = graph.get_dependents(&base);
    let all_dependents: Vec<DeclarationId> = dependents_of_base
        .iter()
        .flat_map(|d| {
            let mut d2 = graph.get_dependents(d);
            d2.push(d.clone());
            d2
        })
        .collect();

    assert!(all_dependents.contains(&util));
    assert!(all_dependents.contains(&main));
}

#[test]
fn test_return_type_change_detected() {
    let source_v1 = r#"
        function getValue(): number
            return 42
        end
    "#;

    let source_v2 = r#"
        function getValue(): string
            return "hello"
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    let hash_v1 = hashes_v1.get("getValue").expect("Missing getValue in v1");
    let hash_v2 = hashes_v2.get("getValue").expect("Missing getValue in v2");

    assert_ne!(
        hash_v1, hash_v2,
        "Return type change should produce different hash"
    );
}

#[test]
fn test_parameter_type_change_detected() {
    let source_v1 = r#"
        function process(x: number)
        end
    "#;

    let source_v2 = r#"
        function process(x: string)
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    let hash_v1 = hashes_v1.get("process").expect("Missing process in v1");
    let hash_v2 = hashes_v2.get("process").expect("Missing process in v2");

    assert_ne!(
        hash_v1, hash_v2,
        "Parameter type change should produce different hash"
    );
}

#[test]
fn test_function_order_independence() {
    let source_v1 = r#"
        function first(): number
            return second()
        end

        function second(): number
            return 42
        end
    "#;

    let source_v2 = r#"
        function second(): number
            return 42
        end

        function first(): number
            return second()
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    assert_eq!(hashes_v1.len(), hashes_v2.len());

    let first_v1 = hashes_v1.get("first").unwrap();
    let first_v2 = hashes_v2.get("first").unwrap();
    assert_eq!(
        first_v1, first_v2,
        "Function hash should be order-independent"
    );

    let second_v1 = hashes_v1.get("second").unwrap();
    let second_v2 = hashes_v2.get("second").unwrap();
    assert_eq!(
        second_v1, second_v2,
        "Function hash should be order-independent"
    );
}

#[test]
fn test_multiple_functions_hash_computation() {
    let source = r#"
        function foo(): number return 1 end
        function bar(): number return 2 end
        function baz(): number return 3 end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes = compute_hashes(source, module_path.clone()).expect("Hash computation failed");

    assert_eq!(hashes.len(), 3);
    assert!(hashes.contains_key("foo"));
    assert!(hashes.contains_key("bar"));
    assert!(hashes.contains_key("baz"));

    let foo_hash = hashes.get("foo").unwrap();
    let bar_hash = hashes.get("bar").unwrap();
    let baz_hash = hashes.get("baz").unwrap();

    assert_ne!(
        foo_hash, bar_hash,
        "Different functions should have different hashes"
    );
    assert_ne!(
        bar_hash, baz_hash,
        "Different functions should have different hashes"
    );
    assert_ne!(
        foo_hash, baz_hash,
        "Different functions should have different hashes"
    );
}

#[test]
fn test_generic_type_parameters_in_signature() {
    let source_v1 = r#"
        function process<T>(x: T): T
            return x
        end
    "#;

    let source_v2 = r#"
        function process<T, U>(x: T, y: U): T
            return x
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    let hash_v1 = hashes_v1.get("process").expect("Missing process in v1");
    let hash_v2 = hashes_v2.get("process").expect("Missing process in v2");

    assert_ne!(
        hash_v1, hash_v2,
        "Adding generic parameter should change hash"
    );
}

#[test]
fn test_constraint_change_detected() {
    let source_v1 = r#"
        function process<T>(x: T): T
            return x
        end
    "#;

    let source_v2 = r#"
        function process<T extends string>(x: T): T
            return x
        end
    "#;

    let module_path = PathBuf::from("/test/module.tl");
    let hashes_v1 = compute_hashes(source_v1, module_path.clone()).expect("v1 hash failed");
    let hashes_v2 = compute_hashes(source_v2, module_path.clone()).expect("v2 hash failed");

    let hash_v1 = hashes_v1.get("process").expect("Missing process in v1");
    let hash_v2 = hashes_v2.get("process").expect("Missing process in v2");

    assert_ne!(hash_v1, hash_v2, "Adding constraint should change hash");
}
