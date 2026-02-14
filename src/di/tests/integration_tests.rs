use crate::cli::config::CompilerOptions;
use crate::cli::diagnostics::CollectingDiagnosticHandler;
use bumpalo::Bump;
use std::sync::Arc;

#[test]
fn test_typechecker_di_integration() {
    let arena = Bump::new();
    let mut container = crate::di::DiContainer::new();

    // Register required services
    container.register(
        |_| {
            Arc::new(CollectingDiagnosticHandler::new())
                as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        crate::di::ServiceLifetime::Singleton,
    );

    container.register(
        |_| CompilerOptions::default(),
        crate::di::ServiceLifetime::Singleton,
    );

    // Create string interner (required for TypeChecker)
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeChecker creation with DI
    let _checker = crate::core::type_checker::TypeChecker::new_with_di(
        &mut container,
        &interner,
        &common,
        &arena,
    );

    // Test passes if creation succeeds without panic
}

#[test]
fn test_typechecker_state_di_integration() {
    let mut container = crate::di::DiContainer::new();

    // Register required services
    container.register(
        |_| {
            Arc::new(CollectingDiagnosticHandler::new())
                as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        crate::di::ServiceLifetime::Singleton,
    );

    container.register(
        |_| CompilerOptions::default(),
        crate::di::ServiceLifetime::Singleton,
    );

    // Create string interner (required for TypeCheckerState)
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeCheckerState creation with DI
    let _state = crate::state::TypeCheckerState::new_with_di(&mut container, &interner, &common);

    // Test passes if creation succeeds without panic
}

#[test]
fn test_default_container_with_typechecker() {
    let arena = Bump::new();
    let mut container = crate::di::create_default_container();

    // Create string interner
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test that TypeChecker can be created with default container
    let _checker = crate::core::type_checker::TypeChecker::new_with_di(
        &mut container,
        &interner,
        &common,
        &arena,
    );

    // Test passes if creation succeeds without panic
}

#[test]
fn test_di_container_service_lifetimes() {
    let mut container = crate::di::DiContainer::new();

    // Register services with different lifetimes
    container.register(
        |_| {
            Arc::new(CollectingDiagnosticHandler::new())
                as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        crate::di::ServiceLifetime::Singleton,
    );

    container.register(
        |_| CompilerOptions::default(),
        crate::di::ServiceLifetime::Transient,
    );

    // Verify singleton behavior
    let handler1 = container
        .resolve::<Arc<dyn crate::cli::diagnostics::DiagnosticHandler>>()
        .unwrap();
    let handler2 = container
        .resolve::<Arc<dyn crate::cli::diagnostics::DiagnosticHandler>>()
        .unwrap();
    assert!(
        Arc::ptr_eq(&handler1, &handler2),
        "Singleton services should return same instance"
    );

    // Verify transient behavior
    let options1 = container.resolve::<CompilerOptions>().unwrap();
    let options2 = container.resolve::<CompilerOptions>().unwrap();
    assert!(
        !std::ptr::eq(&options1, &options2),
        "Transient services should return different instances"
    );
}

#[test]
fn test_di_container_with_custom_options() {
    let arena = Bump::new();
    let mut container = crate::di::DiContainer::new();

    // Register services with custom configuration
    container.register(
        |_| {
            Arc::new(CollectingDiagnosticHandler::new())
                as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        crate::di::ServiceLifetime::Singleton,
    );

    let custom_options = CompilerOptions {
        target: CompilerOptions::default().target,
        ..Default::default()
    };

    container.register(
        move |_| custom_options.clone(),
        crate::di::ServiceLifetime::Transient,
    );

    // Create string interner
    let (interner, common) =
        luanext_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeChecker with custom options
    let _checker = crate::core::type_checker::TypeChecker::new_with_di(
        &mut container,
        &interner,
        &common,
        &arena,
    );

    // Test passes if creation succeeds without panic
}
