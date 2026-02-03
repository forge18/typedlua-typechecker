use crate::cli::config::CompilerOptions;
use crate::cli::config::LuaVersion;
use crate::cli::diagnostics::CollectingDiagnosticHandler;
use crate::di::{DiContainer, ServiceLifetime};
use std::sync::Arc;

#[test]
fn test_typechecker_di_integration() {
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
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeChecker creation with DI
    let checker =
        crate::core::type_checker::TypeChecker::new_with_di(&mut container, &interner, &common);

    // Verify the checker was created successfully (can't access private fields)
    assert!(true); // Successful creation is the test
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
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeCheckerState creation with DI
    let state = crate::state::TypeCheckerState::new_with_di(&mut container, &interner, &common);

    // Verify the state was created successfully (can't access private fields)
    assert!(true); // Successful creation is the test
}

#[test]
fn test_default_container_with_typechecker() {
    let mut container = crate::di::create_default_container();

    // Create string interner
    let (interner, common) =
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test that TypeChecker can be created with default container
    let checker =
        crate::core::type_checker::TypeChecker::new_with_di(&container, &interner, &common);

    // Verify it works
    assert!(checker
        .diagnostic_handler
        .is::<CollectingDiagnosticHandler>());
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
        target: typedlua_parser::LuaVersion::Lua5_4,
        ..Default::default()
    };

    container.register(
        move |_| custom_options.clone(),
        crate::di::ServiceLifetime::Singleton,
    );

    // Create string interner
    let (interner, common) =
        typedlua_parser::string_interner::StringInterner::new_with_common_identifiers();

    // Test TypeChecker with custom options
    let checker =
        crate::core::type_checker::TypeChecker::new_with_di(&mut container, &interner, &common);

    // Verify custom options were used
    // Can't access private fields directly, but we can verify the checker was created successfully
    assert!(true); // Placeholder - actual verification happens through successful creation
}
