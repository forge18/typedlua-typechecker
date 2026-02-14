//! Integration tests demonstrating DI system usage
//!
//! These tests show how to use the DI container with real components
//! to create comprehensive, maintainable test scenarios.

use crate::cli::diagnostics::Diagnostic;
use crate::cli::fs::FileSystem;
use crate::di::{DiContainer, ServiceLifetime};
use crate::test_utils::mocks::{MockDiagnosticHandler, MockFileSystem};
use std::path::Path;
use std::sync::Arc;

#[test]
fn test_di_container_with_real_components() {
    let mut container = DiContainer::new();

    // Register mock services that implement real traits
    container.register(
        |_| {
            let mock_fs = MockFileSystem::new();
            mock_fs.add_file("test.lua", "local x = 5");
            Arc::new(mock_fs) as Arc<dyn FileSystem>
        },
        ServiceLifetime::Singleton,
    );

    container.register(
        |_| {
            let mock_diagnostics = MockDiagnosticHandler::new();
            Arc::new(mock_diagnostics) as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        ServiceLifetime::Singleton,
    );

    // Test that we can resolve and use the services
    let fs = container.resolve::<Arc<dyn FileSystem>>().unwrap();
    let diagnostics = container
        .resolve::<Arc<dyn crate::cli::diagnostics::DiagnosticHandler>>()
        .unwrap();

    // Verify file system works
    assert!(fs.exists(Path::new("test.lua")));
    let content = fs.read_file(Path::new("test.lua")).unwrap();
    assert_eq!(content, "local x = 5");

    // Verify diagnostics work
    assert_eq!(diagnostics.error_count(), 0);
    assert!(!diagnostics.has_errors());

    // Test diagnostic reporting
    diagnostics.report(Diagnostic::error(
        Default::default(),
        "Test error".to_string(),
    ));

    assert_eq!(diagnostics.error_count(), 1);
    assert!(diagnostics.has_errors());
    assert_eq!(diagnostics.get_diagnostics().len(), 1);
}

#[test]
fn test_di_singleton_caching() {
    let mut container = DiContainer::new();

    // Register a simple service
    container.register(|_| 42i32, ServiceLifetime::Singleton);

    // Resolve multiple times
    let value1 = container.resolve::<i32>().unwrap();
    let value2 = container.resolve::<i32>().unwrap();

    // Should get same instance (singleton)
    assert_eq!(value1, 42);
    assert_eq!(value2, 42);
    assert_eq!(container.singleton_count(), 1);
}

#[test]
fn test_di_transient_services() {
    let mut container = DiContainer::new();

    // Register a transient service using a counter to ensure different instances
    let counter = std::sync::atomic::AtomicUsize::new(0);
    container.register(
        move |_| counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst),
        ServiceLifetime::Transient,
    );

    // Resolve multiple times
    let id1 = container.resolve::<usize>().unwrap();
    let id2 = container.resolve::<usize>().unwrap();

    // Should get different instances (transient)
    assert_ne!(id1, id2);
    assert_eq!(container.singleton_count(), 0);
}

#[test]
fn test_di_container_service_management() {
    let mut container = DiContainer::new();

    // Initially no services registered
    assert_eq!(container.service_count(), 0);
    assert_eq!(container.singleton_count(), 0);

    // Register services - use different types to avoid replacement
    container.register(|_| "service1", ServiceLifetime::Singleton);

    container.register(|_| 42i32, ServiceLifetime::Transient);

    // Verify registration
    assert_eq!(container.service_count(), 2);
    assert_eq!(container.singleton_count(), 0); // Not cached until resolved

    // Resolve services
    let s1 = container.resolve::<&str>().unwrap();
    assert_eq!(s1, "service1");
    assert_eq!(container.singleton_count(), 1); // Now cached

    let s2 = container.resolve::<i32>().unwrap();
    assert_eq!(s2, 42);
    assert_eq!(container.singleton_count(), 1); // Transient not cached
}
