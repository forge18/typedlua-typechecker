//! Module tests demonstrating DI system usage
//!
//! These tests show how to use the DI container with file system
//! and diagnostic components.

use crate::di::{DiContainer, ServiceLifetime};
use crate::test_utils::mocks::{MockDiagnosticHandler, MockFileSystem};
use std::path::Path;
use std::sync::Arc;

#[test]
fn test_file_system_with_di() {
    let mut container = DiContainer::new();

    // Setup mock file system
    container.register(
        |_| {
            let mock_fs = MockFileSystem::new();
            mock_fs.add_file("config.lua", "return { version = '1.0' }");
            mock_fs.add_file("utils.lua", "local function helper() return 42 end");
            Arc::new(mock_fs) as Arc<dyn crate::cli::fs::FileSystem>
        },
        ServiceLifetime::Singleton,
    );

    // Test file operations
    let fs = container
        .resolve::<Arc<dyn crate::cli::fs::FileSystem>>()
        .unwrap();

    // Test reading files
    let config_content = fs.read_file(&Path::new("config.lua")).unwrap();
    assert!(config_content.contains("version"));

    let utils_content = fs.read_file(&Path::new("utils.lua")).unwrap();
    assert!(utils_content.contains("helper"));

    // Test file existence
    assert!(fs.exists(&Path::new("config.lua")));
    assert!(!fs.exists(&Path::new("nonexistent.lua")));

    // Test path resolution
    let resolved = fs.resolve_path(&Path::new("/base"), "sub/dir");
    assert_eq!(resolved, Path::new("/base/sub/dir"));

    // Test writing files
    fs.write_file(&Path::new("new.lua"), "local x = 1").unwrap();
    assert!(fs.exists(&Path::new("new.lua")));
    let new_content = fs.read_file(&Path::new("new.lua")).unwrap();
    assert_eq!(new_content, "local x = 1");
}

#[test]
fn test_diagnostics_with_di() {
    let mut container = DiContainer::new();

    // Setup mock diagnostics
    container.register(
        |_| {
            let mock_diagnostics = MockDiagnosticHandler::new();
            Arc::new(mock_diagnostics) as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>
        },
        ServiceLifetime::Singleton,
    );

    let diagnostics = container
        .resolve::<Arc<dyn crate::cli::diagnostics::DiagnosticHandler>>()
        .unwrap();

    // Initially no diagnostics
    assert_eq!(diagnostics.error_count(), 0);
    assert_eq!(diagnostics.warning_count(), 0);
    assert!(!diagnostics.has_errors());

    // Test diagnostic reporting
    diagnostics.report(crate::cli::diagnostics::Diagnostic::error(
        Default::default(),
        "Test error".to_string(),
    ));

    assert_eq!(diagnostics.error_count(), 1);
    assert!(diagnostics.has_errors());
    assert_eq!(diagnostics.get_diagnostics().len(), 1);
}

#[test]
fn test_integration_file_system_and_diagnostics() {
    let mut container = DiContainer::new();

    // Setup complete mock environment - create mocks first, then wrap in Arc for sharing
    let mut mock_fs = MockFileSystem::new();
    mock_fs.add_file("main.lua", "print('hello')");
    mock_fs.add_file("lib.lua", "local function lib() return true end");

    let mut mock_diagnostics = MockDiagnosticHandler::new();

    let fs_ptr = Arc::new(mock_fs);
    let diagnostics_ptr = Arc::new(mock_diagnostics);

    container.register(
        move |_| fs_ptr.clone() as Arc<dyn crate::cli::fs::FileSystem>,
        ServiceLifetime::Singleton,
    );

    container.register(
        move |_| diagnostics_ptr.clone() as Arc<dyn crate::cli::diagnostics::DiagnosticHandler>,
        ServiceLifetime::Singleton,
    );

    // Verify all services work together
    let fs = container
        .resolve::<Arc<dyn crate::cli::fs::FileSystem>>()
        .unwrap();
    let diagnostics = container
        .resolve::<Arc<dyn crate::cli::diagnostics::DiagnosticHandler>>()
        .unwrap();

    // Test integrated functionality
    assert!(fs.exists(&Path::new("main.lua")));
    assert!(fs.exists(&Path::new("lib.lua")));

    // Read and verify content
    let main_content = fs.read_file(&Path::new("main.lua")).unwrap();
    assert_eq!(main_content, "print('hello')");

    // Test diagnostics
    assert_eq!(diagnostics.error_count(), 0);
    assert_eq!(diagnostics.warning_count(), 0);
    assert!(!diagnostics.has_errors());
}
