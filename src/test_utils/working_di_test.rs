//! Working DI tests that demonstrate core functionality
//!
//! These tests show the DI container working with basic types
//! and demonstrate the core DI patterns.

#[test]
fn test_di_container_basic_types() {
    use crate::di::{DiContainer, ServiceLifetime};

    let mut container = DiContainer::new();

    // Register a simple integer service
    container.register(|_| 42i32, ServiceLifetime::Singleton);

    // Register a string service
    container.register(|_| "hello".to_string(), ServiceLifetime::Transient);

    // Test that services are registered
    assert_eq!(container.service_count(), 2);

    // Test singleton resolution
    let value1 = container.resolve::<i32>().unwrap();
    let value2 = container.resolve::<i32>().unwrap();
    assert_eq!(value1, 42);
    assert_eq!(value2, 42);

    // Test transient resolution
    let str1 = container.resolve::<String>().unwrap();
    let str2 = container.resolve::<String>().unwrap();
    assert_eq!(str1, "hello");
    assert_eq!(str2, "hello");
}

#[test]
fn test_di_container_with_complex_types() {
    use crate::di::{DiContainer, ServiceLifetime};

    #[derive(Debug, Clone, PartialEq)]
    struct Config {
        debug: bool,
        timeout: u32,
    }

    let mut container = DiContainer::new();

    // Register a config service
    container.register(
        |_| Config {
            debug: true,
            timeout: 30,
        },
        ServiceLifetime::Singleton,
    );

    // Test resolution
    let config = container.resolve::<Config>().unwrap();
    assert_eq!(config.debug, true);
    assert_eq!(config.timeout, 30);

    // Test singleton caching
    let config2 = container.resolve::<Config>().unwrap();
    assert_eq!(config.debug, config2.debug);
    assert_eq!(config.timeout, config2.timeout);
}

#[test]
fn test_di_container_dependency_injection() {
    use crate::di::{DiContainer, ServiceLifetime};

    #[derive(Debug, Clone)]
    struct DatabaseConfig {
        url: String,
    }

    #[derive(Debug, Clone)]
    struct Service {
        config: DatabaseConfig,
        name: String,
    }

    let mut container = DiContainer::new();

    // Register base dependency
    container.register(
        |_| DatabaseConfig {
            url: "postgres://localhost".to_string(),
        },
        ServiceLifetime::Singleton,
    );

    // Register service that depends on config
    container.register(
        |container| Service {
            config: container.resolve::<DatabaseConfig>().unwrap(),
            name: "test_service".to_string(),
        },
        ServiceLifetime::Transient,
    );

    // Test dependency injection
    let service = container.resolve::<Service>().unwrap();
    assert_eq!(service.config.url, "postgres://localhost");
    assert_eq!(service.name, "test_service");
}

#[test]
fn test_di_container_error_handling() {
    use crate::di::{DiContainer, ServiceLifetime};

    let mut container = DiContainer::new();

    // Test unregistered service returns None
    assert_eq!(container.resolve::<i32>(), None);
    assert!(!container.is_registered::<i32>());

    // Register and test
    container.register(|_| 100i32, ServiceLifetime::Singleton);

    assert_eq!(container.resolve::<i32>(), Some(100));
    assert!(container.is_registered::<i32>());
}
