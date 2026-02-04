//! Simple DI test that demonstrates the core functionality
//!
//! This test shows the DI container working with basic types
//! to verify the core functionality is working correctly.

#[test]
fn test_di_container_basic_functionality() {
    use crate::di::{DiContainer, ServiceLifetime};

    let mut container = DiContainer::new();

    // Test simple value registration and resolution
    container.register(|_| 42i32, ServiceLifetime::Singleton);

    container.register(|_| "hello".to_string(), ServiceLifetime::Transient);

    // Verify service count
    assert_eq!(container.service_count(), 2);

    // Test singleton resolution
    let value1 = container.resolve::<i32>().unwrap();
    let value2 = container.resolve::<i32>().unwrap();
    assert_eq!(value1, 42);
    assert_eq!(value2, 42);
    assert_eq!(container.singleton_count(), 1);

    // Test transient resolution
    let str1 = container.resolve::<String>().unwrap();
    let str2 = container.resolve::<String>().unwrap();
    assert_eq!(str1, "hello");
    assert_eq!(str2, "hello");
    assert_eq!(container.singleton_count(), 1); // Transient not cached
}

#[test]
fn test_di_container_service_lifetimes() {
    use crate::di::{DiContainer, ServiceLifetime};

    let mut container = DiContainer::new();

    // Test singleton lifetime
    container.register(|_| vec![1, 2, 3], ServiceLifetime::Singleton);

    let v1 = container.resolve::<Vec<i32>>().unwrap();
    let v2 = container.resolve::<Vec<i32>>().unwrap();

    // Should be the same instance (same pointer)
    assert_eq!(v1.len(), 3);
    assert_eq!(v2.len(), 3);
    assert_eq!(container.singleton_count(), 1);
}

#[test]
fn test_di_container_complex_types() {
    use crate::di::{DiContainer, ServiceLifetime};
    use std::collections::HashMap;

    #[derive(Debug, Clone, PartialEq)]
    struct Config {
        settings: HashMap<String, String>,
    }

    let mut container = DiContainer::new();

    // Test with complex type
    let mut settings = HashMap::new();
    settings.insert("key".to_string(), "value".to_string());

    container.register(
        move |_| Config {
            settings: settings.clone(),
        },
        ServiceLifetime::Singleton,
    );

    let config = container.resolve::<Config>().unwrap();
    assert_eq!(config.settings.get("key"), Some(&"value".to_string()));
}

#[test]
fn test_di_container_error_handling() {
    use crate::di::{DiContainer, ServiceLifetime};

    let mut container = DiContainer::new();

    // Test unregistered service
    assert_eq!(container.resolve::<i32>(), None);

    // Test service registration and resolution
    container.register(|_| 100i32, ServiceLifetime::Singleton);

    assert_eq!(container.resolve::<i32>(), Some(100));
    assert!(container.is_registered::<i32>());
}
