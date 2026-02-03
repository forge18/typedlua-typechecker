use crate::di::{DiContainer, DiError, ServiceLifetime};

#[test]
fn test_service_not_found_error() {
    let error = DiError::not_found::<String>();
    assert!(matches!(error, DiError::ServiceNotFound(_)));
    assert!(error.to_string().contains("String"));
}

#[test]
fn test_circular_dependency_error() {
    let error = DiError::circular::<String>();
    assert!(matches!(error, DiError::CircularDependency(_)));
    assert!(error.to_string().contains("String"));
}

#[test]
fn test_construction_failed_error() {
    let error = DiError::construction::<String>("test reason");
    assert!(matches!(error, DiError::ConstructionFailed(_)));
    assert!(error.to_string().contains("String"));
    assert!(error.to_string().contains("test reason"));
}

#[test]
fn test_invalid_registration_error() {
    let error = DiError::invalid("test reason");
    assert!(matches!(error, DiError::InvalidRegistration(_)));
    assert!(error.to_string().contains("test reason"));
}

#[test]
fn test_error_display_formats() {
    let not_found = DiError::not_found::<i32>();
    let circular = DiError::circular::<f64>();
    let construction = DiError::construction::<String>("invalid config");
    let invalid = DiError::invalid("missing trait bound");

    assert!(not_found.to_string().contains("i32"));
    assert!(circular.to_string().contains("f64"));
    assert!(construction.to_string().contains("String"));
    assert!(construction.to_string().contains("invalid config"));
    assert!(invalid.to_string().contains("missing trait bound"));
}

#[test]
fn test_error_equality() {
    let error1 = DiError::not_found::<String>();
    let error2 = DiError::not_found::<String>();
    let error3 = DiError::not_found::<i32>();

    assert_eq!(error1, error2); // Same error type and message
    assert_ne!(error1, error3); // Different service types
}
