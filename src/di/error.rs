use std::fmt;

/// Error type for dependency injection operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiError {
    /// Service not found in container
    ServiceNotFound(String),
    /// Circular dependency detected
    CircularDependency(String),
    /// Service construction failed
    ConstructionFailed(String),
    /// Invalid service registration
    InvalidRegistration(String),
}

impl fmt::Display for DiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DiError::ServiceNotFound(service) => write!(f, "Service not found: {}", service),
            DiError::CircularDependency(service) => {
                write!(f, "Circular dependency detected: {}", service)
            }
            DiError::ConstructionFailed(service) => {
                write!(f, "Failed to construct service: {}", service)
            }
            DiError::InvalidRegistration(reason) => {
                write!(f, "Invalid service registration: {}", reason)
            }
        }
    }
}

impl std::error::Error for DiError {}

impl DiError {
    /// Create a service not found error
    pub fn not_found<T: 'static>() -> Self {
        DiError::ServiceNotFound(std::any::type_name::<T>().to_string())
    }

    /// Create a circular dependency error
    pub fn circular<T: 'static>() -> Self {
        DiError::CircularDependency(std::any::type_name::<T>().to_string())
    }

    /// Create a construction failed error
    pub fn construction<T: 'static>(reason: &str) -> Self {
        DiError::ConstructionFailed(format!("{}: {}", std::any::type_name::<T>(), reason))
    }

    /// Create an invalid registration error
    pub fn invalid(reason: &str) -> Self {
        DiError::InvalidRegistration(reason.to_string())
    }
}
