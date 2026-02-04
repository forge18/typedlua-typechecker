use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::Arc;

/// Service lifetime options for dependency injection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServiceLifetime {
    /// Create a new instance every time the service is resolved
    Transient,
    /// Create a single instance that is reused for all resolutions
    Singleton,
}

type FactoryFn = Arc<dyn Fn(&mut DiContainer) -> Box<dyn Any + Send + Sync> + Send + Sync>;

/// Dependency Injection container for managing service lifetimes and resolution
pub struct DiContainer {
    factories: HashMap<TypeId, (FactoryFn, ServiceLifetime)>,
    singletons: HashMap<TypeId, Arc<dyn Any + Send + Sync>>,
}

impl DiContainer {
    /// Create a new empty DI container
    pub fn new() -> Self {
        Self {
            factories: HashMap::new(),
            singletons: HashMap::new(),
        }
    }

    /// Register a service with the container
    ///
    /// # Arguments
    ///
    /// * `factory` - A function that creates the service instance
    /// * `lifetime` - The lifetime management strategy for the service
    ///
    /// # Example
    ///
    /// ```rust
    /// use typedlua_typechecker::di::{DiContainer, ServiceLifetime};
    ///
    /// let mut container = DiContainer::new();
    /// container.register(|_| String::from("Hello"), ServiceLifetime::Singleton);
    /// let greeting = container.resolve::<String>().unwrap();
    /// assert_eq!(greeting, "Hello");
    /// ```
    pub fn register<T: 'static + Send + Sync>(
        &mut self,
        factory: impl Fn(&mut DiContainer) -> T + 'static + Send + Sync,
        lifetime: ServiceLifetime,
    ) {
        let type_id = TypeId::of::<T>();
        self.factories.insert(
            type_id,
            (
                Arc::new(move |container| Box::new(factory(container))),
                lifetime,
            ),
        );
    }

    /// Resolve a service from the container
    ///
    /// # Returns
    ///
    /// `Some(T)` if the service is registered, `None` otherwise
    ///
    /// # Example
    ///
    /// ```rust
    /// use typedlua_typechecker::di::{DiContainer, ServiceLifetime};
    ///
    /// let mut container = DiContainer::new();
    /// container.register(|_| 42i32, ServiceLifetime::Singleton);
    /// let value = container.resolve::<i32>();
    /// assert_eq!(value, Some(42));
    /// ```
    pub fn resolve<T: 'static + Send + Sync + Clone>(&mut self) -> Option<T> {
        let type_id = TypeId::of::<T>();

        // Check singletons first
        if let Some(singleton_arc) = self.singletons.get(&type_id) {
            if let Some(singleton_ref) = singleton_arc.downcast_ref::<T>() {
                return Some(singleton_ref.clone());
            }
            // If downcast fails, remove the invalid entry and continue
            self.singletons.remove(&type_id);
        }

        // Create new instance
        let (factory, lifetime) = {
            let factory_tuple = self.factories.get(&type_id)?;
            (factory_tuple.0.clone(), factory_tuple.1)
        };
        let instance = factory(self);

        // Extract the value for caching
        let result = instance.downcast::<T>().ok().map(|t| (*t).clone());

        // Cache if singleton and we successfully extracted the value
        if matches!(lifetime, ServiceLifetime::Singleton) {
            if let Some(value) = result.as_ref() {
                self.singletons.insert(type_id, Arc::new(value.clone()));
            }
        }

        result
    }

    /// Check if a service is registered
    ///
    /// # Returns
    ///
    /// `true` if the service is registered, `false` otherwise
    pub fn is_registered<T: 'static>(&self) -> bool {
        let type_id = TypeId::of::<T>();
        self.factories.contains_key(&type_id)
    }

    /// Get the number of registered services
    pub fn service_count(&self) -> usize {
        self.factories.len()
    }

    /// Get the number of cached singleton instances
    pub fn singleton_count(&self) -> usize {
        self.singletons.len()
    }
}
