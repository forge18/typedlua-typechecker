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

type FactoryFn = Box<dyn Fn(&mut DiContainer) -> Box<dyn Any + Send + Sync> + Send + Sync>;

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
    /// container.register(|_| MyService::new(), ServiceLifetime::Singleton);
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
                Box::new(move |container| Box::new(factory(container))),
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
    /// let service = container.resolve::<MyService>();
    /// ```
    pub fn resolve<T: 'static + Send + Sync + Clone>(&mut self) -> Option<T> {
        let type_id = TypeId::of::<T>();

        // Check singletons first
        if let Some(singleton) = self.singletons.get(&type_id) {
            return singleton.downcast_ref::<T>().cloned();
        }

        // Create new instance
        let factory_tuple = self.factories.get(&type_id)?;
        let instance = (factory_tuple.0)(self);
        let lifetime = factory_tuple.1;

        // Cache if singleton
        if matches!(lifetime, ServiceLifetime::Singleton) {
            let arc_instance = Arc::new(instance);
            self.singletons.insert(type_id, arc_instance.clone());
            return arc_instance.downcast_ref::<T>().cloned();
        }

        instance.downcast::<T>().ok().map(|t| (*t).clone())
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
