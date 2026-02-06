use rustc_hash::FxHashMap;
use std::sync::Arc;
use typedlua_parser::ast::statement::{ConstructorParameter, TypeParameter};
use typedlua_parser::ast::types::{PrimitiveType, Type, TypeKind};
use typedlua_parser::span::Span;

/// A generic type alias with type parameters
#[derive(Debug, Clone)]
pub struct GenericTypeAlias<'arena> {
    pub type_parameters: Vec<TypeParameter<'arena>>,
    pub typ: Type<'arena>,
}

/// Cache key for utility types
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct UtilityTypeCacheKey {
    name: String,
    type_args_hash: u64,
}

/// Cache key for generic type instantiation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GenericInstantiationCacheKey {
    name: String,
    type_args_hash: u64,
}

/// Type environment managing type aliases and interfaces
#[derive(Debug)]
pub struct TypeEnvironment<'arena> {
    /// Type aliases (type Foo = ...)
    type_aliases: FxHashMap<String, Type<'arena>>,
    /// Generic type aliases (type Foo<T> = ...)
    generic_type_aliases: FxHashMap<String, GenericTypeAlias<'arena>>,
    /// Interface types
    interfaces: FxHashMap<String, Type<'arena>>,
    /// Built-in types
    builtins: FxHashMap<String, Type<'arena>>,
    /// Currently resolving types (for cycle detection)
    resolving: std::cell::RefCell<std::collections::HashSet<String>>,
    /// Type parameter constraints (T -> constraint type)
    type_param_constraints: FxHashMap<String, Type<'arena>>,
    /// Class implements relationships (class name -> list of implemented interface types)
    class_implements: FxHashMap<String, Vec<Type<'arena>>>,
    /// Abstract classes (class name -> is_abstract)
    abstract_classes: FxHashMap<String, bool>,
    /// Class primary constructors (class name -> constructor parameters)
    class_constructors: FxHashMap<String, Vec<ConstructorParameter<'arena>>>,
    /// Interface type parameter names (interface name -> ordered parameter names)
    interface_type_params: FxHashMap<String, Vec<String>>,
    /// Cached primitive types (singletons)
    primitive_nil: Arc<Type<'arena>>,
    primitive_boolean: Arc<Type<'arena>>,
    primitive_number: Arc<Type<'arena>>,
    primitive_integer: Arc<Type<'arena>>,
    primitive_string: Arc<Type<'arena>>,
    primitive_unknown: Arc<Type<'arena>>,
    primitive_never: Arc<Type<'arena>>,
    primitive_void: Arc<Type<'arena>>,
    primitive_table: Arc<Type<'arena>>,
    primitive_coroutine: Arc<Type<'arena>>,
    /// Cache for utility type resolutions (Pick, Omit, Keyof, etc.)
    utility_type_cache: std::cell::RefCell<FxHashMap<UtilityTypeCacheKey, Type<'arena>>>,
    /// Cache for generic type instantiations
    generic_instantiation_cache: std::cell::RefCell<FxHashMap<GenericInstantiationCacheKey, Type<'arena>>>,
}

impl<'arena> TypeEnvironment<'arena> {
    pub fn new() -> Self {
        let span = Span::new(0, 0, 0, 0);

        let primitive_nil = Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Nil), span));
        let primitive_boolean =
            Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Boolean), span));
        let primitive_number =
            Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Number), span));
        let primitive_integer =
            Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Integer), span));
        let primitive_string =
            Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::String), span));
        let primitive_unknown =
            Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span));
        let primitive_never = Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Never), span));
        let primitive_void = Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Void), span));
        let primitive_table = Arc::new(Type::new(TypeKind::Primitive(PrimitiveType::Table), span));
        let primitive_coroutine = Arc::new(Type::new(
            TypeKind::Primitive(PrimitiveType::Coroutine),
            span,
        ));

        let mut env = Self {
            type_aliases: FxHashMap::with_capacity_and_hasher(64, Default::default()),
            generic_type_aliases: FxHashMap::with_capacity_and_hasher(32, Default::default()),
            interfaces: FxHashMap::with_capacity_and_hasher(64, Default::default()),
            builtins: FxHashMap::with_capacity_and_hasher(16, Default::default()),
            resolving: std::cell::RefCell::new(std::collections::HashSet::new()),
            type_param_constraints: FxHashMap::with_capacity_and_hasher(32, Default::default()),
            class_implements: FxHashMap::with_capacity_and_hasher(32, Default::default()),
            abstract_classes: FxHashMap::with_capacity_and_hasher(16, Default::default()),
            class_constructors: FxHashMap::with_capacity_and_hasher(32, Default::default()),
            interface_type_params: FxHashMap::with_capacity_and_hasher(16, Default::default()),
            primitive_nil,
            primitive_boolean,
            primitive_number,
            primitive_integer,
            primitive_string,
            primitive_unknown,
            primitive_never,
            primitive_void,
            primitive_table,
            primitive_coroutine,
            utility_type_cache: std::cell::RefCell::new(FxHashMap::with_capacity_and_hasher(
                64,
                Default::default(),
            )),
            generic_instantiation_cache: std::cell::RefCell::new(
                FxHashMap::with_capacity_and_hasher(64, Default::default()),
            ),
        };

        env.register_builtins();
        env
    }

    /// Register built-in types using cached primitives
    fn register_builtins(&mut self) {
        self.builtins
            .insert("nil".to_string(), (*self.primitive_nil).clone());
        self.builtins
            .insert("boolean".to_string(), (*self.primitive_boolean).clone());
        self.builtins
            .insert("number".to_string(), (*self.primitive_number).clone());
        self.builtins
            .insert("integer".to_string(), (*self.primitive_integer).clone());
        self.builtins
            .insert("string".to_string(), (*self.primitive_string).clone());
        self.builtins
            .insert("unknown".to_string(), (*self.primitive_unknown).clone());
        self.builtins
            .insert("never".to_string(), (*self.primitive_never).clone());
        self.builtins
            .insert("void".to_string(), (*self.primitive_void).clone());
        self.builtins
            .insert("table".to_string(), (*self.primitive_table).clone());
        self.builtins
            .insert("coroutine".to_string(), (*self.primitive_coroutine).clone());
    }

    /// Register a type alias
    pub fn register_type_alias(&mut self, name: String, typ: Type<'arena>) -> Result<(), String> {
        if self.type_aliases.contains_key(&name) {
            return Err(format!("Type alias '{}' already defined", name));
        }
        self.type_aliases.insert(name, typ);
        Ok(())
    }

    /// Remove a type alias (used for cleaning up scoped type parameters)
    pub fn remove_type_alias(&mut self, name: &str) {
        self.type_aliases.remove(name);
    }

    /// Register a generic type alias
    pub fn register_generic_type_alias(
        &mut self,
        name: String,
        type_parameters: Vec<TypeParameter<'arena>>,
        typ: Type<'arena>,
    ) -> Result<(), String> {
        if self.generic_type_aliases.contains_key(&name) {
            return Err(format!("Generic type alias '{}' already defined", name));
        }
        self.generic_type_aliases.insert(
            name,
            GenericTypeAlias {
                type_parameters,
                typ,
            },
        );
        Ok(())
    }

    /// Register an interface
    pub fn register_interface(&mut self, name: String, typ: Type<'arena>) -> Result<(), String> {
        if self.interfaces.contains_key(&name) {
            return Err(format!("Interface '{}' already defined", name));
        }
        self.interfaces.insert(name.clone(), typ);
        Ok(())
    }

    /// Register the type parameter names for a generic interface.
    pub fn register_interface_type_params(&mut self, name: String, params: Vec<String>) {
        self.interface_type_params.insert(name, params);
    }

    /// Get the type parameter names for a generic interface.
    pub fn get_interface_type_params(&self, name: &str) -> Option<&Vec<String>> {
        self.interface_type_params.get(name)
    }

    /// Look up a type by name (checks type aliases, interfaces, and builtins)
    pub fn lookup_type(&self, name: &str) -> Option<&Type<'arena>> {
        self.type_aliases
            .get(name)
            .or_else(|| self.interfaces.get(name))
            .or_else(|| self.builtins.get(name))
    }

    /// Look up a type alias
    pub fn lookup_type_alias(&self, name: &str) -> Option<&Type<'arena>> {
        self.type_aliases.get(name)
    }

    /// Look up an interface
    pub fn lookup_interface(&self, name: &str) -> Option<&Type<'arena>> {
        self.interfaces.get(name)
    }

    /// Get an interface (alias for lookup_interface)
    pub fn get_interface(&self, name: &str) -> Option<&Type<'arena>> {
        self.lookup_interface(name)
    }

    /// Fast access to primitive type singletons
    pub fn type_nil(&self) -> &Arc<Type<'arena>> {
        &self.primitive_nil
    }

    pub fn type_boolean(&self) -> &Arc<Type<'arena>> {
        &self.primitive_boolean
    }

    pub fn type_number(&self) -> &Arc<Type<'arena>> {
        &self.primitive_number
    }

    pub fn type_integer(&self) -> &Arc<Type<'arena>> {
        &self.primitive_integer
    }

    pub fn type_string(&self) -> &Arc<Type<'arena>> {
        &self.primitive_string
    }

    pub fn type_unknown(&self) -> &Arc<Type<'arena>> {
        &self.primitive_unknown
    }

    pub fn type_never(&self) -> &Arc<Type<'arena>> {
        &self.primitive_never
    }

    pub fn type_void(&self) -> &Arc<Type<'arena>> {
        &self.primitive_void
    }

    pub fn type_table(&self) -> &Arc<Type<'arena>> {
        &self.primitive_table
    }

    pub fn type_coroutine(&self) -> &Arc<Type<'arena>> {
        &self.primitive_coroutine
    }

    /// Create a primitive type using cached instance (avoids allocation for primitives)
    pub fn new_primitive_type(&self, prim: PrimitiveType, span: Span) -> Type<'arena> {
        Type::new(TypeKind::Primitive(prim), span)
    }

    /// Get number type (clones Arc for backward compatibility)
    pub fn get_number_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_number).clone()
    }

    /// Get string type (clones Arc for backward compatibility)
    pub fn get_string_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_string).clone()
    }

    /// Get boolean type (clones Arc for backward compatibility)
    pub fn get_boolean_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_boolean).clone()
    }

    /// Get unknown type (clones Arc for backward compatibility)
    pub fn get_unknown_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_unknown).clone()
    }

    /// Get void type (clones Arc for backward compatibility)
    pub fn get_void_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_void).clone()
    }

    /// Get nil type (clones Arc for backward compatibility)
    pub fn get_nil_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_nil).clone()
    }

    /// Get integer type (clones Arc for backward compatibility)
    pub fn get_integer_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_integer).clone()
    }

    /// Get never type (clones Arc for backward compatibility)
    pub fn get_never_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_never).clone()
    }

    /// Get table type (clones Arc for backward compatibility)
    pub fn get_table_type(&self, _span: Span) -> Type<'arena> {
        (*self.primitive_table).clone()
    }

    /// Check if a type name is defined
    pub fn is_type_defined(&self, name: &str) -> bool {
        self.lookup_type(name).is_some()
    }

    /// Register a type parameter constraint (e.g., T extends/implements Identifiable)
    pub fn register_type_param_constraint(&mut self, name: String, constraint: Type<'arena>) {
        self.type_param_constraints.insert(name, constraint);
    }

    /// Remove a type parameter constraint
    pub fn remove_type_param_constraint(&mut self, name: &str) {
        self.type_param_constraints.remove(name);
    }

    /// Get the constraint for a type parameter
    pub fn get_type_param_constraint(&self, name: &str) -> Option<&Type<'arena>> {
        self.type_param_constraints.get(name)
    }

    /// Register that a class implements one or more interfaces
    pub fn register_class_implements(&mut self, class_name: String, interfaces: Vec<Type<'arena>>) {
        self.class_implements.insert(class_name, interfaces);
    }

    /// Get the interfaces a class implements
    pub fn get_class_implements(&self, class_name: &str) -> Option<&Vec<Type<'arena>>> {
        self.class_implements.get(class_name)
    }

    /// Register a class as abstract
    pub fn register_abstract_class(&mut self, class_name: String) {
        self.abstract_classes.insert(class_name, true);
    }

    /// Check if a class is abstract
    pub fn is_abstract_class(&self, class_name: &str) -> bool {
        self.abstract_classes
            .get(class_name)
            .copied()
            .unwrap_or(false)
    }

    /// Register a class's primary constructor parameters
    pub fn register_class_constructor(
        &mut self,
        class_name: String,
        params: Vec<ConstructorParameter<'arena>>,
    ) {
        self.class_constructors.insert(class_name, params);
    }

    /// Get a class's primary constructor parameters
    pub fn get_class_constructor(&self, class_name: &str) -> Option<&Vec<ConstructorParameter<'arena>>> {
        self.class_constructors.get(class_name)
    }

    /// Resolve a type reference, detecting cycles
    pub fn resolve_type_reference(&self, name: &str) -> Result<Option<Type<'arena>>, String> {
        // Check if we're already resolving this type (cycle detection)
        if self.resolving.borrow().contains(name) {
            return Err(format!("Recursive type alias '{}' detected", name));
        }

        // Mark as resolving
        self.resolving.borrow_mut().insert(name.to_string());

        // Look up the type
        let result = self.lookup_type(name).cloned();

        // Unmark
        self.resolving.borrow_mut().remove(name);

        Ok(result)
    }

    /// Get a generic type alias
    pub fn get_generic_type_alias(&self, name: &str) -> Option<&GenericTypeAlias<'arena>> {
        self.generic_type_aliases.get(name)
    }

    /// Instantiate a generic type alias with the given type arguments, with caching
    pub fn instantiate_generic_type(
        &self,
        name: &str,
        type_args: &[Type<'arena>],
        _span: Span,
    ) -> Result<Type<'arena>, String> {
        let cache_key = GenericInstantiationCacheKey {
            name: name.to_string(),
            type_args_hash: Self::compute_type_args_fingerprint(type_args),
        };

        let mut cache = self.generic_instantiation_cache.borrow_mut();
        if let Some(cached) = cache.get(&cache_key) {
            return Ok(cached.clone());
        }

        let generic_alias = self
            .generic_type_aliases
            .get(name)
            .ok_or_else(|| format!("Generic type '{}' not found", name))?;

        let instantiated = crate::types::generics::instantiate_type(
            &generic_alias.typ,
            &generic_alias.type_parameters,
            type_args,
        )?;

        cache.insert(cache_key, instantiated.clone());
        Ok(instantiated)
    }

    /// Check if a name is a built-in utility type
    pub fn is_utility_type(name: &str) -> bool {
        matches!(
            name,
            "Partial"
                | "Required"
                | "Readonly"
                | "Record"
                | "Pick"
                | "Omit"
                | "Exclude"
                | "Extract"
                | "NonNilable"
                | "Nilable"
                | "ReturnType"
                | "Parameters"
        )
    }

    fn compute_type_args_fingerprint(type_args: &[Type<'arena>]) -> u64 {
        let mut hash = 0u64;
        for typ in type_args {
            hash = hash.wrapping_mul(31);
            hash ^= Self::type_fingerprint(typ);
        }
        hash
    }

    fn type_fingerprint(typ: &Type<'arena>) -> u64 {
        let kind_hash = match &typ.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::Nil => 1,
                PrimitiveType::Boolean => 2,
                PrimitiveType::Number => 3,
                PrimitiveType::Integer => 4,
                PrimitiveType::String => 5,
                PrimitiveType::Unknown => 6,
                PrimitiveType::Never => 7,
                PrimitiveType::Void => 8,
                PrimitiveType::Table => 9,
                PrimitiveType::Coroutine => 10,
                PrimitiveType::Thread => 11,
            },
            TypeKind::Object(obj) => 100u64.wrapping_add(obj.members.len() as u64),
            TypeKind::Array(elem) => 200u64
                .wrapping_mul(31)
                .wrapping_add(Self::type_fingerprint(elem)),
            TypeKind::Function(_) => 300,
            TypeKind::Union(types) => {
                let mut h = 400u64;
                for t in types.iter() {
                    h = h.wrapping_mul(31).wrapping_add(Self::type_fingerprint(t));
                }
                h
            }
            TypeKind::Intersection(types) => {
                let mut h = 500u64;
                for t in types.iter() {
                    h = h.wrapping_mul(31).wrapping_add(Self::type_fingerprint(t));
                }
                h
            }
            TypeKind::Reference(_type_ref) => 600,
            TypeKind::KeyOf(_) => 700,
            TypeKind::Mapped(_) => 800,
            TypeKind::Conditional(_) => 900,
            TypeKind::TemplateLiteral(_) => 1000,
            TypeKind::TypeQuery(_) => 1100,
            TypeKind::Tuple(types) => {
                let mut h = 1200u64;
                for t in types.iter() {
                    h = h.wrapping_mul(31).wrapping_add(Self::type_fingerprint(t));
                }
                h
            }
            TypeKind::Variadic(inner) => 1300u64
                .wrapping_mul(31)
                .wrapping_add(Self::type_fingerprint(inner)),
            TypeKind::Nullable(inner) => 1400u64
                .wrapping_mul(31)
                .wrapping_add(Self::type_fingerprint(inner)),
            TypeKind::Namespace(path) => {
                let mut h = 1500u64;
                for part in path {
                    for c in part.chars() {
                        h = h.wrapping_mul(31).wrapping_add(c as u64);
                    }
                }
                h
            }
            _ => 9999,
        };
        kind_hash.wrapping_add(typ.span.start as u64)
    }

    /// Resolve a utility type with caching
    pub fn resolve_utility_type(
        &self,
        name: &str,
        type_args: &[Type<'arena>],
        span: Span,
        interner: &typedlua_parser::string_interner::StringInterner,
        common_ids: &typedlua_parser::string_interner::CommonIdentifiers,
    ) -> Result<Type<'arena>, String> {
        let cache_key = UtilityTypeCacheKey {
            name: name.to_string(),
            type_args_hash: Self::compute_type_args_fingerprint(type_args),
        };

        let mut cache = self.utility_type_cache.borrow_mut();
        if let Some(cached) = cache.get(&cache_key) {
            return Ok(cached.clone());
        }

        use crate::types::utility_types::apply_utility_type;
        let result = apply_utility_type(name, type_args, span, interner, common_ids)?;

        cache.insert(cache_key, result.clone());
        Ok(result)
    }
}

impl<'arena> Default for TypeEnvironment<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builtins_registered() {
        let env = TypeEnvironment::new();

        assert!(env.lookup_type("number").is_some());
        assert!(env.lookup_type("string").is_some());
        assert!(env.lookup_type("boolean").is_some());
        assert!(env.lookup_type("nil").is_some());
        assert!(env.lookup_type("unknown").is_some());
        assert!(env.lookup_type("never").is_some());
        assert!(env.lookup_type("void").is_some());
    }

    #[test]
    fn test_register_type_alias() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );

        env.register_type_alias("MyNumber".to_string(), typ)
            .unwrap();

        assert!(env.lookup_type("MyNumber").is_some());
        assert!(env.lookup_type_alias("MyNumber").is_some());
    }

    #[test]
    fn test_register_interface() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Table),
            Span::new(0, 0, 0, 0),
        );

        env.register_interface("MyInterface".to_string(), typ)
            .unwrap();

        assert!(env.lookup_type("MyInterface").is_some());
        assert!(env.lookup_interface("MyInterface").is_some());
    }

    #[test]
    fn test_duplicate_type_alias() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );

        env.register_type_alias("Foo".to_string(), typ.clone())
            .unwrap();
        assert!(env.register_type_alias("Foo".to_string(), typ).is_err());
    }

    #[test]
    fn test_all_builtins_registered() {
        let env = TypeEnvironment::new();

        let builtins = vec![
            "nil",
            "boolean",
            "number",
            "integer",
            "string",
            "unknown",
            "never",
            "void",
            "table",
            "coroutine",
        ];

        for builtin in &builtins {
            assert!(
                env.lookup_type(builtin).is_some(),
                "Builtin type '{}' should be registered",
                builtin
            );
        }
    }

    #[test]
    fn test_is_type_defined() {
        let mut env = TypeEnvironment::new();

        // Builtins should be defined
        assert!(env.is_type_defined("number"));
        assert!(env.is_type_defined("string"));

        // Custom types should not be defined initially
        assert!(!env.is_type_defined("MyType"));

        // Register custom type
        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );
        env.register_type_alias("MyType".to_string(), typ).unwrap();

        // Now it should be defined
        assert!(env.is_type_defined("MyType"));
    }

    #[test]
    fn test_lookup_type_alias_priority() {
        let mut env = TypeEnvironment::new();

        // Register interface with same name as type alias
        let alias_type = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );
        env.register_type_alias("Foo".to_string(), alias_type.clone())
            .unwrap();

        let interface_type = Type::new(
            TypeKind::Primitive(PrimitiveType::String),
            Span::new(0, 0, 0, 0),
        );
        env.register_interface("Foo".to_string(), interface_type.clone())
            .unwrap();

        // Type aliases take priority over interfaces in lookup_type
        let found = env.lookup_type("Foo").unwrap();
        match &found.kind {
            TypeKind::Primitive(PrimitiveType::Number) => (), // Type alias
            TypeKind::Primitive(PrimitiveType::String) => {
                panic!("Should have found type alias, not interface")
            }
            _ => panic!("Unexpected type"),
        }
    }

    #[test]
    fn test_register_generic_type_alias() {
        let mut env = TypeEnvironment::new();

        // Create a proper TypeParameter with StringId
        use typedlua_parser::ast::Spanned;
        use typedlua_parser::string_interner::StringInterner;

        let interner = StringInterner::new();
        let t_id = interner.get_or_intern("T");
        let type_param = TypeParameter {
            name: Spanned::new(t_id, Span::new(0, 1, 1, 0)),
            constraint: None,
            default: None,
            span: Span::new(0, 1, 1, 0),
        };

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );

        env.register_generic_type_alias("Container".to_string(), vec![type_param], typ)
            .unwrap();

        let generic_alias = env.get_generic_type_alias("Container");
        assert!(generic_alias.is_some());
        assert_eq!(generic_alias.unwrap().type_parameters.len(), 1);
    }

    #[test]
    fn test_duplicate_generic_type_alias() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );

        env.register_generic_type_alias("Box".to_string(), vec![], typ.clone())
            .unwrap();
        assert!(env
            .register_generic_type_alias("Box".to_string(), vec![], typ)
            .is_err());
    }

    #[test]
    fn test_duplicate_interface() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Table),
            Span::new(0, 0, 0, 0),
        );

        env.register_interface("MyInterface".to_string(), typ.clone())
            .unwrap();
        assert!(env
            .register_interface("MyInterface".to_string(), typ)
            .is_err());
    }

    #[test]
    fn test_resolve_type_reference_success() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        );
        env.register_type_alias("MyNumber".to_string(), typ)
            .unwrap();

        let resolved = env.resolve_type_reference("MyNumber");
        assert!(resolved.is_ok());
        assert!(resolved.unwrap().is_some());
    }

    #[test]
    fn test_resolve_type_reference_not_found() {
        let env = TypeEnvironment::new();

        let resolved = env.resolve_type_reference("NonExistent");
        assert!(resolved.is_ok());
        assert!(resolved.unwrap().is_none());
    }

    #[test]
    fn test_resolve_type_reference_cycle() {
        let env = TypeEnvironment::new();

        // Create a self-referencing type alias
        // Note: This requires the type to reference itself, which is tricky
        // with the current API. For now, we'll just test that the cycle
        // detection mechanism works by manually marking a type as resolving.
        env.resolving.borrow_mut().insert("Cycle".to_string());

        let result = env.resolve_type_reference("Cycle");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Recursive type alias"));

        // Clean up
        env.resolving.borrow_mut().remove("Cycle");
    }

    #[test]
    fn test_is_utility_type() {
        let utility_types = vec![
            "Partial",
            "Required",
            "Readonly",
            "Record",
            "Pick",
            "Omit",
            "Exclude",
            "Extract",
            "NonNilable",
            "Nilable",
            "ReturnType",
            "Parameters",
        ];

        for utility in &utility_types {
            assert!(
                TypeEnvironment::is_utility_type(utility),
                "'{}' should be recognized as utility type",
                utility
            );
        }

        let non_utility_types = vec!["number", "string", "Array", "Map", "MyType"];

        for non_utility in &non_utility_types {
            assert!(
                !TypeEnvironment::is_utility_type(non_utility),
                "'{}' should not be recognized as utility type",
                non_utility
            );
        }
    }

    #[test]
    fn test_get_interface_alias() {
        let mut env = TypeEnvironment::new();

        let typ = Type::new(
            TypeKind::Primitive(PrimitiveType::Table),
            Span::new(0, 0, 0, 0),
        );
        env.register_interface("User".to_string(), typ.clone())
            .unwrap();

        // get_interface should be an alias for lookup_interface
        assert!(env.get_interface("User").is_some());
        assert!(env.get_interface("NonExistent").is_none());
    }

    #[test]
    fn test_default_impl() {
        let env: TypeEnvironment = Default::default();
        assert!(env.lookup_type("number").is_some());
    }

    #[test]
    fn test_multiple_type_aliases() {
        let mut env = TypeEnvironment::new();

        let types = vec![
            ("Int", PrimitiveType::Integer),
            ("Float", PrimitiveType::Number),
            ("Bool", PrimitiveType::Boolean),
            ("Str", PrimitiveType::String),
        ];

        for (name, prim) in &types {
            let typ = Type::new(TypeKind::Primitive(*prim), Span::new(0, 0, 0, 0));
            env.register_type_alias(name.to_string(), typ).unwrap();
        }

        for (name, _) in &types {
            assert!(env.lookup_type(name).is_some());
        }
    }

    #[test]
    fn test_type_not_found_returns_none() {
        let env = TypeEnvironment::new();

        assert!(env.lookup_type("UnknownType").is_none());
        assert!(env.lookup_type_alias("UnknownType").is_none());
        assert!(env.lookup_interface("UnknownType").is_none());
        assert!(env.get_generic_type_alias("UnknownType").is_none());
    }
}
