use super::TypeCheckVisitor;
use crate::TypeCheckError;
use rustc_hash::FxHashMap;
use typedlua_parser::ast::statement::{AccessModifier, Parameter};
use typedlua_parser::ast::types::Type;
use typedlua_parser::prelude::OperatorKind;
use typedlua_parser::span::Span;

/// Information about a class member for access checking
#[derive(Clone)]
pub struct ClassMemberInfo<'arena> {
    pub(crate) name: String,
    pub(crate) access: AccessModifier,
    pub(crate) _is_static: bool,
    pub(crate) kind: ClassMemberKind<'arena>,
    pub(crate) is_final: bool,
}

#[derive(Clone)]
pub enum ClassMemberKind<'arena> {
    Property {
        type_annotation: Type<'arena>,
    },
    Method {
        parameters: Vec<Parameter<'arena>>,
        return_type: Option<Type<'arena>>,
        is_abstract: bool,
    },
    Getter {
        return_type: Type<'arena>,
    },
    Setter {
        parameter_type: Type<'arena>,
    },
    Operator {
        operator: OperatorKind,
        parameters: Vec<Parameter<'arena>>,
        return_type: Option<Type<'arena>>,
    },
}

/// Context for tracking the current class during type checking
#[derive(Clone)]
pub struct ClassContext<'arena> {
    pub(crate) name: String,
    pub(crate) parent: Option<String>,
    /// The full extends type (preserves type arguments for generic parent classes)
    pub(crate) extends_type: Option<typedlua_parser::ast::types::Type<'arena>>,
}

/// Trait for access control checks on class members
pub trait AccessControlVisitor<'arena>: TypeCheckVisitor {
    /// Check if access to a class member is allowed based on access modifier
    fn check_member_access(
        &self,
        current_class: &Option<ClassContext<'arena>>,
        class_name: &str,
        member_name: &str,
        span: Span,
    ) -> Result<(), TypeCheckError>;

    /// Check if a class is a subclass of another
    fn is_subclass(&self, child: &str, ancestor: &str) -> bool;

    /// Register a class with its members
    fn register_class(&mut self, name: &str, parent: Option<String>);

    /// Register a class member
    fn register_member(&mut self, class_name: &str, member: ClassMemberInfo<'arena>);

    /// Mark a class as final
    fn mark_class_final(&mut self, name: &str, is_final: bool);

    /// Check if a class is marked as final
    fn is_class_final(&self, name: &str) -> bool;

    /// Mark a class as having the @readonly decorator
    fn mark_class_readonly(&mut self, name: &str, is_readonly: bool);

    /// Check if a class has the @readonly decorator
    fn is_class_readonly(&self, name: &str) -> bool;

    /// Check if assignment to a class property is allowed (readonly check)
    fn check_readonly_assignment(
        &self,
        class_name: &str,
        member_name: &str,
    ) -> Result<(), TypeCheckError>;

    /// Get class members
    fn get_class_members(&self, class_name: &str) -> Option<&Vec<ClassMemberInfo<'arena>>>;

    /// Get parent class name
    fn get_parent_class(&self, class_name: &str) -> Option<String>;

    /// Set current class context
    fn set_current_class(&mut self, class: Option<ClassContext<'arena>>);

    /// Get current class context
    fn get_current_class(&self) -> &Option<ClassContext<'arena>>;

    /// Register the interfaces that a class implements
    fn register_class_implements(&mut self, class_name: &str, interfaces: Vec<String>);

    /// Get the interfaces implemented by a class
    fn get_class_implements(&self, class_name: &str) -> Option<&Vec<String>>;
}

/// Default implementation of access control
pub struct AccessControl<'arena> {
    class_members: FxHashMap<String, Vec<ClassMemberInfo<'arena>>>,
    final_classes: FxHashMap<String, bool>,
    class_parents: FxHashMap<String, Option<String>>, // Store class hierarchy
    class_implements: FxHashMap<String, Vec<String>>, // Store class -> interfaces mapping
    current_class: Option<ClassContext<'arena>>,
    readonly_classes: FxHashMap<String, bool>, // Track classes with @readonly decorator
}

impl<'arena> Default for AccessControl<'arena> {
    fn default() -> Self {
        Self {
            class_members: FxHashMap::default(),
            final_classes: FxHashMap::default(),
            class_parents: FxHashMap::default(),
            class_implements: FxHashMap::default(),
            current_class: None,
            readonly_classes: FxHashMap::default(),
        }
    }
}

impl<'arena> AccessControl<'arena> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Find a member by walking the class hierarchy (current class, then parent, etc.)
    /// Also checks implemented interfaces for default method implementations
    fn find_member_in_hierarchy(
        &self,
        class_name: &str,
        member_name: &str,
    ) -> Option<&ClassMemberInfo<'arena>> {
        let mut current = class_name;
        loop {
            if let Some(members) = self.class_members.get(current) {
                if let Some(info) = members.iter().find(|m| m.name == member_name) {
                    return Some(info);
                }
            }
            // Walk to parent class
            if let Some(Some(parent_name)) = self.class_parents.get(current) {
                // Strip generic arguments from parent name (e.g. "DataStore<number>" -> "DataStore")
                let base_name = if let Some(idx) = parent_name.find('<') {
                    &parent_name[..idx]
                } else {
                    parent_name.as_str()
                };
                if base_name == current {
                    break; // Prevent infinite loop
                }
                current = base_name;
            } else {
                break;
            }
        }

        // If not found in class hierarchy, check implemented interfaces
        self.find_member_in_interfaces(class_name, member_name)
    }

    /// Find a member in the interfaces implemented by a class
    fn find_member_in_interfaces(
        &self,
        class_name: &str,
        member_name: &str,
    ) -> Option<&ClassMemberInfo<'arena>> {
        if let Some(interfaces) = self.class_implements.get(class_name) {
            for interface_name in interfaces {
                // Strip generic arguments from interface name
                let base_name = if let Some(idx) = interface_name.find('<') {
                    &interface_name[..idx]
                } else {
                    interface_name.as_str()
                };

                if let Some(members) = self.class_members.get(base_name) {
                    if let Some(info) = members.iter().find(|m| m.name == member_name) {
                        return Some(info);
                    }
                }
            }
        }
        None
    }
}

impl<'arena> TypeCheckVisitor for AccessControl<'arena> {
    fn name(&self) -> &'static str {
        "AccessControl"
    }
}

impl<'arena> AccessControlVisitor<'arena> for AccessControl<'arena> {
    fn check_member_access(
        &self,
        current_class: &Option<ClassContext<'arena>>,
        class_name: &str,
        member_name: &str,
        span: Span,
    ) -> Result<(), TypeCheckError> {
        // Get the member info - check current class and parent classes
        let member_info = self.find_member_in_hierarchy(class_name, member_name);

        if let Some(info) = member_info {
            match &info.access {
                AccessModifier::Public => {
                    // Public members are accessible from anywhere
                    Ok(())
                }
                AccessModifier::Private => {
                    // Private members are only accessible from within the same class
                    if let Some(ref current) = current_class {
                        if current.name == class_name {
                            Ok(())
                        } else {
                            Err(TypeCheckError::new(
                                format!(
                                    "Property '{}' is private and only accessible within class '{}'",
                                    member_name, class_name
                                ),
                                span,
                            ))
                        }
                    } else {
                        Err(TypeCheckError::new(
                            format!(
                                "Property '{}' is private and only accessible within class '{}'",
                                member_name, class_name
                            ),
                            span,
                        ))
                    }
                }
                AccessModifier::Protected => {
                    // Protected members are accessible from within the class and subclasses
                    if let Some(ref current) = current_class {
                        if current.name == class_name {
                            // Same class - allowed
                            Ok(())
                        } else if self.is_subclass(&current.name, class_name) {
                            // Subclass - allowed
                            Ok(())
                        } else {
                            Err(TypeCheckError::new(
                                format!(
                                    "Property '{}' is protected and only accessible within class '{}' and its subclasses",
                                    member_name, class_name
                                ),
                                span,
                            ))
                        }
                    } else {
                        Err(TypeCheckError::new(
                            format!(
                                "Property '{}' is protected and only accessible within class '{}' and its subclasses",
                                member_name, class_name
                            ),
                            span,
                        ))
                    }
                }
            }
        } else {
            // Check if class exists in access control
            if !self.class_members.contains_key(class_name) {
                // Class not registered in access control - this may be a type alias,
                // interface, or other non-class type. Allow access; the type resolver
                // will handle member lookup or report errors downstream.
                return Ok(());
            }

            // Class exists but member not found - allow access since the member
            // might be resolved through type environment or parent classes
            Ok(())
        }
    }

    fn is_subclass(&self, child: &str, ancestor: &str) -> bool {
        // Use stored class hierarchy to check subclass relationship
        let mut current = child;

        while let Some(parent) = self.class_parents.get(current) {
            if let Some(ref parent_name) = parent {
                if parent_name == ancestor {
                    return true;
                }
                current = parent_name;
            } else {
                break;
            }
        }

        false
    }

    fn register_class(&mut self, name: &str, parent: Option<String>) {
        self.class_members.entry(name.to_string()).or_default();
        self.final_classes.entry(name.to_string()).or_insert(false);
        self.class_parents.insert(name.to_string(), parent);
    }

    fn register_member(&mut self, class_name: &str, member: ClassMemberInfo<'arena>) {
        if let Some(members) = self.class_members.get_mut(class_name) {
            members.push(member);
        }
    }

    fn mark_class_final(&mut self, name: &str, is_final: bool) {
        self.final_classes.insert(name.to_string(), is_final);
    }

    fn is_class_final(&self, name: &str) -> bool {
        *self.final_classes.get(name).unwrap_or(&false)
    }

    /// Mark a class as having the @readonly decorator
    fn mark_class_readonly(&mut self, name: &str, is_readonly: bool) {
        self.readonly_classes.insert(name.to_string(), is_readonly);
    }

    /// Check if a class has the @readonly decorator
    fn is_class_readonly(&self, name: &str) -> bool {
        *self.readonly_classes.get(name).unwrap_or(&false)
    }

    /// Check if assignment to a class property is allowed (readonly check)
    fn check_readonly_assignment(
        &self,
        class_name: &str,
        member_name: &str,
    ) -> Result<(), TypeCheckError> {
        if self.is_class_readonly(class_name) {
            // For readonly classes, all properties are effectively final
            return Err(TypeCheckError::new(
                format!("Cannot assign to readonly property '{}'", member_name),
                typedlua_parser::span::Span::default(),
            ));
        }
        // Check individual property finality even on non-readonly classes
        if let Some(member) = self.find_member_in_hierarchy(class_name, member_name) {
            if member.is_final {
                return Err(TypeCheckError::new(
                    format!("Cannot assign to readonly property '{}'", member_name),
                    typedlua_parser::span::Span::default(),
                ));
            }
        }
        Ok(())
    }

    fn get_class_members(&self, class_name: &str) -> Option<&Vec<ClassMemberInfo<'arena>>> {
        self.class_members.get(class_name)
    }

    fn get_parent_class(&self, class_name: &str) -> Option<String> {
        self.class_parents.get(class_name).cloned().flatten()
    }

    fn set_current_class(&mut self, class: Option<ClassContext<'arena>>) {
        self.current_class = class;
    }

    fn get_current_class(&self) -> &Option<ClassContext<'arena>> {
        &self.current_class
    }

    fn register_class_implements(&mut self, class_name: &str, interfaces: Vec<String>) {
        self.class_implements
            .insert(class_name.to_string(), interfaces);
    }

    fn get_class_implements(&self, class_name: &str) -> Option<&Vec<String>> {
        self.class_implements.get(class_name)
    }
}

#[cfg(test)]
mod access_control_tests;
