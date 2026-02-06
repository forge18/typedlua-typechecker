//! Validation phase: Type compatibility and validation checks
//!
//! This phase handles:
//! - Interface member validation (duplicate checking)
//! - Index signature validation
//! - Abstract method implementation verification
//! - Method override validation (parameter/return type compatibility)
//! - Decorator validation
//!
//! **Design Pattern**: Stateless phase functions that take explicit context parameters.

#![allow(dead_code)]

use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_compat::TypeCompatibility;
use crate::types::generics;
use crate::utils::symbol_table::SymbolTable;
use crate::visitors::{AccessControl, AccessControlVisitor, ClassMemberKind};
use crate::TypeCheckError;
use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::sync::Arc;
use typedlua_parser::ast::expression::Expression;
use typedlua_parser::ast::statement::{
    ClassMember, Decorator, DecoratorExpression, IndexSignature, MethodDeclaration, TypeParameter,
};
use typedlua_parser::ast::types::{ObjectTypeMember, Type};
use typedlua_parser::prelude::ClassDeclaration;
use typedlua_parser::span::Span;
use typedlua_parser::string_interner::StringInterner;

/// Validate interface members for duplicate property names.
///
/// Interfaces cannot have duplicate property or method names.
/// This function checks all members and returns an error if duplicates are found.
///
/// # Parameters
///
/// - `members`: The interface members to validate
/// - `span`: Source span for error reporting
///
/// # Returns
///
/// Returns `Ok(())` if validation passes, or an error if duplicates are found.
pub fn validate_interface_members(
    members: &[ObjectTypeMember],
    span: Span,
) -> Result<(), TypeCheckError> {
    // Check for duplicate property names
    let mut seen_names = HashSet::new();

    for member in members {
        let name = match member {
            ObjectTypeMember::Property(prop) => Some(&prop.name.node),
            ObjectTypeMember::Method(method) => Some(&method.name.node),
            ObjectTypeMember::Index(_) => None,
        };

        if let Some(name) = name {
            if !seen_names.insert(*name) {
                return Err(TypeCheckError::new(
                    format!("Duplicate property '{}' in interface", name),
                    span,
                ));
            }
        }
    }

    Ok(())
}

/// Validate that class properties conform to index signature constraints.
///
/// When a class has an index signature, all properties must have types that are
/// assignable to the index signature's value type.
///
/// # Parameters
///
/// - `class_decl`: The class declaration to validate
/// - `index_sig`: The index signature to check against
/// - `interner`: String interner for resolving property names
///
/// # Returns
///
/// Returns `Ok(())` if validation passes, or an error if any property violates the constraint.
pub fn validate_index_signature<'arena>(
    class_decl: &ClassDeclaration<'arena>,
    index_sig: &IndexSignature<'arena>,
    interner: &StringInterner,
) -> Result<(), TypeCheckError> {
    for member in &class_decl.members {
        if let ClassMember::Property(prop) = member {
            // Check if property type is assignable to index signature value type
            if !TypeCompatibility::is_assignable(&prop.type_annotation, &index_sig.value_type) {
                return Err(TypeCheckError::new(
                    format!(
                        "Property '{}' is not assignable to index signature value type",
                        interner.resolve(prop.name.node)
                    ),
                    prop.span,
                ));
            }
        }
    }

    Ok(())
}

/// Check that a class implements all abstract methods from its parent class.
///
/// When a class extends a parent class with abstract methods, it must provide
/// concrete implementations for all abstract methods. This function walks the
/// inheritance chain to verify all abstract methods are implemented.
///
/// # Parameters
///
/// - `class_name`: The name of the class being validated
/// - `parent_name`: The name of the parent class
/// - `class_members`: The members of the child class
/// - `access_control`: Access control visitor for checking parent members
/// - `interner`: String interner for name resolution
///
/// # Returns
///
/// Returns `Ok(())` if all abstract methods are implemented, or an error otherwise.
pub fn check_abstract_methods_implemented(
    class_name: &str,
    parent_name: &str,
    class_members: &[ClassMember],
    access_control: &AccessControl,
    interner: &StringInterner,
) -> Result<(), TypeCheckError> {
    // Get the parent class members
    if let Some(parent_members) = access_control.get_class_members(parent_name) {
        for member in parent_members {
            if let ClassMemberKind::Method {
                is_abstract: true, ..
            } = &member.kind
            {
                // Check if this class implements the abstract method
                let method_name = &member.name;
                let implemented = class_members.iter().any(|m| {
                    if let ClassMember::Method(method) = m {
                        method.name.node.as_u32() == interner.get_or_intern(method_name).as_u32()
                    } else {
                        false
                    }
                });

                if !implemented {
                    return Err(TypeCheckError::new(
                        format!(
                            "Class '{}' must implement abstract method '{}' from parent class '{}'",
                            class_name, method_name, parent_name
                        ),
                        Span::dummy(),
                    ));
                }
            }
        }
    }

    Ok(())
}

/// Validate decorators on a declaration.
///
/// This function checks:
/// - Decorators are enabled in configuration
/// - No duplicate decorators
/// - Decorator expressions are valid
///
/// # Parameters
///
/// - `decorators`: The decorators to validate
/// - `enable_decorators`: Whether decorators are enabled in configuration
/// - `interner`: String interner for name resolution
/// - `symbol_table`: Symbol table for checking decorator existence
/// - `diagnostic_handler`: For reporting warnings
/// - `infer_expression_type`: Callback to infer decorator argument types
///
/// # Returns
///
/// Returns `Ok(())` if validation passes, or an error if decorators are disabled
/// or expressions are invalid.
pub fn check_decorators<F>(
    decorators: &mut [Decorator],
    enable_decorators: bool,
    interner: &StringInterner,
    symbol_table: &SymbolTable<'arena>,
    diagnostic_handler: &Arc<dyn DiagnosticHandler>,
    mut infer_expression_type: F,
) -> Result<(), TypeCheckError>
where
    F: FnMut(&mut Expression<'arena>) -> Result<Type, TypeCheckError>,
{
    // Check if decorators are enabled
    if !decorators.is_empty() && !enable_decorators {
        return Err(TypeCheckError::new(
            "Decorators require decorator features to be enabled. Enable 'enableDecorators' in your configuration.".to_string(),
            decorators[0].span,
        ));
    }

    // Check for duplicate decorators
    let mut seen_decorators = HashSet::new();
    for decorator in decorators.iter() {
        // Get decorator name for comparison
        let decorator_name = match &decorator.expression {
            DecoratorExpression::Identifier(name) => interner.resolve(name.node).to_string(),
            DecoratorExpression::Call { callee, .. } => {
                // For calls, use the callee name
                if let DecoratorExpression::Identifier(name) = &**callee {
                    interner.resolve(name.node).to_string()
                } else {
                    continue; // Skip complex expressions
                }
            }
            DecoratorExpression::Member { .. } => {
                continue; // Skip member expressions for duplicate checking
            }
        };

        if !seen_decorators.insert(decorator_name.clone()) {
            diagnostic_handler.warning(
                decorator.span,
                &format!("Duplicate decorator '@{}'", decorator_name),
            );
        }
    }

    // Validate decorator expressions
    for decorator in decorators.iter_mut() {
        check_decorator_expression(
            &mut decorator.expression,
            interner,
            symbol_table,
            &mut infer_expression_type,
        )?;
    }

    Ok(())
}

/// Check a decorator expression.
///
/// Validates that decorator identifiers, calls, and member expressions are well-formed.
/// For decorator calls, type-checks all arguments.
///
/// # Parameters
///
/// - `expr`: The decorator expression to check
/// - `interner`: String interner for name resolution
/// - `symbol_table`: Symbol table for checking identifier existence
/// - `infer_expression_type`: Callback to infer argument types
fn check_decorator_expression<F>(
    expr: &mut DecoratorExpression,
    interner: &StringInterner,
    symbol_table: &SymbolTable<'arena>,
    infer_expression_type: &mut F,
) -> Result<(), TypeCheckError>
where
    F: FnMut(&mut Expression<'arena>) -> Result<Type, TypeCheckError>,
{
    match expr {
        DecoratorExpression::Identifier(name) => {
            // Verify the decorator identifier exists (could be a function or imported decorator)
            // For now, we allow any identifier - full validation would check it's a valid decorator function
            let name_str = interner.resolve(name.node);
            if symbol_table.lookup(&name_str).is_none() {
                // It's okay if it doesn't exist - it might be a built-in decorator like @readonly, @sealed
                // We'll allow it through for now
            }
            Ok(())
        }
        DecoratorExpression::Call {
            callee, arguments, ..
        } => {
            // Check the callee
            check_decorator_expression(callee, interner, symbol_table, infer_expression_type)?;

            // Type check all arguments
            for arg in arguments.iter_mut() {
                infer_expression_type(arg)?;
            }

            Ok(())
        }
        DecoratorExpression::Member { object, .. } => {
            // Check the object part
            check_decorator_expression(object, interner, symbol_table, infer_expression_type)?;
            Ok(())
        }
    }
}

/// Check method override compatibility.
///
/// When a method is marked with the `override` keyword, this function validates:
/// - The class has a parent class
/// - The parent class has a method with the same name
/// - The parent method is not marked `final`
/// - Parameter types are compatible (contravariant)
/// - Return types are compatible (covariant)
/// - Generic parent types are properly instantiated
///
/// # Parameters
///
/// - `method`: The method declaration to check
/// - `class_name`: Name of the class containing the method
/// - `parent_name`: Name of the parent class
/// - `parent_type_params`: Type parameters of the parent class (if generic)
/// - `extends_type_args`: Type arguments in the extends clause
/// - `access_control`: Access control visitor for checking parent members
/// - `interner`: String interner for name resolution
/// - `deep_resolve_type`: Callback to resolve type aliases
///
/// # Returns
///
/// Returns `Ok(())` if the override is valid, or an error if validation fails.
#[allow(clippy::too_many_arguments)]
pub fn check_method_override<F>(
    method: &MethodDeclaration<'arena>,
    class_name: &str,
    parent_name: Option<&String>,
    parent_type_params: Option<&Vec<TypeParameter<'arena>>>,
    extends_type_args: Option<&Vec<Type<'arena>>>,
    access_control: &AccessControl,
    interner: &StringInterner,
    mut deep_resolve_type: F,
) -> Result<(), TypeCheckError>
where
    F: FnMut(&Type<'arena>) -> Type<'arena>,
{
    // Check if class has a parent
    let parent_name = parent_name.ok_or_else(|| {
        TypeCheckError::new(
            format!(
                "Method '{}' uses override but class '{}' has no parent class",
                method.name.node, class_name
            ),
            method.span,
        )
    })?;

    // Walk the inheritance chain to find the method and check if it's final
    let method_name = interner.resolve(method.name.node);
    let mut current_class = parent_name.clone();
    let mut found_method = None;
    let mut found_in_class = None;

    loop {
        if let Some(parent_members) = access_control.get_class_members(&current_class) {
            if let Some(parent_method) = parent_members.iter().find(|m| m.name == method_name) {
                found_method = Some(parent_method);
                found_in_class = Some(current_class.clone());
                break;
            }
        }

        // Get parent from access_control's hierarchy
        let parent_name_opt = access_control.get_parent_class(&current_class);
        match parent_name_opt {
            Some(next_parent) => current_class = next_parent,
            None => break,
        }
    }

    let parent_method = found_method.ok_or_else(|| {
        TypeCheckError::new(
            format!(
                "Method '{}' marked as override but parent class does not have this method",
                method_name
            ),
            method.span,
        )
    })?;

    // Check if parent method is final anywhere in the inheritance chain
    if parent_method.is_final {
        return Err(TypeCheckError::new(
            format!(
                "Cannot override final method {} from ancestor class {}",
                method.name.node,
                found_in_class.unwrap()
            ),
            method.span,
        ));
    }

    match &parent_method.kind {
        ClassMemberKind::Method {
            parameters: parent_params,
            return_type: parent_return,
            ..
        } => {
            // Check parameter count
            if method.parameters.len() != parent_params.len() {
                return Err(TypeCheckError::new(
                    format!(
                        "Method '{}' has {} parameters but overridden method has {} parameters",
                        method.name.node,
                        method.parameters.len(),
                        parent_params.len()
                    ),
                    method.span,
                ));
            }

            // Check parameter types (contravariance)
            for (i, (child_param, parent_param)) in method
                .parameters
                .iter()
                .zip(parent_params.iter())
                .enumerate()
            {
                let child_type = child_param.type_annotation.as_ref().ok_or_else(|| {
                    TypeCheckError::new(
                        format!(
                            "Override method '{}' parameter {} must have explicit type annotation",
                            method.name.node,
                            i + 1
                        ),
                        child_param.span,
                    )
                })?;

                let raw_parent_type = parent_param.type_annotation.as_ref().ok_or_else(|| {
                    TypeCheckError::new(
                        format!(
                            "Parent method '{}' parameter {} has no type annotation",
                            method.name.node,
                            i + 1
                        ),
                        parent_param.span,
                    )
                })?;

                // Instantiate parent type if the parent class is generic
                let parent_type = if let (Some(type_params), Some(type_args)) =
                    (parent_type_params, extends_type_args)
                {
                    generics::instantiate_type(raw_parent_type, type_params, type_args)
                        .unwrap_or_else(|_| raw_parent_type.clone())
                } else {
                    raw_parent_type.clone()
                };

                // Deep-resolve both types for comparison
                let resolved_child = deep_resolve_type(child_type);
                let resolved_parent = deep_resolve_type(&parent_type);

                // Parameters are contravariant: parent type must be assignable to child type
                // (child can accept a more specific type than parent)
                if !TypeCompatibility::is_assignable(&resolved_parent, &resolved_child) {
                    return Err(TypeCheckError::new(
                        format!(
                            "Method '{}' parameter {} type is incompatible with parent parameter type",
                            method.name.node,
                            i + 1
                        ),
                        child_param.span,
                    ));
                }
            }

            // Check return type (covariance)
            if let Some(child_return) = &method.return_type {
                if let Some(raw_parent_ret) = parent_return {
                    // Instantiate parent return type if generic
                    let parent_ret = if let (Some(type_params), Some(type_args)) =
                        (parent_type_params, extends_type_args)
                    {
                        generics::instantiate_type(raw_parent_ret, type_params, type_args)
                            .unwrap_or_else(|_| raw_parent_ret.clone())
                    } else {
                        raw_parent_ret.clone()
                    };

                    let resolved_child_ret = deep_resolve_type(child_return);
                    let resolved_parent_ret = deep_resolve_type(&parent_ret);

                    // Child return type must be assignable to parent return type
                    if !TypeCompatibility::is_assignable(&resolved_parent_ret, &resolved_child_ret)
                    {
                        return Err(TypeCheckError::new(
                            format!(
                                "Method '{}' return type is incompatible with parent return type",
                                method.name.node
                            ),
                            method.span,
                        ));
                    }
                }
            } else if parent_return.is_some() {
                return Err(TypeCheckError::new(
                    format!(
                        "Method '{}' must have return type to match parent method",
                        method.name.node
                    ),
                    method.span,
                ));
            }

            Ok(())
        }
        _ => Err(TypeCheckError::new(
            format!(
                "Cannot override '{}' - parent member is not a method",
                method.name.node
            ),
            method.span,
        )),
    }
}

/// Check if a class has circular inheritance.
///
/// Detects inheritance cycles like: A extends B, B extends C, C extends A.
///
/// # Parameters
///
/// - `class_name`: The class name to check for circular inheritance
/// - `class_parents`: Map from class name to parent class name
///
/// # Returns
///
/// Returns `true` if a circular inheritance is detected, `false` otherwise.
pub fn has_circular_inheritance(
    class_name: &str,
    class_parents: &FxHashMap<String, String>,
) -> bool {
    let mut visited = std::collections::HashSet::new();
    let mut current = class_name.to_string();

    visited.insert(current.clone());

    while let Some(parent) = class_parents.get(&current) {
        if visited.contains(parent) {
            return true; // Found a cycle
        }
        visited.insert(parent.clone());
        current = parent.clone();
    }

    false
}

/// Check that a class properly implements an interface.
///
/// Validates that:
/// - All required interface properties are present in the class
/// - All required interface methods are implemented with compatible signatures
/// - Index signatures are properly implemented
///
/// # Parameters
///
/// - `class_decl`: The class declaration to validate
/// - `interface`: The interface type that the class claims to implement
/// - `type_env`: Type environment for checking class implements relationships
/// - `interner`: String interner for resolving names in error messages
///
/// # Returns
///
/// Returns `Ok(())` if the class properly implements the interface, or an error if validation fails.
pub fn check_class_implements_interface<'arena>(
    class_decl: &ClassDeclaration<'arena>,
    interface: &Type<'arena>,
    type_env: &crate::core::type_environment::TypeEnvironment,
    interner: &StringInterner,
) -> Result<(), TypeCheckError> {
    use typedlua_parser::ast::statement::ClassMember;
    use typedlua_parser::ast::types::{ObjectTypeMember, TypeKind};

    if let TypeKind::Object(obj_type) = &interface.kind {
        for required_member in &obj_type.members {
            match required_member {
                ObjectTypeMember::Property(req_prop) => {
                    // Find matching property in class
                    let found = class_decl.members.iter().any(|member| {
                        if let ClassMember::Property(class_prop) = member {
                            class_prop.name.node == req_prop.name.node
                        } else {
                            false
                        }
                    });

                    if !found && !req_prop.is_optional {
                        return Err(TypeCheckError::new(
                            format!(
                                "Class '{}' does not implement required property '{}' from interface",
                                interner.resolve(class_decl.name.node),
                                interner.resolve(req_prop.name.node)
                            ),
                            class_decl.span,
                        ));
                    }
                }
                ObjectTypeMember::Method(req_method) => {
                    // Find matching method in class and validate signature
                    let matching_method = class_decl.members.iter().find_map(|member| {
                        if let ClassMember::Method(class_method) = member {
                            if class_method.name.node == req_method.name.node {
                                return Some(class_method);
                            }
                        }
                        None
                    });

                    match matching_method {
                        None => {
                            if req_method.body.is_none() {
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Class '{}' does not implement required method '{}' from interface",
                                        interner.resolve(class_decl.name.node),
                                        interner.resolve(req_method.name.node)
                                    ),
                                    class_decl.span,
                                ));
                            }
                            // Method has default implementation in interface, okay
                        }
                        Some(class_method) => {
                            // Check parameter count
                            if class_method.parameters.len() != req_method.parameters.len() {
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Method '{}' has {} parameters but interface requires {}",
                                        interner.resolve(req_method.name.node),
                                        class_method.parameters.len(),
                                        req_method.parameters.len()
                                    ),
                                    class_method.span,
                                ));
                            }

                            // Check parameter types
                            for (i, (class_param, req_param)) in class_method
                                .parameters
                                .iter()
                                .zip(req_method.parameters.iter())
                                .enumerate()
                            {
                                if let (Some(class_type), Some(req_type)) =
                                    (&class_param.type_annotation, &req_param.type_annotation)
                                {
                                    if !TypeCompatibility::is_assignable(class_type, req_type) {
                                        return Err(TypeCheckError::new(
                                            format!(
                                                "Method '{}' parameter {} has incompatible type",
                                                interner.resolve(req_method.name.node),
                                                i
                                            ),
                                            class_method.span,
                                        ));
                                    }
                                }
                            }

                            // Check return type (covariant: class return must be assignable to interface return)
                            // MethodSignature has return_type: Type (not Option)
                            // MethodDeclaration has return_type: Option<Type>
                            if let Some(class_return) = &class_method.return_type {
                                if !TypeCompatibility::is_assignable(
                                    class_return,
                                    &req_method.return_type,
                                ) && !check_implements_assignable(
                                    class_return,
                                    &req_method.return_type,
                                    type_env,
                                    interner,
                                ) {
                                    return Err(TypeCheckError::new(
                                        format!(
                                            "Method '{}' has incompatible return type",
                                            interner.resolve(req_method.name.node)
                                        ),
                                        class_method.span,
                                    ));
                                }
                            } else {
                                // Method has no return type annotation, but interface requires one
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Method '{}' must have a return type annotation to match interface",
                                        interner.resolve(req_method.name.node)
                                    ),
                                    class_method.span,
                                ));
                            }
                        }
                    }
                }
                ObjectTypeMember::Index(index_sig) => {
                    // Validate that all class properties are compatible with index signature
                    validate_index_signature(class_decl, index_sig, interner)?;
                }
            }
        }
    }

    Ok(())
}

/// Check if source type is assignable to target type via implements relationship.
///
/// This handles covariance in interface implementation. For example, Box<number> is
/// assignable to Storable<number> if Box implements Storable<T>.
///
/// # Parameters
///
/// - `source`: The source type to check
/// - `target`: The target type to check against
/// - `type_env`: Type environment for looking up class implements relationships
/// - `interner`: String interner for resolving type names
///
/// # Returns
///
/// Returns `true` if source type implements target interface, `false` otherwise.
pub fn check_implements_assignable<'arena>(
    source: &Type<'arena>,
    target: &Type<'arena>,
    type_env: &crate::core::type_environment::TypeEnvironment,
    interner: &StringInterner,
) -> bool {
    use typedlua_parser::ast::types::TypeKind;

    if let (TypeKind::Reference(s_ref), TypeKind::Reference(t_ref)) = (&source.kind, &target.kind) {
        let source_name = interner.resolve(s_ref.name.node);
        let target_name = interner.resolve(t_ref.name.node);

        // Check if source class implements the target interface
        if let Some(implements) = type_env.get_class_implements(&source_name) {
            for iface_type in implements {
                if let TypeKind::Reference(iface_ref) = &iface_type.kind {
                    let iface_name = interner.resolve(iface_ref.name.node);
                    if iface_name == target_name {
                        // Interface name matches. For generic interfaces, check type arg
                        // compatibility. The common case is pass-through type params:
                        // class Box<T> implements Storable<T> means Box<number> -> Storable<number>
                        match (&s_ref.type_arguments, &t_ref.type_arguments) {
                            (None, None) => return true,
                            (Some(s_args), Some(t_args)) if s_args.len() == t_args.len() => {
                                if s_args
                                    .iter()
                                    .zip(t_args.iter())
                                    .all(|(s, t)| TypeCompatibility::is_assignable(s, t))
                                {
                                    return true;
                                }
                            }
                            _ => {
                                // Arity mismatch or partial generics - still allow if names match
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

/// Validate class inheritance - checks for final parent and circular inheritance.
///
/// This focused function validates that a class's inheritance is valid:
/// - Parent class is not marked as final
/// - No circular inheritance exists
///
/// # Returns
///
/// Returns Ok(parent_name) if inheritance is valid, or an error if validation fails.
pub fn validate_class_inheritance(
    class_name: &str,
    extends_type: &typedlua_parser::ast::types::Type,
    access_control: &crate::visitors::AccessControl,
    class_parents: &mut rustc_hash::FxHashMap<String, String>,
    interner: &typedlua_parser::string_interner::StringInterner,
    span: typedlua_parser::span::Span,
) -> Result<String, crate::TypeCheckError> {
    use typedlua_parser::ast::types::TypeKind;

    if let TypeKind::Reference(type_ref) = &extends_type.kind {
        let parent_name = interner.resolve(type_ref.name.node).to_string();

        // Check if parent class is final
        if access_control.is_class_final(&parent_name) {
            return Err(crate::TypeCheckError::new(
                format!("Cannot extend final class {}", parent_name),
                span,
            ));
        }

        // Check for circular inheritance
        class_parents.insert(class_name.to_string(), parent_name.clone());
        if has_circular_inheritance(class_name, class_parents) {
            return Err(crate::TypeCheckError::new(
                format!(
                    "Circular inheritance detected: class '{}' inherits from itself through the inheritance chain",
                    class_name
                ),
                span,
            ));
        }

        Ok(parent_name)
    } else {
        Err(crate::TypeCheckError::new(
            "Class can only extend another class (type reference)",
            span,
        ))
    }
}
