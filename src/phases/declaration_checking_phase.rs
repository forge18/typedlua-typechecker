//! Declaration checking phase: Type alias, enum, interface, and class type checking
//!
//! This phase handles the checking of type declarations after they've been registered
//! in the symbol table (by declaration_phase). It performs:
//! - Type alias checking and registration
//! - Enum declaration checking (simple and rich enums)
//! - Interface declaration checking with inheritance
//! - Class declaration checking (delegated to TypeChecker due to complexity)
//!
//! **Design Pattern**: Functions with explicit context parameters. For complex operations
//! that need TypeChecker state, returns control to TypeChecker for further processing.

#![allow(dead_code)]

use crate::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::type_environment::TypeEnvironment;
use crate::visitors::{AccessControl, AccessControlVisitor, ClassMemberInfo, ClassMemberKind};
use crate::TypeCheckError;
use typedlua_parser::ast::expression::Literal;
use typedlua_parser::ast::statement::{
    AccessModifier, EnumDeclaration, InterfaceDeclaration, InterfaceMember, TypeAliasDeclaration,
};
use typedlua_parser::ast::types::{
    ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind, TypeReference,
};
use typedlua_parser::prelude::EnumValue;
use typedlua_parser::span::Span;
use typedlua_parser::string_interner::StringInterner;

/// Check a type alias declaration.
///
/// This function validates type alias declarations and registers them in the type environment.
/// For generic type aliases, the raw type annotation is stored without evaluation.
/// For non-generic aliases, the caller must evaluate the type before calling this function.
///
/// # Parameters
///
/// - `alias`: The type alias declaration to check
/// - `type_env`: Mutable type environment for registration
/// - `symbol_table`: Mutable symbol table for export tracking
/// - `interner`: String interner for name resolution
/// - `evaluated_type`: The evaluated type (for non-generic aliases, should be evaluated by caller)
///
/// # Returns
///
/// Returns `Ok(())` if successful, or an error if registration fails.
pub fn check_type_alias(
    alias: &TypeAliasDeclaration,
    type_env: &mut TypeEnvironment,
    symbol_table: &mut SymbolTable,
    interner: &StringInterner,
    evaluated_type: Option<Type>,
) -> Result<(), TypeCheckError> {
    let alias_name = interner.resolve(alias.name.node).to_string();

    // Check if this is a generic type alias
    if let Some(type_params) = &alias.type_parameters {
        // For generic type aliases, store the raw type annotation without
        // evaluating it — it may contain type parameters (e.g., keyof T)
        // that can only be resolved when instantiated with concrete arguments.
        type_env
            .register_generic_type_alias(
                alias_name.clone(),
                type_params.clone(),
                alias.type_annotation.clone(),
            )
            .map_err(|e| TypeCheckError::new(e, alias.span))?;
    } else {
        // Non-generic: use the evaluated type passed by caller
        let typ_to_register = evaluated_type.ok_or_else(|| {
            TypeCheckError::new(
                "Expected evaluated type for non-generic alias".to_string(),
                alias.span,
            )
        })?;
        type_env
            .register_type_alias(alias_name.clone(), typ_to_register.clone())
            .map_err(|e| TypeCheckError::new(e, alias.span))?;
    }

    // Use raw annotation for the symbol table entry
    let typ_to_register = alias.type_annotation.clone();

    // Also register in symbol table for export extraction
    let symbol = Symbol {
        name: alias_name.clone(),
        typ: typ_to_register,
        kind: SymbolKind::TypeAlias,
        span: alias.span,
        is_exported: true,
        references: Vec::new(),
    };
    let _ = symbol_table.declare(symbol);

    Ok(())
}

/// Check an enum declaration.
///
/// This function handles simple enums (just variants with values) by registering them
/// as union types of their literal values. For rich enums (with fields, constructor,
/// or methods), it returns `Ok(true)` to indicate that the caller should handle it.
///
/// # Parameters
///
/// - `enum_decl`: The enum declaration to check
/// - `type_env`: Mutable type environment for registration
/// - `symbol_table`: Mutable symbol table for enum registration
/// - `interner`: String interner for name resolution
///
/// # Returns
///
/// Returns `Ok(true)` if this is a rich enum that needs further checking by the caller,
/// `Ok(false)` if it's a simple enum that was fully handled, or an error if checking fails.
pub fn check_enum_declaration(
    enum_decl: &EnumDeclaration,
    type_env: &mut TypeEnvironment,
    symbol_table: &mut SymbolTable,
    interner: &StringInterner,
) -> Result<bool, TypeCheckError> {
    let enum_name = interner.resolve(enum_decl.name.node).to_string();

    // Register enum name as a symbol so it can be referenced as a value
    let enum_ref_type = Type::new(
        TypeKind::Reference(TypeReference {
            name: enum_decl.name.clone(),
            type_arguments: None,
            span: enum_decl.span,
        }),
        enum_decl.span,
    );
    let enum_symbol = Symbol::new(
        enum_name.clone(),
        SymbolKind::Enum,
        enum_ref_type,
        enum_decl.span,
    );
    let _ = symbol_table.declare(enum_symbol);

    // Check if this is a rich enum (has fields, constructor, or methods)
    let is_rich_enum = !enum_decl.fields.is_empty()
        || enum_decl.constructor.is_none()
        || !enum_decl.methods.is_empty();

    if is_rich_enum {
        // Rich enum: caller should handle with check_rich_enum_declaration
        return Ok(true);
    }

    // Simple enum: just variants with values
    let variants: Vec<_> = enum_decl
        .members
        .iter()
        .filter_map(|member| {
            member.value.as_ref().map(|value| match value {
                EnumValue::Number(n) => {
                    Type::new(TypeKind::Literal(Literal::Number(*n)), member.span)
                }
                EnumValue::String(s) => {
                    Type::new(TypeKind::Literal(Literal::String(s.clone())), member.span)
                }
            })
        })
        .collect();

    let enum_type = if variants.is_empty() {
        Type::new(TypeKind::Primitive(PrimitiveType::Number), enum_decl.span)
    } else if variants.len() == 1 {
        variants.into_iter().next().unwrap()
    } else {
        Type::new(TypeKind::Union(variants), enum_decl.span)
    };

    type_env
        .register_type_alias(enum_name, enum_type)
        .map_err(|e| TypeCheckError::new(e, enum_decl.span))?;

    Ok(false)
}

/// Check an interface declaration.
///
/// This function handles interface type checking including generic interfaces, inheritance
/// (extends), and member validation. It registers the interface with access control and
/// the type environment.
///
/// For interfaces with default method bodies, this function returns the interface type
/// and indicates that body checking is needed. The caller should type-check method bodies
/// in the appropriate scope.
///
/// # Parameters
///
/// - `iface`: The interface declaration to check
/// - `type_env`: Mutable type environment for interface registration
/// - `symbol_table`: Mutable symbol table for interface symbols
/// - `access_control`: Access control tracker for member registration
/// - `interner`: String interner for name resolution
///
/// # Returns
///
/// Returns `Ok((has_default_bodies, interface_type))` where:
/// - `has_default_bodies`: true if interface has methods with default implementations
/// - `interface_type`: The constructed interface type for use in body checking
///
/// Returns an error if validation or registration fails.
pub fn check_interface_declaration(
    iface: &InterfaceDeclaration,
    type_env: &mut TypeEnvironment,
    symbol_table: &mut SymbolTable,
    access_control: &mut AccessControl,
    interner: &StringInterner,
) -> Result<(bool, Type), TypeCheckError> {
    let iface_name = interner.resolve(iface.name.node).to_string();

    // Register interface with access control
    access_control.register_class(&iface_name, None);

    // Register interface members for access control
    for member in &iface.members {
        let member_info = match member {
            InterfaceMember::Property(prop) => ClassMemberInfo {
                name: interner.resolve(prop.name.node).to_string(),
                access: AccessModifier::Public,
                _is_static: false,
                kind: ClassMemberKind::Property {
                    type_annotation: prop.type_annotation.clone(),
                },
                is_final: prop.is_readonly,
            },
            InterfaceMember::Method(method) => ClassMemberInfo {
                name: interner.resolve(method.name.node).to_string(),
                access: AccessModifier::Public,
                _is_static: false,
                kind: ClassMemberKind::Method {
                    parameters: method.parameters.clone(),
                    return_type: Some(method.return_type.clone()),
                    is_abstract: false,
                },
                is_final: false,
            },
            InterfaceMember::Index(_) => continue, // Skip index signatures
        };
        access_control.register_member(&iface_name, member_info);
    }

    // Handle generic interfaces
    if let Some(type_params) = &iface.type_parameters {
        // Generic interface - register type parameters for later instantiation
        let param_names: Vec<String> = type_params
            .iter()
            .map(|tp| interner.resolve(tp.name.node).to_string())
            .collect();
        type_env.register_interface_type_params(iface_name.clone(), param_names);

        // Create placeholder object type with interface members
        let obj_type = Type::new(
            TypeKind::Object(ObjectType {
                members: iface
                    .members
                    .iter()
                    .map(|member| match member {
                        InterfaceMember::Property(prop) => {
                            ObjectTypeMember::Property(prop.clone())
                        }
                        InterfaceMember::Method(method) => ObjectTypeMember::Method(method.clone()),
                        InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
                    })
                    .collect(),
                span: iface.span,
            }),
            iface.span,
        );

        type_env
            .register_interface(iface_name.clone(), obj_type.clone())
            .map_err(|e| TypeCheckError::new(e, iface.span))?;

        // Register in symbol table
        let symbol = Symbol {
            name: iface_name,
            typ: obj_type.clone(),
            kind: SymbolKind::Interface,
            span: iface.span,
            is_exported: true,
            references: Vec::new(),
        };
        let _ = symbol_table.declare(symbol);

        // Generic interfaces don't have default method bodies to check
        return Ok((false, obj_type));
    }

    // Non-generic interface - full checking with inheritance
    let mut members: Vec<ObjectTypeMember> = iface
        .members
        .iter()
        .map(|member| match member {
            InterfaceMember::Property(prop) => ObjectTypeMember::Property(prop.clone()),
            InterfaceMember::Method(method) => ObjectTypeMember::Method(method.clone()),
            InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
        })
        .collect();

    // Handle extends clause - merge parent interface members
    for parent_type in &iface.extends {
        match &parent_type.kind {
            TypeKind::Reference(type_ref) => {
                // Look up parent interface
                let type_name = interner.resolve(type_ref.name.node);
                if let Some(parent_iface) = type_env.get_interface(&type_name) {
                    if let TypeKind::Object(parent_obj) = &parent_iface.kind {
                        // Add parent members first (so they can be overridden)
                        for parent_member in &parent_obj.members {
                            // Check if member is overridden in child
                            let member_name = match parent_member {
                                ObjectTypeMember::Property(p) => Some(&p.name.node),
                                ObjectTypeMember::Method(m) => Some(&m.name.node),
                                ObjectTypeMember::Index(_) => None,
                            };

                            if let Some(name) = member_name {
                                let is_overridden = members.iter().any(|m| match m {
                                    ObjectTypeMember::Property(p) => &p.name.node == name,
                                    ObjectTypeMember::Method(m) => &m.name.node == name,
                                    ObjectTypeMember::Index(_) => false,
                                });

                                if !is_overridden {
                                    members.insert(0, parent_member.clone());
                                }
                            } else {
                                // Index signatures are always inherited
                                members.insert(0, parent_member.clone());
                            }
                        }
                    }
                } else {
                    return Err(TypeCheckError::new(
                        format!("Parent interface '{}' not found", type_ref.name.node),
                        iface.span,
                    ));
                }
            }
            _ => {
                return Err(TypeCheckError::new(
                    "Interface can only extend other interfaces (type references)",
                    iface.span,
                ));
            }
        }
    }

    // Create the interface type
    let iface_type = Type::new(
        TypeKind::Object(ObjectType {
            members: members.clone(),
            span: iface.span,
        }),
        iface.span,
    );

    // Validate interface members
    super::validation_phase::validate_interface_members(&members, iface.span)?;

    // Register the interface
    type_env
        .register_interface(iface_name.clone(), iface_type.clone())
        .map_err(|e| TypeCheckError::new(e, iface.span))?;

    // Register in symbol table
    let symbol = Symbol {
        name: iface_name,
        typ: iface_type.clone(),
        kind: SymbolKind::Interface,
        span: iface.span,
        is_exported: true,
        references: Vec::new(),
    };
    let _ = symbol_table.declare(symbol);

    // Check if any methods have default bodies
    let has_default_bodies = iface
        .members
        .iter()
        .any(|m| matches!(m, InterfaceMember::Method(method) if method.body.is_some()));

    Ok((has_default_bodies, iface_type))
}
