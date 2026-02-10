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

use crate::core::type_environment::TypeEnvironment;
use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::visitors::{AccessControl, AccessControlVisitor, ClassMemberInfo, ClassMemberKind};
use crate::TypeCheckError;
use luanext_parser::ast::expression::Literal;
use luanext_parser::ast::statement::{
    AccessModifier, ClassDeclaration, ClassMember, EnumDeclaration, InterfaceDeclaration,
    InterfaceMember, TypeAliasDeclaration,
};
use tracing::debug;
use luanext_parser::ast::types::{
    ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind, TypeReference,
};
use luanext_parser::prelude::EnumValue;
use luanext_parser::string_interner::StringInterner;

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
pub fn check_type_alias<'arena>(
    alias: &TypeAliasDeclaration<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
    evaluated_type: Option<Type<'arena>>,
) -> Result<(), TypeCheckError> {
    let alias_name = interner.resolve(alias.name.node).to_string();

    // Check if this is a generic type alias
    if let Some(type_params) = alias.type_parameters {
        // For generic type aliases, store the raw type annotation without
        // evaluating it — it may contain type parameters (e.g., keyof T)
        // that can only be resolved when instantiated with concrete arguments.
        type_env
            .register_generic_type_alias(
                alias_name.clone(),
                type_params.to_vec(),
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
pub fn check_enum_declaration<'arena>(
    arena: &'arena bumpalo::Bump,
    enum_decl: &EnumDeclaration<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
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
        Type::new(
            TypeKind::Union(arena.alloc_slice_fill_iter(variants)),
            enum_decl.span,
        )
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
pub fn check_interface_declaration<'arena>(
    arena: &'arena bumpalo::Bump,
    iface: &InterfaceDeclaration<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    access_control: &mut AccessControl<'arena>,
    interner: &StringInterner,
) -> Result<(bool, Type<'arena>), TypeCheckError> {
    let iface_name = interner.resolve(iface.name.node).to_string();

    // Handle forward declarations: register interface name for mutual references
    // but skip member processing since forward declarations have no members
    if iface.is_forward_declaration {
        debug!("Processing forward declaration for interface: {}", iface_name);

        // Register interface with access control for forward references
        access_control.register_class(&iface_name, None);

        // Create placeholder interface type for forward declaration
        let empty_object = Type::new(
            TypeKind::Object(ObjectType {
                members: arena.alloc_slice_fill_iter(vec![]),
                span: iface.span,
            }),
            iface.span,
        );

        // Register in type environment
        type_env
            .register_interface(iface_name.clone(), empty_object.clone())
            .map_err(|e| TypeCheckError::new(e, iface.span))?;

        // Register in symbol table
        let symbol = Symbol::new(iface_name.clone(), SymbolKind::Interface, empty_object.clone(), iface.span);
        symbol_table.declare(symbol)
            .map_err(|e| TypeCheckError::new(e, iface.span))?;

        return Ok((true, empty_object));
    }

    // Register interface with access control
    access_control.register_class(&iface_name, None);

    // Register interface members for access control
    for member in iface.members.iter() {
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
                    parameters: method.parameters.to_vec(),
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
    if let Some(type_params) = iface.type_parameters {
        // Generic interface - register type parameters for later instantiation
        let param_names: Vec<String> = type_params
            .iter()
            .map(|tp| interner.resolve(tp.name.node).to_string())
            .collect();
        type_env.register_interface_type_params(iface_name.clone(), param_names);

        // Create placeholder object type with interface members
        let members_vec: Vec<ObjectTypeMember<'arena>> = iface
            .members
            .iter()
            .map(|member| match member {
                InterfaceMember::Property(prop) => ObjectTypeMember::Property(prop.clone()),
                InterfaceMember::Method(method) => ObjectTypeMember::Method(method.clone()),
                InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
            })
            .collect();
        let obj_type = Type::new(
            TypeKind::Object(ObjectType {
                members: arena.alloc_slice_fill_iter(members_vec),
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
    let mut members: Vec<ObjectTypeMember<'arena>> = iface
        .members
        .iter()
        .map(|member| match member {
            InterfaceMember::Property(prop) => ObjectTypeMember::Property(prop.clone()),
            InterfaceMember::Method(method) => ObjectTypeMember::Method(method.clone()),
            InterfaceMember::Index(index) => ObjectTypeMember::Index(index.clone()),
        })
        .collect();

    // Handle extends clause - merge parent interface members
    for parent_type in iface.extends.iter() {
        match &parent_type.kind {
            TypeKind::Reference(type_ref) => {
                // Look up parent interface
                let type_name = interner.resolve(type_ref.name.node);
                if let Some(parent_iface) = type_env.get_interface(&type_name) {
                    if let TypeKind::Object(parent_obj) = &parent_iface.kind {
                        // Add parent members first (so they can be overridden)
                        for parent_member in parent_obj.members.iter() {
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
            members: arena.alloc_slice_fill_iter(members.clone()),
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

/// Check a rich enum declaration with fields, constructor, and methods.
///
/// Rich enums have additional complexity beyond simple enums - they include fields,
/// constructors, and methods. This function handles registration of all enum components
/// with access control and type environment.
///
/// Returns the enum's self type which the caller should use for checking constructor
/// and method bodies in the appropriate scope.
///
/// # Parameters
///
/// - `enum_decl`: The rich enum declaration to check
/// - `type_env`: Mutable type environment for type registration
/// - `access_control`: Access control tracker for member registration
/// - `interner`: String interner for name resolution
///
/// # Returns
///
/// Returns `Ok(enum_self_type)` with the enum's type for body checking, or an error if
/// registration or validation fails. The caller should use this type to check constructor
/// and method bodies.
pub fn check_rich_enum_declaration<'arena>(
    enum_decl: &EnumDeclaration<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    access_control: &mut AccessControl<'arena>,
    interner: &StringInterner,
) -> Result<Type<'arena>, TypeCheckError> {
    use rustc_hash::FxHashMap;

    let enum_name = interner.resolve(enum_decl.name.node).to_string();

    // Register rich enum with access control so its members can be tracked
    access_control.register_class(&enum_name, None);

    // Register enum fields as members for access control
    for field in enum_decl.fields.iter() {
        let field_info = ClassMemberInfo {
            name: interner.resolve(field.name.node).to_string(),
            access: AccessModifier::Public,
            _is_static: false,
            kind: ClassMemberKind::Property {
                type_annotation: field.type_annotation.clone(),
            },
            is_final: false,
        };
        access_control.register_member(&enum_name, field_info);
    }

    let mut member_types = FxHashMap::default();
    for (i, member) in enum_decl.members.iter().enumerate() {
        let member_name_str = interner.resolve(member.name.node).to_string();
        let member_type_name = format!("{}.{}", enum_name, member_name_str);
        let member_type = Type::new(
            TypeKind::Literal(Literal::String(member_name_str.clone())),
            member.span,
        );
        type_env
            .register_type_alias(member_type_name, member_type.clone())
            .map_err(|e| TypeCheckError::new(e, member.span))?;
        member_types.insert(i, member_type.clone());

        // Register enum variant as a static public property for member access
        access_control.register_member(
            &enum_name,
            ClassMemberInfo {
                name: member_name_str,
                access: AccessModifier::Public,
                _is_static: true,
                kind: ClassMemberKind::Property {
                    type_annotation: member_type,
                },
                is_final: true,
            },
        );
    }

    // Register enum methods as members for access control
    for method in enum_decl.methods.iter() {
        let method_name = interner.resolve(method.name.node).to_string();
        access_control.register_member(
            &enum_name,
            ClassMemberInfo {
                name: method_name,
                access: AccessModifier::Public,
                _is_static: false,
                kind: ClassMemberKind::Method {
                    parameters: method.parameters.to_vec(),
                    return_type: method.return_type.clone(),
                    is_abstract: false,
                },
                is_final: false,
            },
        );
    }

    let enum_type = Type::new(
        TypeKind::Reference(TypeReference {
            name: enum_decl.name.clone(),
            type_arguments: None,
            span: enum_decl.span,
        }),
        enum_decl.span,
    );

    type_env
        .register_type_alias(enum_name, enum_type.clone())
        .map_err(|e| TypeCheckError::new(e, enum_decl.span))?;

    Ok(enum_type)
}

/// Register a class symbol and handle abstract class registration.
///
/// This is a focused function that handles the basic class registration in the symbol table
/// and type environment. It does NOT handle members, inheritance, or other complex logic.
///
/// # Returns
///
/// Returns the class type for use in further checking.
pub fn register_class_symbol<'arena>(
    class_decl: &ClassDeclaration<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    type_env: &mut TypeEnvironment<'arena>,
    class_type_params: &mut rustc_hash::FxHashMap<
        String,
        Vec<luanext_parser::ast::statement::TypeParameter<'arena>>,
    >,
    interner: &StringInterner,
) -> Result<Type<'arena>, TypeCheckError> {
    let class_name = interner.resolve(class_decl.name.node).to_string();

    // Register the class name as a symbol in the symbol table so `new ClassName()` works
    let class_type = Type::new(
        TypeKind::Reference(TypeReference {
            name: class_decl.name.clone(),
            type_arguments: None,
            span: class_decl.span,
        }),
        class_decl.span,
    );
    let class_symbol = Symbol::new(
        class_name.clone(),
        SymbolKind::Class,
        class_type.clone(),
        class_decl.span,
    );
    let _ = symbol_table.declare(class_symbol);

    // Register abstract class
    if class_decl.is_abstract {
        type_env.register_abstract_class(class_name.clone());
    }

    // Store type parameters for this class (needed for generic override checking)
    if let Some(type_params) = class_decl.type_parameters {
        class_type_params.insert(class_name, type_params.to_vec());
    }

    Ok(class_type)
}

/// Extract class member information for access control registration.
///
/// This function processes all class members (properties, methods, getters, setters, operators)
/// from the class declaration to build a list of ClassMemberInfo structures for
/// access control registration.
///
/// # Parameters
///
/// - `class_decl`: The class declaration containing members
/// - `interner`: String interner for resolving identifiers
///
/// # Returns
///
/// Returns a vector of ClassMemberInfo structures ready for access control registration.
/// Note: Primary constructor properties must be added separately by the caller since
/// they require special handling for `is_readonly` field mapping.
pub fn extract_class_member_infos<'arena>(
    class_decl: &ClassDeclaration<'arena>,
    interner: &StringInterner,
) -> Vec<ClassMemberInfo<'arena>> {
    use crate::helpers::type_utilities::operator_kind_name;
    let mut member_infos = Vec::new();

    // Add regular class members
    for member in class_decl.members.iter() {
        match member {
            ClassMember::Property(prop) => {
                member_infos.push(ClassMemberInfo {
                    name: interner.resolve(prop.name.node).to_string(),
                    access: prop.access.unwrap_or(AccessModifier::Public),
                    _is_static: prop.is_static,
                    kind: ClassMemberKind::Property {
                        type_annotation: prop.type_annotation.clone(),
                    },
                    is_final: false,
                });
            }
            ClassMember::Method(method) => {
                member_infos.push(ClassMemberInfo {
                    name: interner.resolve(method.name.node).to_string(),
                    access: method.access.unwrap_or(AccessModifier::Public),
                    _is_static: method.is_static,
                    kind: ClassMemberKind::Method {
                        parameters: method.parameters.to_vec(),
                        return_type: method.return_type.clone(),
                        is_abstract: method.is_abstract,
                    },
                    is_final: method.is_final,
                });
            }
            ClassMember::Getter(getter) => {
                member_infos.push(ClassMemberInfo {
                    name: interner.resolve(getter.name.node).to_string(),
                    access: getter.access.unwrap_or(AccessModifier::Public),
                    _is_static: getter.is_static,
                    kind: ClassMemberKind::Getter {
                        return_type: getter.return_type.clone(),
                    },
                    is_final: false,
                });
            }
            ClassMember::Setter(setter) => {
                member_infos.push(ClassMemberInfo {
                    name: interner.resolve(setter.name.node).to_string(),
                    access: setter.access.unwrap_or(AccessModifier::Public),
                    _is_static: setter.is_static,
                    kind: ClassMemberKind::Setter {
                        parameter_type: setter.parameter.type_annotation.clone().unwrap_or_else(
                            || Type::new(TypeKind::Primitive(PrimitiveType::Unknown), setter.span),
                        ),
                    },
                    is_final: false,
                });
            }
            ClassMember::Constructor(_) => {
                // Constructor doesn't have access modifiers for member access
            }
            ClassMember::Operator(op) => {
                let op_name = operator_kind_name(&op.operator);
                member_infos.push(ClassMemberInfo {
                    name: op_name,
                    access: op.access.unwrap_or(AccessModifier::Public),
                    _is_static: false,
                    kind: ClassMemberKind::Operator {
                        operator: op.operator,
                        parameters: op.parameters.to_vec(),
                        return_type: op.return_type.clone(),
                    },
                    is_final: false,
                });
            }
        }
    }

    member_infos
}

/// Classify a class member error as critical or non-critical.
///
/// Critical errors should fail compilation immediately, while non-critical errors
/// can be converted to warnings to prevent cascading failures.
///
/// # Parameters
///
/// - `error_message`: The error message to classify
///
/// # Returns
///
/// Returns `true` if the error is critical and should fail compilation, `false` otherwise.
pub fn is_critical_member_error(error_message: &str) -> bool {
    (error_message.contains("Abstract method") && error_message.contains("abstract class"))
        || error_message.contains("one constructor")
        || error_message.contains("Decorators require decorator features")
        || error_message.contains("Cannot override final method")
        || error_message.contains("is incompatible with parent")
        || error_message.contains("must implement abstract method")
        || error_message.contains("uses override but class")
        || error_message.contains("marked as override but parent class does not have this method")
        || error_message.contains("Return type mismatch")
        || error_message.contains("is private and only accessible")
        || error_message.contains("is protected and only accessible")
        || error_message.contains("operators can have 0 parameters")
        || error_message.contains("Binary operator must have exactly")
        || error_message.contains("Operator must have 0, 1, or 2")
        || error_message.contains("must have exactly 2 parameters")
        || error_message.contains("must return 'boolean'")
}

/// Register class type parameters in the type environment.
///
/// Type parameters from a generic class declaration are registered as type aliases
/// in the type environment, scoped to the class body. Any existing type aliases
/// with the same name are removed first.
///
/// # Parameters
///
/// - `type_params`: Optional slice of type parameters from the class declaration
/// - `type_env`: Mutable type environment for registration
/// - `interner`: String interner for resolving parameter names
///
/// # Returns
///
/// Returns `Ok(())` if successful, or an error if registration fails.
pub fn register_class_type_parameters(
    type_params: Option<&[luanext_parser::ast::statement::TypeParameter]>,
    type_env: &mut crate::core::type_environment::TypeEnvironment,
    interner: &StringInterner,
) -> Result<(), crate::TypeCheckError> {
    if let Some(type_params) = type_params {
        for type_param in type_params {
            let param_name = interner.resolve(type_param.name.node).to_string();
            let param_type = Type::new(
                TypeKind::Reference(TypeReference {
                    name: type_param.name.clone(),
                    type_arguments: None,
                    span: type_param.span,
                }),
                type_param.span,
            );

            // Remove any existing type alias with this name (from a previous generic class)
            // then register fresh. Type params are scoped to the class body.
            type_env.remove_type_alias(&param_name);
            type_env
                .register_type_alias(param_name, param_type)
                .map_err(|e| crate::TypeCheckError::new(e, type_param.span))?;
        }
    }
    Ok(())
}

/// Register class-implements relationships in type environment and access control.
///
/// This function extracts interface names from the class's implements clause and
/// registers them with both the type environment (for type checking) and access
/// control (for member lookup).
///
/// # Parameters
///
/// - `class_name`: Name of the class
/// - `implements`: Vector of interface types that the class implements
/// - `type_env`: Mutable type environment for registration
/// - `access_control`: Mutable access control for member lookup
/// - `interner`: String interner for resolving interface names
pub fn register_class_implements<'arena>(
    class_name: String,
    implements: Vec<Type<'arena>>,
    type_env: &mut crate::core::type_environment::TypeEnvironment<'arena>,
    access_control: &mut crate::visitors::AccessControl<'arena>,
    interner: &StringInterner,
) {
    if implements.is_empty() {
        return;
    }

    // Register with type environment for type checking
    type_env.register_class_implements(class_name.clone(), implements.clone());

    // Extract interface names and register with access control for member lookup
    let interface_names: Vec<String> = implements
        .iter()
        .map(|t| {
            // Extract the interface name from the type
            match &t.kind {
                TypeKind::Reference(ref_type) => interner.resolve(ref_type.name.node).to_string(),
                _ => format!("{:?}", t),
            }
        })
        .collect();
    access_control.register_class_implements(&class_name, interface_names);
}

/// Register function type parameters with duplicate checking.
///
/// This function validates that type parameters are unique and registers them
/// in the type environment along with any constraints.
///
/// # Parameters
///
/// - `type_params`: Optional slice of type parameters from the function declaration
/// - `type_env`: Mutable type environment for registration
/// - `interner`: String interner for resolving parameter names
///
/// # Returns
///
/// Returns `Ok(())` if successful, or an error if duplicate parameters are found
/// or registration fails.
pub fn register_function_type_parameters<'arena>(
    type_params: Option<&[luanext_parser::ast::statement::TypeParameter<'arena>]>,
    type_env: &mut crate::core::type_environment::TypeEnvironment<'arena>,
    interner: &StringInterner,
) -> Result<(), crate::TypeCheckError> {
    let Some(type_params) = type_params else {
        return Ok(());
    };

    // Check for duplicate type parameters
    let mut seen_params = std::collections::HashSet::new();
    for type_param in type_params {
        let param_name = interner.resolve(type_param.name.node).to_string();
        if !seen_params.insert(param_name.clone()) {
            return Err(crate::TypeCheckError::new(
                format!("Duplicate type parameter '{}'", param_name),
                type_param.span,
            ));
        }
    }

    // Register type parameters in type environment
    for type_param in type_params {
        let param_name = interner.resolve(type_param.name.node).to_string();
        let param_type = Type::new(
            TypeKind::Reference(TypeReference {
                name: type_param.name.clone(),
                type_arguments: None,
                span: type_param.span,
            }),
            type_param.span,
        );

        // Type parameters are treated as local types in the function scope
        type_env.remove_type_alias(&param_name);
        type_env
            .register_type_alias(param_name.clone(), param_type)
            .map_err(|e| crate::TypeCheckError::new(e, type_param.span))?;

        // Register constraint if present (e.g., T implements Identifiable)
        if let Some(constraint) = &type_param.constraint {
            type_env.register_type_param_constraint(param_name, (**constraint).clone());
        }
    }

    Ok(())
}

/// Instantiate a generic interface with type arguments.
///
/// For generic interfaces like `Comparable<T>`, this function takes the interface type
/// and substitutes all type parameters with concrete type arguments, producing an
/// instantiated interface like `Comparable<number>`.
///
/// This handles the complex nested type substitution required for generic interface
/// implementation checking.
///
/// # Parameters
///
/// - `interface`: The generic interface type to instantiate
/// - `type_args`: The type arguments to substitute
/// - `interface_name`: Name of the interface for substitution context
/// - `substitute_fn`: Callback to perform type argument substitution
///
/// # Returns
///
/// Returns the instantiated interface type with all type parameters replaced.
pub fn instantiate_generic_interface<'arena, F>(
    arena: &'arena bumpalo::Bump,
    interface: Type<'arena>,
    type_args: &[Type<'arena>],
    interface_name: &str,
    substitute_fn: F,
) -> Type<'arena>
where
    F: Fn(&Type<'arena>, &[Type<'arena>], &str) -> Type<'arena>,
{
    if let TypeKind::Object(obj) = &interface.kind {
        use luanext_parser::ast::statement::{MethodSignature, PropertySignature};
        let new_members: Vec<ObjectTypeMember<'arena>> = obj
            .members
            .iter()
            .map(|member| match member {
                ObjectTypeMember::Method(method) => {
                    let new_return_type =
                        substitute_fn(&method.return_type, type_args, interface_name);
                    let new_params: Vec<_> = method
                        .parameters
                        .iter()
                        .map(|param| {
                            let new_type_ann = param
                                .type_annotation
                                .as_ref()
                                .map(|t| substitute_fn(t, type_args, interface_name));
                            luanext_parser::ast::statement::Parameter {
                                type_annotation: new_type_ann,
                                ..param.clone()
                            }
                        })
                        .collect();
                    ObjectTypeMember::Method(MethodSignature {
                        parameters: arena.alloc_slice_fill_iter(new_params),
                        return_type: new_return_type,
                        ..method.clone()
                    })
                }
                ObjectTypeMember::Property(prop) => {
                    let new_type = substitute_fn(&prop.type_annotation, type_args, interface_name);
                    ObjectTypeMember::Property(PropertySignature {
                        type_annotation: new_type,
                        ..prop.clone()
                    })
                }
                other => other.clone(),
            })
            .collect();
        Type::new(
            TypeKind::Object(ObjectType {
                members: arena.alloc_slice_fill_iter(new_members),
                span: obj.span,
            }),
            interface.span,
        )
    } else {
        interface
    }
}
