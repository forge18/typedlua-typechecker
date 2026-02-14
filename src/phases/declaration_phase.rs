//! Declaration phase: Symbol registration and declaration handling
//!
//! This phase handles:
//! - Registering function signatures in the symbol table
//! - Declaring variables, constants, and type aliases
//! - Declaring classes, interfaces, and enums
//! - Tracking declarations for forward references
//!
//! **Design Pattern**: Stateless phase functions that take explicit context parameters.
//! The phase focuses on DECLARING symbols (adding them to the symbol table) before
//! full type checking occurs. This enables forward references and proper scope resolution.

use crate::utils::symbol_table::{Symbol, SymbolKind, SymbolTable};
use crate::TypeCheckError;
use bumpalo::Bump;
use luanext_parser::ast::pattern::{ArrayPatternElement, Pattern, PatternWithDefault};
use luanext_parser::ast::statement::{
    DeclareConstStatement, DeclareFunctionStatement, DeclareNamespaceStatement,
    FunctionDeclaration, MethodSignature, PropertySignature, Statement,
};
use luanext_parser::ast::types::{
    FunctionType, ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind,
};
use luanext_parser::span::Span;
use luanext_parser::string_interner::StringInterner;

/// Register a function signature in the symbol table.
///
/// This function creates a symbol for a function declaration based on its signature
/// (name, parameters, return type, type parameters) and adds it to the symbol table.
/// This allows the function to be referenced before its body is type-checked.
///
/// This is called during the declaration phase (PASS 1), before checking the function body.
///
/// # Validation
///
/// - Type predicate return types: Validates that the parameter name in a type predicate
///   actually matches one of the function's parameters
/// - Return type: Defaults to `void` if no return type is specified
///
/// # Parameters
///
/// - `decl`: The function declaration to register
/// - `symbol_table`: Mutable symbol table to add the function symbol
/// - `interner`: String interner for resolving the function name
///
/// # Returns
///
/// Returns `Ok(())` if the function was successfully registered, or an error if
/// validation fails or a symbol with the same name already exists in the current scope.
pub fn register_function_signature<'arena>(
    decl: &FunctionDeclaration<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
    arena: &'arena Bump,
) -> Result<(), TypeCheckError> {
    // Validate type predicate return types
    if let Some(return_type) = &decl.return_type {
        if let TypeKind::TypePredicate(predicate) = &return_type.kind {
            // Validate that the parameter name in the predicate matches one of the function parameters
            let param_exists = decl.parameters.iter().any(|param| {
                if let Pattern::Identifier(ident) = &param.pattern {
                    ident.node == predicate.parameter_name.node
                } else {
                    false
                }
            });

            if !param_exists {
                return Err(TypeCheckError::new(
                    format!(
                        "Type predicate parameter '{}' does not match any function parameter",
                        predicate.parameter_name.node
                    ),
                    predicate.span,
                ));
            }
        }
    }

    // Create function type
    let return_type = decl
        .return_type
        .clone()
        .unwrap_or_else(|| Type::new(TypeKind::Primitive(PrimitiveType::Void), decl.span));
    let func_type = Type::new(
        TypeKind::Function(FunctionType {
            type_parameters: decl.type_parameters,
            parameters: decl.parameters,
            return_type: arena.alloc(return_type),
            throws: decl.throws,
            span: decl.span,
        }),
        decl.span,
    );

    // Declare function in symbol table
    let symbol = Symbol::new(
        interner.resolve(decl.name.node).to_string(),
        SymbolKind::Function,
        func_type,
        decl.span,
    );

    symbol_table
        .declare(symbol)
        .map_err(|e| TypeCheckError::new(e, decl.span))
}

/// Declare symbols from a destructuring pattern.
///
/// This function recursively traverses a pattern (identifier, array destructuring,
/// object destructuring, or-patterns) and declares each binding in the symbol table.
///
/// # Pattern Types
///
/// - **Identifier**: `let x: number` - declares `x`
/// - **Array**: `let [a, b, ...rest] = array` - declares `a`, `b`, `rest`
/// - **Object**: `let {x, y: z} = obj` - declares `x`, `z`
/// - **Or-pattern**: `let (a | b) = value` - declares from first alternative
/// - **Literals/Wildcards**: No declarations
///
/// # Parameters
///
/// - `pattern`: The pattern to extract bindings from
/// - `typ`: The type to assign to the bindings
/// - `kind`: Symbol kind (Variable, Const, etc.)
/// - `span`: Source location for error reporting
/// - `symbol_table`: Mutable symbol table
/// - `interner`: String interner for resolving names
pub fn declare_pattern<'arena>(
    pattern: &Pattern,
    typ: Type<'arena>,
    kind: SymbolKind,
    span: Span,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
    arena: &'arena Bump,
) -> Result<(), TypeCheckError> {
    match pattern {
        Pattern::Identifier(ident) => {
            let symbol = Symbol::new(interner.resolve(ident.node).to_string(), kind, typ, span);
            symbol_table
                .declare(symbol)
                .map_err(|e| TypeCheckError::new(e, span))?;
            Ok(())
        }
        Pattern::Array(array_pattern) => {
            // Extract element type from array or tuple type
            match &typ.kind {
                TypeKind::Array(elem_type) => {
                    for elem in array_pattern.elements.iter() {
                        match elem {
                            ArrayPatternElement::Pattern(PatternWithDefault {
                                pattern: pat,
                                ..
                            }) => {
                                declare_pattern(
                                    pat,
                                    (*elem_type).clone(),
                                    kind,
                                    span,
                                    symbol_table,
                                    interner,
                                    arena,
                                )?;
                            }
                            ArrayPatternElement::Rest(ident) => {
                                // Rest gets array type
                                let array_type = Type::new(TypeKind::Array(elem_type), span);
                                let symbol = Symbol::new(
                                    interner.resolve(ident.node).to_string(),
                                    kind,
                                    array_type,
                                    span,
                                );
                                symbol_table
                                    .declare(symbol)
                                    .map_err(|e| TypeCheckError::new(e, span))?;
                            }
                            ArrayPatternElement::Hole => {
                                // Holes don't declare symbols
                            }
                        }
                    }
                }
                TypeKind::Tuple(elem_types) => {
                    // Tuple types: each element has a specific type
                    let mut type_index = 0;
                    for elem in array_pattern.elements.iter() {
                        match elem {
                            ArrayPatternElement::Pattern(PatternWithDefault {
                                pattern: pat,
                                ..
                            }) => {
                                let elem_type = if type_index < elem_types.len() {
                                    elem_types[type_index].clone()
                                } else {
                                    Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)
                                };
                                declare_pattern(
                                    pat,
                                    elem_type,
                                    kind,
                                    span,
                                    symbol_table,
                                    interner,
                                    arena,
                                )?;
                                type_index += 1;
                            }
                            ArrayPatternElement::Rest(ident) => {
                                // Rest gets array of remaining tuple element types
                                let remaining = &elem_types[type_index..];
                                let rest_type =
                                    if remaining.is_empty() {
                                        Type::new(
                                            TypeKind::Array(arena.alloc(Type::new(
                                                TypeKind::Primitive(PrimitiveType::Unknown),
                                                span,
                                            ))),
                                            span,
                                        )
                                    } else if remaining.len() == 1 {
                                        Type::new(
                                            TypeKind::Array(arena.alloc(remaining[0].clone())),
                                            span,
                                        )
                                    } else {
                                        let union_types = arena.alloc_slice_clone(remaining);
                                        Type::new(
                                            TypeKind::Array(arena.alloc(Type::new(
                                                TypeKind::Union(union_types),
                                                span,
                                            ))),
                                            span,
                                        )
                                    };
                                let symbol = Symbol::new(
                                    interner.resolve(ident.node).to_string(),
                                    kind,
                                    rest_type,
                                    span,
                                );
                                symbol_table
                                    .declare(symbol)
                                    .map_err(|e| TypeCheckError::new(e, span))?;
                            }
                            ArrayPatternElement::Hole => {
                                type_index += 1;
                            }
                        }
                    }
                }
                TypeKind::Union(variants) => {
                    // For unions containing array types, extract the element type
                    // e.g., Union(Array(T1), Array(T2)) -> elements get Union(T1, T2)
                    let mut array_elem_types = Vec::new();
                    for variant in variants.iter() {
                        match &variant.kind {
                            TypeKind::Array(elem) => {
                                array_elem_types.push((*elem).clone());
                            }
                            TypeKind::Tuple(_) => {
                                // If any variant is a tuple, delegate to tuple handling
                                return declare_pattern(
                                    pattern,
                                    variant.clone(),
                                    kind,
                                    span,
                                    symbol_table,
                                    interner,
                                    arena,
                                );
                            }
                            _ => {}
                        }
                    }
                    if array_elem_types.is_empty() {
                        return Err(TypeCheckError::new(
                            "Cannot destructure non-array type",
                            span,
                        ));
                    }
                    // Merge element types into a single union or use directly
                    let merged_elem = if array_elem_types.len() == 1 {
                        array_elem_types.into_iter().next().unwrap()
                    } else {
                        let types = arena.alloc_slice_fill_iter(array_elem_types);
                        Type::new(TypeKind::Union(types), span)
                    };
                    let array_type = Type::new(TypeKind::Array(arena.alloc(merged_elem)), span);
                    return declare_pattern(
                        pattern,
                        array_type,
                        kind,
                        span,
                        symbol_table,
                        interner,
                        arena,
                    );
                }
                _ => {
                    return Err(TypeCheckError::new(
                        "Cannot destructure non-array type",
                        span,
                    ));
                }
            }
            Ok(())
        }
        Pattern::Object(obj_pattern) => {
            // Handle Union types by extracting the first Object variant
            let typ = if let TypeKind::Union(variants) = &typ.kind {
                variants
                    .iter()
                    .find(|v| matches!(v.kind, TypeKind::Object(_)))
                    .cloned()
                    .unwrap_or(typ)
            } else {
                typ
            };

            if let TypeKind::Object(obj_type) = &typ.kind {
                // Collect the set of destructured property names for rest computation
                let destructured_keys: Vec<_> =
                    obj_pattern.properties.iter().map(|p| p.key.node).collect();

                for prop_pattern in obj_pattern.properties.iter() {
                    // For computed properties, we can't statically resolve the key,
                    // so use Unknown type for the value
                    let prop_type = if prop_pattern.computed_key.is_some() {
                        Type::new(TypeKind::Primitive(PrimitiveType::Unknown), span)
                    } else {
                        // Find matching property in type
                        let found = obj_type.members.iter().find_map(|member| {
                            if let ObjectTypeMember::Property(prop) = member {
                                if prop.name.node == prop_pattern.key.node {
                                    return Some(prop.type_annotation.clone());
                                }
                            }
                            None
                        });

                        match found {
                            Some(t) => t,
                            None => {
                                return Err(TypeCheckError::new(
                                    format!(
                                        "Property '{}' does not exist on type",
                                        interner.resolve(prop_pattern.key.node)
                                    ),
                                    span,
                                ));
                            }
                        }
                    };

                    if let Some(value_pattern) = &prop_pattern.value {
                        declare_pattern(
                            value_pattern,
                            prop_type,
                            kind,
                            span,
                            symbol_table,
                            interner,
                            arena,
                        )?;
                    } else {
                        // Shorthand: { x } means { x: x }
                        let symbol = Symbol::new(
                            interner.resolve(prop_pattern.key.node).to_string(),
                            kind,
                            prop_type,
                            span,
                        );
                        symbol_table
                            .declare(symbol)
                            .map_err(|e| TypeCheckError::new(e, span))?;
                    }
                }

                // Handle rest pattern: { a, ...rest }
                if let Some(rest_ident) = &obj_pattern.rest {
                    // Build object type from remaining properties
                    let remaining_members: Vec<_> = obj_type
                        .members
                        .iter()
                        .filter(|member| {
                            if let ObjectTypeMember::Property(prop) = member {
                                !destructured_keys.contains(&prop.name.node)
                            } else {
                                true
                            }
                        })
                        .cloned()
                        .collect();

                    let rest_type = Type::new(
                        TypeKind::Object(ObjectType {
                            members: arena.alloc_slice_fill_iter(remaining_members),
                            span,
                        }),
                        span,
                    );

                    let symbol = Symbol::new(
                        interner.resolve(rest_ident.node).to_string(),
                        kind,
                        rest_type,
                        span,
                    );
                    symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, span))?;
                }
            } else {
                return Err(TypeCheckError::new(
                    "Cannot destructure non-object type",
                    span,
                ));
            }
            Ok(())
        }
        Pattern::Literal(_, _) | Pattern::Wildcard(_) => {
            // Literals and wildcards don't declare symbols
            Ok(())
        }
        Pattern::Or(or_pattern) => {
            // For or-patterns, all alternatives bind the same variables
            // Declare from the first alternative
            if let Some(first) = or_pattern.alternatives.first() {
                declare_pattern(first, typ, kind, span, symbol_table, interner, arena)?;
            }
            Ok(())
        }
        Pattern::Template(template_pattern) => {
            use luanext_parser::ast::pattern::TemplatePatternPart;
            // Declare all captures as string type
            for part in template_pattern.parts.iter() {
                if let TemplatePatternPart::Capture(ident) = part {
                    let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), span);
                    let symbol = Symbol::new(
                        interner.resolve(ident.node).to_string(),
                        kind,
                        string_type,
                        span,
                    );
                    symbol_table
                        .declare(symbol)
                        .map_err(|e| TypeCheckError::new(e, span))?;
                }
            }
            Ok(())
        }
    }
}

/// Register a `declare function` statement in the symbol table.
///
/// Ambient function declarations (using `declare function`) don't have bodies.
/// They just register the function signature for type checking purposes.
pub fn register_declare_function<'arena>(
    func: &DeclareFunctionStatement<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
    arena: &'arena Bump,
) -> Result<(), TypeCheckError> {
    let func_type = Type::new(
        TypeKind::Function(FunctionType {
            type_parameters: func.type_parameters,
            parameters: func.parameters,
            return_type: arena.alloc(func.return_type.clone()),
            throws: func.throws,
            span: func.span,
        }),
        func.span,
    );

    let symbol = Symbol::new(
        interner.resolve(func.name.node).to_string(),
        SymbolKind::Function,
        func_type,
        func.span,
    );

    symbol_table
        .declare(symbol)
        .map_err(|e| TypeCheckError::new(e, func.span))
}

/// Register a `declare const` statement in the symbol table.
///
/// Ambient constant declarations don't have initializers.
/// They just register the constant name and type.
pub fn register_declare_const<'arena>(
    const_decl: &DeclareConstStatement<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
) -> Result<(), TypeCheckError> {
    let symbol = Symbol::new(
        interner.resolve(const_decl.name.node).to_string(),
        SymbolKind::Const,
        const_decl.type_annotation.clone(),
        const_decl.span,
    );

    symbol_table
        .declare(symbol)
        .map_err(|e| TypeCheckError::new(e, const_decl.span))
}

/// Register a `declare namespace` statement in the symbol table.
///
/// Namespace declarations create an object type containing all exported members.
/// This allows `Namespace.member` access patterns.
pub fn register_declare_namespace<'arena>(
    ns: &DeclareNamespaceStatement<'arena>,
    symbol_table: &mut SymbolTable<'arena>,
    interner: &StringInterner,
    arena: &'arena Bump,
) -> Result<(), TypeCheckError> {
    // Create object type from namespace members
    let members: Vec<_> = ns
        .members
        .iter()
        .filter_map(|member| match member {
            Statement::DeclareFunction(func) if func.is_export => {
                Some(ObjectTypeMember::Method(MethodSignature {
                    name: func.name.clone(),
                    type_parameters: func.type_parameters,
                    parameters: func.parameters,
                    return_type: func.return_type.clone(),
                    body: None,
                    span: func.span,
                }))
            }
            Statement::DeclareConst(const_decl) if const_decl.is_export => {
                Some(ObjectTypeMember::Property(PropertySignature {
                    is_readonly: true, // Constants are readonly
                    name: const_decl.name.clone(),
                    is_optional: false,
                    type_annotation: const_decl.type_annotation.clone(),
                    span: const_decl.span,
                }))
            }
            _ => None,
        })
        .collect();

    let members_slice = arena.alloc_slice_fill_iter(members);
    let namespace_type = Type::new(
        TypeKind::Object(ObjectType {
            members: members_slice,
            span: ns.span,
        }),
        ns.span,
    );

    let symbol = Symbol::new(
        interner.resolve(ns.name.node).to_string(),
        SymbolKind::Const,
        namespace_type,
        ns.span,
    );

    symbol_table
        .declare(symbol)
        .map_err(|e| TypeCheckError::new(e, ns.span))
}
