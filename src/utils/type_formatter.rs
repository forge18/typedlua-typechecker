/// User-friendly type formatting for error messages
///
/// This module provides functions to format types in a human-readable way,
/// suitable for error messages. Unlike Debug formatting, this produces clean,
/// TypeScript-like type representations.
use luanext_parser::ast::{
    expression::Literal,
    pattern::Pattern,
    statement::IndexKeyType,
    types::{FunctionType, ObjectType, ObjectTypeMember, PrimitiveType, Type, TypeKind},
};
use luanext_parser::string_interner::StringInterner;

/// Format a type for display in error messages
///
/// Produces user-friendly type representations:
/// - `Primitive(String)` → `"string"`
/// - `Union([String, Number])` → `"string | number"`
/// - `Function(...)` → `"(string, number) => boolean"`
///
/// # Arguments
/// * `ty` - The type to format
/// * `interner` - String interner for resolving identifiers
pub fn format_type_for_error(ty: &Type, interner: &StringInterner) -> String {
    format_type_kind(&ty.kind, interner)
}

fn format_type_kind(kind: &TypeKind, interner: &StringInterner) -> String {
    match kind {
        TypeKind::Primitive(prim) => format_primitive(*prim),
        TypeKind::Reference(ref_ty) => {
            let name = interner.resolve(ref_ty.name.node);
            if let Some(type_args) = ref_ty.type_arguments {
                let args: Vec<String> = type_args
                    .iter()
                    .map(|t| format_type_for_error(t, interner))
                    .collect();
                format!("{}<{}>", name, args.join(", "))
            } else {
                name.to_string()
            }
        }
        TypeKind::Union(types) => {
            let formatted: Vec<String> = types
                .iter()
                .map(|t| format_type_for_error(t, interner))
                .collect();
            formatted.join(" | ")
        }
        TypeKind::Intersection(types) => {
            let formatted: Vec<String> = types
                .iter()
                .map(|t| format_type_for_error(t, interner))
                .collect();
            formatted.join(" & ")
        }
        TypeKind::Object(obj) => format_object_type(obj, interner),
        TypeKind::Array(elem) => {
            format!("{}[]", format_type_for_error(elem, interner))
        }
        TypeKind::Tuple(elements) => {
            let formatted: Vec<String> = elements
                .iter()
                .map(|t| format_type_for_error(t, interner))
                .collect();
            format!("[{}]", formatted.join(", "))
        }
        TypeKind::Function(func) => format_function_type(func, interner),
        TypeKind::Literal(lit) => format_literal(lit),
        TypeKind::TypeQuery(expr) => format!("typeof {:?}", expr), // Simplified
        TypeKind::KeyOf(ty) => {
            format!("keyof {}", format_type_for_error(ty, interner))
        }
        TypeKind::IndexAccess(obj, index) => {
            format!(
                "{}[{}]",
                format_type_for_error(obj, interner),
                format_type_for_error(index, interner)
            )
        }
        TypeKind::Conditional(cond) => {
            format!(
                "{} extends {} ? {} : {}",
                format_type_for_error(cond.check_type, interner),
                format_type_for_error(cond.extends_type, interner),
                format_type_for_error(cond.true_type, interner),
                format_type_for_error(cond.false_type, interner)
            )
        }
        TypeKind::Mapped(mapped) => {
            format!(
                "{{ [K in {}]: {} }}",
                format_type_for_error(mapped.in_type, interner),
                format_type_for_error(mapped.value_type, interner)
            )
        }
        TypeKind::TemplateLiteral(template) => {
            let parts: Vec<String> = template
                .parts
                .iter()
                .map(|part| match part {
                    luanext_parser::ast::types::TemplateLiteralTypePart::String(s) => s.clone(),
                    luanext_parser::ast::types::TemplateLiteralTypePart::Type(t) => {
                        format!("${{{}}}", format_type_for_error(t, interner))
                    }
                })
                .collect();
            format!("`{}`", parts.join(""))
        }
        TypeKind::Nullable(ty) => {
            format!("{}?", format_type_for_error(ty, interner))
        }
        TypeKind::Parenthesized(ty) => {
            format!("({})", format_type_for_error(ty, interner))
        }
        TypeKind::Infer(ident) => {
            format!("infer {}", interner.resolve(ident.node))
        }
        TypeKind::TypePredicate(pred) => {
            format!(
                "{} is {}",
                interner.resolve(pred.parameter_name.node),
                format_type_for_error(pred.type_annotation, interner)
            )
        }
        TypeKind::Variadic(ty) => {
            format!("...{}", format_type_for_error(ty, interner))
        }
        TypeKind::Namespace(parts) => parts.join("."),
    }
}

fn format_primitive(prim: PrimitiveType) -> String {
    match prim {
        PrimitiveType::Nil => "nil".to_string(),
        PrimitiveType::Boolean => "boolean".to_string(),
        PrimitiveType::Number => "number".to_string(),
        PrimitiveType::Integer => "integer".to_string(),
        PrimitiveType::String => "string".to_string(),
        PrimitiveType::Unknown => "unknown".to_string(),
        PrimitiveType::Never => "never".to_string(),
        PrimitiveType::Void => "void".to_string(),
        PrimitiveType::Table => "table".to_string(),
        PrimitiveType::Coroutine => "coroutine".to_string(),
        PrimitiveType::Thread => "thread".to_string(),
    }
}

fn format_object_type(obj: &ObjectType, interner: &StringInterner) -> String {
    if obj.members.is_empty() {
        return "{}".to_string();
    }

    let members: Vec<String> = obj
        .members
        .iter()
        .map(|member| match member {
            ObjectTypeMember::Property(prop) => {
                let name = interner.resolve(prop.name.node);
                let optional = if prop.is_optional { "?" } else { "" };
                let ty = format_type_for_error(&prop.type_annotation, interner);
                format!("{}{}: {}", name, optional, ty)
            }
            ObjectTypeMember::Method(method) => {
                let name = interner.resolve(method.name.node);
                let params: Vec<String> = method
                    .parameters
                    .iter()
                    .map(|p| format_parameter(p, interner))
                    .collect();
                let ret = format_type_for_error(&method.return_type, interner);
                format!("{}({}): {}", name, params.join(", "), ret)
            }
            ObjectTypeMember::Index(index) => {
                let key_ty = format_index_key_type(index.key_type);
                let value_ty = format_type_for_error(&index.value_type, interner);
                format!("[key: {}]: {}", key_ty, value_ty)
            }
        })
        .collect();

    // Truncate if too many members
    if members.len() > 3 {
        format!("{{ {}, ... }}", members[..3].join("; "))
    } else {
        format!("{{ {} }}", members.join("; "))
    }
}

fn format_index_key_type(key_type: IndexKeyType) -> String {
    match key_type {
        IndexKeyType::String => "string".to_string(),
        IndexKeyType::Number => "number".to_string(),
    }
}

fn format_parameter(
    p: &luanext_parser::ast::statement::Parameter,
    interner: &StringInterner,
) -> String {
    let param_name = match &p.pattern {
        Pattern::Identifier(ident) => interner.resolve(ident.node).to_string(),
        _ => "_".to_string(), // Fallback for complex patterns
    };

    if let Some(ty) = &p.type_annotation {
        format!("{}: {}", param_name, format_type_for_error(ty, interner))
    } else {
        param_name
    }
}

fn format_function_type(func: &FunctionType, interner: &StringInterner) -> String {
    let params: Vec<String> = func
        .parameters
        .iter()
        .map(|p| format_parameter(p, interner))
        .collect();

    let ret = format_type_for_error(func.return_type, interner);

    if let Some(type_params) = func.type_parameters {
        if !type_params.is_empty() {
            let tparams: Vec<String> = type_params
                .iter()
                .map(|tp| interner.resolve(tp.name.node).to_string())
                .collect();
            return format!("<{}>({}) => {}", tparams.join(", "), params.join(", "), ret);
        }
    }

    format!("({}) => {}", params.join(", "), ret)
}

fn format_literal(lit: &Literal) -> String {
    match lit {
        Literal::String(s) => format!("\"{}\"", s),
        Literal::Number(n) => n.to_string(),
        Literal::Integer(i) => i.to_string(),
        Literal::Boolean(b) => b.to_string(),
        Literal::Nil => "nil".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use luanext_parser::ast::{types::TypeReference, Spanned};
    use luanext_parser::span::Span;
    use luanext_parser::string_interner::StringInterner;

    fn make_span() -> Span {
        Span::new(0, 10, 1, 1)
    }

    #[test]
    fn test_format_primitive_types() {
        let interner = StringInterner::default();

        let ty = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "string");

        let ty = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "number");

        let ty = Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "boolean");
    }

    #[test]
    fn test_format_union_type() {
        let interner = StringInterner::default();

        let types = vec![
            Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
            Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
        ];

        let leaked_types = Box::leak(types.into_boxed_slice());
        let ty = Type::new(TypeKind::Union(leaked_types), make_span());

        assert_eq!(format_type_for_error(&ty, &interner), "string | number");
    }

    #[test]
    fn test_format_array_type() {
        let interner = StringInterner::default();

        let elem = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let leaked_elem = Box::leak(Box::new(elem));

        let ty = Type::new(TypeKind::Array(leaked_elem), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "string[]");
    }

    #[test]
    fn test_format_literal_types() {
        let interner = StringInterner::default();

        let ty = Type::new(
            TypeKind::Literal(Literal::String("hello".to_string())),
            make_span(),
        );
        assert_eq!(format_type_for_error(&ty, &interner), "\"hello\"");

        let ty = Type::new(TypeKind::Literal(Literal::Number(42.0)), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "42");

        let ty = Type::new(TypeKind::Literal(Literal::Boolean(true)), make_span());
        assert_eq!(format_type_for_error(&ty, &interner), "true");
    }

    #[test]
    fn test_format_reference_type() {
        let interner = StringInterner::default();
        let name_id = interner.get_or_intern("User");

        let ty = Type::new(
            TypeKind::Reference(TypeReference {
                name: Spanned {
                    node: name_id,
                    span: make_span(),
                },
                type_arguments: None,
                span: make_span(),
            }),
            make_span(),
        );

        assert_eq!(format_type_for_error(&ty, &interner), "User");
    }
}
