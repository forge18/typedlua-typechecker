use rustc_hash::FxHashMap;
use typedlua_parser::ast::expression::{BinaryOp, Expression, ExpressionKind, Literal, UnaryOp};
use typedlua_parser::ast::types::{PrimitiveType, Type, TypeKind};
use typedlua_parser::string_interner::StringId;

/// Trait for type narrowing operations
///
/// This trait defines the interface for narrowing types based on conditions and patterns.
/// It is used by the type checker to refine variable types in conditional branches.
pub trait NarrowingVisitor {
    /// Narrow types based on a condition expression
    ///
    /// Returns (then_context, else_context) with refined types for each branch.
    /// The then_context contains types that apply when the condition is true,
    /// and the else_context contains types that apply when the condition is false.
    fn narrow_from_condition(
        &self,
        condition: &Expression,
        base_ctx: &NarrowingContext,
        original_types: &FxHashMap<StringId, Type>,
        interner: &typedlua_parser::string_interner::StringInterner,
    ) -> (NarrowingContext, NarrowingContext);

    /// Get the current narrowing context
    fn get_context(&self) -> &NarrowingContext;

    /// Get a mutable reference to the narrowing context
    fn get_context_mut(&mut self) -> &mut NarrowingContext;
}

/// Type narrowing context - tracks refined types for variables in the current scope
#[derive(Debug, Clone)]
pub struct NarrowingContext {
    /// Map from variable name to narrowed type
    narrowed_types: FxHashMap<StringId, Type>,
}

impl Default for NarrowingContext {
    fn default() -> Self {
        Self::new()
    }
}

impl NarrowingContext {
    pub fn new() -> Self {
        Self {
            narrowed_types: FxHashMap::default(),
        }
    }

    /// Get the narrowed type for a variable, if any
    pub fn get_narrowed_type(&self, name: StringId) -> Option<&Type> {
        self.narrowed_types.get(&name)
    }

    /// Set a narrowed type for a variable
    pub fn set_narrowed_type(&mut self, name: StringId, typ: Type) {
        self.narrowed_types.insert(name, typ);
    }

    /// Remove a narrowed type (when variable is reassigned)
    pub fn remove_narrowed_type(&mut self, name: StringId) {
        self.narrowed_types.remove(&name);
    }

    /// Merge two narrowing contexts (for branch join points)
    pub fn merge(then_ctx: &Self, else_ctx: &Self) -> Self {
        // For now, we only keep types that are the same in both branches
        // More sophisticated: create union types for divergent branches
        let mut merged = NarrowingContext::new();

        for (name, then_type) in &then_ctx.narrowed_types {
            if let Some(else_type) = else_ctx.narrowed_types.get(name) {
                if types_equal(then_type, else_type) {
                    merged.narrowed_types.insert(*name, then_type.clone());
                }
            }
        }

        merged
    }

    /// Clone the context for a new branch
    pub fn clone_for_branch(&self) -> Self {
        self.clone()
    }
}

/// Type narrower implementation that tracks narrowed types
pub struct TypeNarrower {
    context: NarrowingContext,
}

impl TypeNarrower {
    /// Create a new type narrower with an empty context
    pub fn new() -> Self {
        Self {
            context: NarrowingContext::new(),
        }
    }
}

impl Default for TypeNarrower {
    fn default() -> Self {
        Self::new()
    }
}

impl NarrowingVisitor for TypeNarrower {
    fn narrow_from_condition(
        &self,
        condition: &Expression,
        base_ctx: &NarrowingContext,
        original_types: &FxHashMap<StringId, Type>,
        interner: &typedlua_parser::string_interner::StringInterner,
    ) -> (NarrowingContext, NarrowingContext) {
        narrow_type_from_condition(condition, base_ctx, original_types, interner)
    }

    fn get_context(&self) -> &NarrowingContext {
        &self.context
    }

    fn get_context_mut(&mut self) -> &mut NarrowingContext {
        &mut self.context
    }
}

/// Narrow a type based on a condition expression
/// Returns (then_context, else_context) with refined types for each branch
pub fn narrow_type_from_condition(
    condition: &Expression,
    base_ctx: &NarrowingContext,
    original_types: &FxHashMap<StringId, Type>,
    interner: &typedlua_parser::string_interner::StringInterner,
) -> (NarrowingContext, NarrowingContext) {
    let mut then_ctx = base_ctx.clone_for_branch();
    let mut else_ctx = base_ctx.clone_for_branch();

    match &condition.kind {
        // typeof x == "string"
        ExpressionKind::Binary(BinaryOp::Equal, left, right) => {
            if let Some((var_name, type_name)) = extract_typeof_check(interner, left, right) {
                if let Some(narrowed_type) = typeof_string_to_type(&type_name) {
                    then_ctx.set_narrowed_type(var_name, narrowed_type.clone());

                    // In else branch, exclude the checked type
                    if let Some(original) = original_types.get(&var_name) {
                        if let Some(else_type) = exclude_type(original, &narrowed_type) {
                            else_ctx.set_narrowed_type(var_name, else_type);
                        }
                    }
                }
            } else {
                // Check for x == nil equality narrowing
                if let Some((var_name, is_nil)) = extract_nil_check(interner, left, right) {
                    if is_nil {
                        // then: x is nil
                        then_ctx.set_narrowed_type(
                            var_name,
                            Type::new(TypeKind::Primitive(PrimitiveType::Nil), condition.span),
                        );

                        // else: x is non-nil
                        if let Some(original) = original_types.get(&var_name) {
                            if let Some(non_nil) = remove_nil_from_type(original) {
                                else_ctx.set_narrowed_type(var_name, non_nil);
                            }
                        }
                    }
                }
            }
        }

        // typeof x != "string"
        ExpressionKind::Binary(BinaryOp::NotEqual, left, right) => {
            if let Some((var_name, type_name)) = extract_typeof_check(interner, left, right) {
                if let Some(narrowed_type) = typeof_string_to_type(&type_name) {
                    // Flip the narrowing for != operator
                    else_ctx.set_narrowed_type(var_name, narrowed_type.clone());

                    if let Some(original) = original_types.get(&var_name) {
                        if let Some(then_type) = exclude_type(original, &narrowed_type) {
                            then_ctx.set_narrowed_type(var_name, then_type);
                        }
                    }
                }
            } else {
                // x != nil
                if let Some((var_name, is_nil)) = extract_nil_check(interner, left, right) {
                    if is_nil {
                        // Flip for != operator
                        // then: x is non-nil
                        if let Some(original) = original_types.get(&var_name) {
                            if let Some(non_nil) = remove_nil_from_type(original) {
                                then_ctx.set_narrowed_type(var_name, non_nil);
                            }
                        }

                        // else: x is nil
                        else_ctx.set_narrowed_type(
                            var_name,
                            Type::new(TypeKind::Primitive(PrimitiveType::Nil), condition.span),
                        );
                    }
                }
            }
        }

        // not condition (flip the branches)
        ExpressionKind::Unary(UnaryOp::Not, operand) => {
            let (inner_then, inner_else) =
                narrow_type_from_condition(operand, base_ctx, original_types, interner);
            return (inner_else, inner_then); // Flip!
        }

        // condition1 and condition2
        ExpressionKind::Binary(BinaryOp::And, left, right) => {
            // First narrow with left condition
            let (left_then, _left_else) =
                narrow_type_from_condition(left, base_ctx, original_types, interner);

            // Then narrow the 'then' branch with right condition
            let (final_then, _final_else) =
                narrow_type_from_condition(right, &left_then, original_types, interner);

            return (final_then, else_ctx);
        }

        // condition1 or condition2
        ExpressionKind::Binary(BinaryOp::Or, left, right) => {
            // For 'or', we narrow in the else branch with the right condition
            let (left_then, left_else) =
                narrow_type_from_condition(left, base_ctx, original_types, interner);
            let (right_then, right_else) =
                narrow_type_from_condition(right, &left_else, original_types, interner);

            // Then branch: either left or right was true
            let merged_then = NarrowingContext::merge(&left_then, &right_then);

            return (merged_then, right_else);
        }

        // Type guard function call: isString(x)
        ExpressionKind::Call(function, arguments, _) => {
            if let Some((var_name, narrowed_type)) =
                extract_type_guard_call(function, arguments, original_types)
            {
                // In then branch: narrow to the guarded type
                then_ctx.set_narrowed_type(var_name, narrowed_type.clone());

                // In else branch: exclude the guarded type
                if let Some(original) = original_types.get(&var_name) {
                    if let Some(else_type) = exclude_type(original, &narrowed_type) {
                        else_ctx.set_narrowed_type(var_name, else_type);
                    }
                }
            }
        }

        // instanceof check: x instanceof ClassName
        ExpressionKind::Binary(BinaryOp::Instanceof, left, right) => {
            if let ExpressionKind::Identifier(var_name) = &left.kind {
                if let ExpressionKind::Identifier(class_name) = &right.kind {
                    // In then branch: narrow to the class type
                    // For now, create a reference to the class type
                    let class_type = Type::new(
                        TypeKind::Reference(typedlua_parser::ast::types::TypeReference {
                            name: typedlua_parser::ast::Ident::new(*class_name, condition.span),
                            type_arguments: None,
                            span: condition.span,
                        }),
                        condition.span,
                    );
                    then_ctx.set_narrowed_type(*var_name, class_type.clone());

                    // In else branch: exclude the class type
                    if let Some(original) = original_types.get(var_name) {
                        if let Some(else_type) = exclude_type(original, &class_type) {
                            else_ctx.set_narrowed_type(*var_name, else_type);
                        }
                    }
                }
            }
        }

        // Truthiness check: if x then ...
        ExpressionKind::Identifier(name) => {
            if let Some(original) = original_types.get(name) {
                // In then branch: x is truthy (non-nil, non-false)
                if let Some(truthy_type) = make_truthy_type(original) {
                    then_ctx.set_narrowed_type(*name, truthy_type);
                }

                // In else branch: x is falsy (nil or false)
                if let Some(falsy_type) = make_falsy_type(original) {
                    else_ctx.set_narrowed_type(*name, falsy_type);
                }
            }
        }

        _ => {
            // No narrowing for other expression types
        }
    }

    (then_ctx, else_ctx)
}

/// Extract typeof check: typeof x == "string" -> Some((x, "string"))
fn extract_typeof_check(
    interner: &typedlua_parser::string_interner::StringInterner,
    left: &Expression,
    right: &Expression,
) -> Option<(StringId, String)> {
    // Check: typeof x == "string"
    if let ExpressionKind::Call(function, arguments, _) = &left.kind {
        if let ExpressionKind::Identifier(func_name) = &function.kind {
            if interner.resolve(*func_name) == "typeof" && arguments.len() == 1 {
                if let ExpressionKind::Identifier(var_name) = &arguments[0].value.kind {
                    if let ExpressionKind::Literal(Literal::String(type_name)) = &right.kind {
                        return Some((*var_name, type_name.clone()));
                    }
                }
            }
        }
    }

    // Check: "string" == typeof x (reversed)
    if let ExpressionKind::Literal(Literal::String(type_name)) = &left.kind {
        if let ExpressionKind::Call(function, arguments, _) = &right.kind {
            if let ExpressionKind::Identifier(func_name) = &function.kind {
                if interner.resolve(*func_name) == "typeof" && arguments.len() == 1 {
                    if let ExpressionKind::Identifier(var_name) = &arguments[0].value.kind {
                        return Some((*var_name, type_name.clone()));
                    }
                }
            }
        }
    }

    None
}

/// Extract type guard function call: isString(x) -> Some((x, string))
/// Type guards are functions with return type `param is Type`
fn extract_type_guard_call(
    function: &Expression,
    arguments: &[typedlua_parser::ast::expression::Argument],
    original_types: &FxHashMap<StringId, Type>,
) -> Option<(StringId, Type)> {
    // Check if this is a function call with one argument
    if arguments.len() != 1 {
        return None;
    }

    // Get the variable being checked
    let var_name = match &arguments[0].value.kind {
        ExpressionKind::Identifier(name) => *name,
        _ => return None,
    };

    // Try to get the function type from the passed context
    // This allows checking actual type signatures when available
    if let ExpressionKind::Identifier(func_name) = &function.kind {
        // Check if we have type information for this function
        if let Some(func_type) = original_types.get(func_name) {
            // Check if it's a function with a TypePredicate return type
            if let TypeKind::Function(func_sig) = &func_type.kind {
                if let TypeKind::TypePredicate(predicate) = &func_sig.return_type.kind {
                    // Verify the parameter name matches the argument
                    if predicate.parameter_name.node == var_name {
                        return Some((var_name, (*predicate.type_annotation).clone()));
                    }
                }
            }
        }
    }

    None
}

/// Extract nil check: x == nil -> Some((x, true))
fn extract_nil_check(
    _interner: &typedlua_parser::string_interner::StringInterner,
    left: &Expression,
    right: &Expression,
) -> Option<(StringId, bool)> {
    // Check: x == nil
    if let ExpressionKind::Identifier(var_name) = &left.kind {
        if let ExpressionKind::Literal(Literal::Nil) = &right.kind {
            return Some((*var_name, true));
        }
    }

    // Check: nil == x (reversed)
    if let ExpressionKind::Literal(Literal::Nil) = &left.kind {
        if let ExpressionKind::Identifier(var_name) = &right.kind {
            return Some((*var_name, true));
        }
    }

    None
}

/// Convert typeof string to a type
fn typeof_string_to_type(type_name: &str) -> Option<Type> {
    let span = typedlua_parser::span::Span::new(0, 0, 0, 0);
    match type_name {
        "nil" => Some(Type::new(TypeKind::Primitive(PrimitiveType::Nil), span)),
        "boolean" => Some(Type::new(TypeKind::Primitive(PrimitiveType::Boolean), span)),
        "number" => Some(Type::new(TypeKind::Primitive(PrimitiveType::Number), span)),
        "string" => Some(Type::new(TypeKind::Primitive(PrimitiveType::String), span)),
        "table" => Some(Type::new(TypeKind::Primitive(PrimitiveType::Table), span)),
        _ => None,
    }
}

/// Exclude a type from a union
fn exclude_type(typ: &Type, to_exclude: &Type) -> Option<Type> {
    match &typ.kind {
        TypeKind::Union(types) => {
            let remaining: Vec<Type> = types
                .iter()
                .filter(|t| !types_equal(t, to_exclude))
                .cloned()
                .collect();

            if remaining.is_empty() {
                Some(Type::new(
                    TypeKind::Primitive(PrimitiveType::Never),
                    typ.span,
                ))
            } else if remaining.len() == 1 {
                Some(remaining.into_iter().next().unwrap())
            } else {
                Some(Type::new(TypeKind::Union(remaining), typ.span))
            }
        }
        _ if types_equal(typ, to_exclude) => Some(Type::new(
            TypeKind::Primitive(PrimitiveType::Never),
            typ.span,
        )),
        _ => Some(typ.clone()),
    }
}

/// Remove nil from a type (for non-nil narrowing)
fn remove_nil_from_type(typ: &Type) -> Option<Type> {
    match &typ.kind {
        TypeKind::Union(types) => {
            let remaining: Vec<Type> = types.iter().filter(|t| !is_nil_type(t)).cloned().collect();

            if remaining.is_empty() {
                Some(Type::new(
                    TypeKind::Primitive(PrimitiveType::Never),
                    typ.span,
                ))
            } else if remaining.len() == 1 {
                Some(remaining.into_iter().next().unwrap())
            } else {
                Some(Type::new(TypeKind::Union(remaining), typ.span))
            }
        }
        _ if is_nil_type(typ) => Some(Type::new(
            TypeKind::Primitive(PrimitiveType::Never),
            typ.span,
        )),
        _ => Some(typ.clone()),
    }
}

/// Check if a type is nil (handles both Literal(Nil) and Primitive(Nil))
fn is_nil_type(typ: &Type) -> bool {
    matches!(
        typ.kind,
        TypeKind::Primitive(PrimitiveType::Nil) | TypeKind::Literal(Literal::Nil)
    )
}

/// Make a type truthy (remove nil and false)
fn make_truthy_type(typ: &Type) -> Option<Type> {
    match &typ.kind {
        TypeKind::Union(types) => {
            let truthy: Vec<Type> = types
                .iter()
                .filter(|t| !is_falsy_type(t))
                .cloned()
                .collect();

            if truthy.is_empty() {
                Some(Type::new(
                    TypeKind::Primitive(PrimitiveType::Never),
                    typ.span,
                ))
            } else if truthy.len() == 1 {
                Some(truthy.into_iter().next().unwrap())
            } else {
                Some(Type::new(TypeKind::Union(truthy), typ.span))
            }
        }
        _ if is_falsy_type(typ) => Some(Type::new(
            TypeKind::Primitive(PrimitiveType::Never),
            typ.span,
        )),
        _ => Some(typ.clone()),
    }
}

/// Make a type falsy (only nil or false)
fn make_falsy_type(typ: &Type) -> Option<Type> {
    match &typ.kind {
        TypeKind::Union(types) => {
            let falsy: Vec<Type> = types.iter().filter(|t| is_falsy_type(t)).cloned().collect();

            if falsy.is_empty() {
                Some(Type::new(
                    TypeKind::Primitive(PrimitiveType::Never),
                    typ.span,
                ))
            } else if falsy.len() == 1 {
                Some(falsy.into_iter().next().unwrap())
            } else {
                Some(Type::new(TypeKind::Union(falsy), typ.span))
            }
        }
        _ if is_falsy_type(typ) => Some(typ.clone()),
        _ => Some(Type::new(
            TypeKind::Primitive(PrimitiveType::Never),
            typ.span,
        )),
    }
}

/// Check if a type is falsy (nil or false)
fn is_falsy_type(typ: &Type) -> bool {
    matches!(
        typ.kind,
        TypeKind::Primitive(PrimitiveType::Nil)
            | TypeKind::Literal(Literal::Nil)
            | TypeKind::Literal(Literal::Boolean(false))
    )
}

/// Simple type equality check
fn types_equal(t1: &Type, t2: &Type) -> bool {
    match (&t1.kind, &t2.kind) {
        (TypeKind::Primitive(p1), TypeKind::Primitive(p2)) => p1 == p2,
        (TypeKind::Literal(l1), TypeKind::Literal(l2)) => l1 == l2,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typedlua_parser::span::Span;

    fn make_span() -> Span {
        Span::new(0, 0, 0, 0)
    }

    #[test]
    fn test_narrowing_context_basic() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let mut ctx = NarrowingContext::new();

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let x_id = interner.intern("x");
        ctx.set_narrowed_type(x_id, string_type.clone());

        assert!(ctx.get_narrowed_type(x_id).is_some());
        let y_id = interner.intern("y");
        assert!(ctx.get_narrowed_type(y_id).is_none());

        ctx.remove_narrowed_type(x_id);
        assert!(ctx.get_narrowed_type(x_id).is_none());
    }

    #[test]
    fn test_narrowing_context_merge() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let mut then_ctx = NarrowingContext::new();
        let mut else_ctx = NarrowingContext::new();

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let x_id = interner.intern("x");
        let y_id = interner.intern("y");

        // Both have 'x' as string - should be kept
        then_ctx.set_narrowed_type(x_id, string_type.clone());
        else_ctx.set_narrowed_type(x_id, string_type.clone());

        // Only then has 'y' - should not be kept
        then_ctx.set_narrowed_type(y_id, number_type.clone());

        let merged = NarrowingContext::merge(&then_ctx, &else_ctx);

        assert!(merged.get_narrowed_type(x_id).is_some());
        assert!(merged.get_narrowed_type(y_id).is_none());
    }

    #[test]
    fn test_remove_nil_from_union() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
            ]),
            make_span(),
        );

        let non_nil = remove_nil_from_type(&union_type).unwrap();

        assert!(matches!(
            non_nil.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_make_truthy_type() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
                Type::new(TypeKind::Literal(Literal::Boolean(false)), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
            ]),
            make_span(),
        );

        let truthy = make_truthy_type(&union_type).unwrap();

        if let TypeKind::Union(types) = &truthy.kind {
            assert_eq!(types.len(), 2); // string and number
        } else {
            panic!("Expected union type");
        }
    }

    // ========================================================================
    // Additional Comprehensive Tests
    // ========================================================================

    #[test]
    fn test_narrowing_context_default() {
        let ctx: NarrowingContext = Default::default();
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let x_id = interner.intern("x");
        assert!(ctx.get_narrowed_type(x_id).is_none());
    }

    #[test]
    fn test_narrowing_context_clone_for_branch() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let mut ctx = NarrowingContext::new();

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let x_id = interner.intern("x");
        ctx.set_narrowed_type(x_id, string_type.clone());

        let cloned = ctx.clone_for_branch();
        assert!(cloned.get_narrowed_type(x_id).is_some());

        // Modifying cloned should not affect original
        let y_id = interner.intern("y");
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        let mut cloned_mut = cloned;
        cloned_mut.set_narrowed_type(y_id, number_type);

        assert!(ctx.get_narrowed_type(y_id).is_none());
        assert!(cloned_mut.get_narrowed_type(y_id).is_some());
    }

    #[test]
    fn test_narrowing_context_merge_different_types() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let mut then_ctx = NarrowingContext::new();
        let mut else_ctx = NarrowingContext::new();

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        let x_id = interner.intern("x");

        // Different types for same variable - should not be kept
        then_ctx.set_narrowed_type(x_id, string_type);
        else_ctx.set_narrowed_type(x_id, number_type);

        let merged = NarrowingContext::merge(&then_ctx, &else_ctx);
        assert!(merged.get_narrowed_type(x_id).is_none());
    }

    #[test]
    fn test_narrowing_context_merge_empty() {
        let then_ctx = NarrowingContext::new();
        let else_ctx = NarrowingContext::new();

        let merged = NarrowingContext::merge(&then_ctx, &else_ctx);
        // Should be empty
        assert!(merged
            .get_narrowed_type(typedlua_parser::string_interner::StringId::from_u32(0))
            .is_none());
    }

    #[test]
    fn test_type_narrower_new() {
        let narrower = TypeNarrower::new();
        assert!(narrower
            .get_context()
            .get_narrowed_type(typedlua_parser::string_interner::StringId::from_u32(0))
            .is_none());
    }

    #[test]
    fn test_type_narrower_default() {
        let narrower: TypeNarrower = Default::default();
        assert!(narrower
            .get_context()
            .get_narrowed_type(typedlua_parser::string_interner::StringId::from_u32(0))
            .is_none());
    }

    #[test]
    fn test_type_narrower_get_context_mut() {
        let mut narrower = TypeNarrower::new();
        let interner = typedlua_parser::string_interner::StringInterner::new();

        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let x_id = interner.intern("x");

        {
            let ctx = narrower.get_context_mut();
            ctx.set_narrowed_type(x_id, string_type);
        }

        assert!(narrower.get_context().get_narrowed_type(x_id).is_some());
    }

    #[test]
    fn test_is_nil_type() {
        let nil_prim = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());
        let nil_lit = Type::new(TypeKind::Literal(Literal::Nil), make_span());
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        assert!(is_nil_type(&nil_prim));
        assert!(is_nil_type(&nil_lit));
        assert!(!is_nil_type(&string_type));
    }

    #[test]
    fn test_is_falsy_type() {
        let nil_prim = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());
        let nil_lit = Type::new(TypeKind::Literal(Literal::Nil), make_span());
        let false_lit = Type::new(TypeKind::Literal(Literal::Boolean(false)), make_span());
        let true_lit = Type::new(TypeKind::Literal(Literal::Boolean(true)), make_span());
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        assert!(is_falsy_type(&nil_prim));
        assert!(is_falsy_type(&nil_lit));
        assert!(is_falsy_type(&false_lit));
        assert!(!is_falsy_type(&true_lit));
        assert!(!is_falsy_type(&string_type));
    }

    #[test]
    fn test_remove_nil_from_non_union() {
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());

        // Non-nil type should remain unchanged
        let result = remove_nil_from_type(&string_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // Nil type should become Never
        let result = remove_nil_from_type(&nil_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_remove_nil_results_in_single_type() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
            ]),
            make_span(),
        );

        let result = remove_nil_from_type(&union_type).unwrap();
        // Should result in a single type, not a union
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_make_truthy_type_non_union() {
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());

        // Truthy type should remain unchanged
        let result = make_truthy_type(&string_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // Nil type should become Never
        let result = make_truthy_type(&nil_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_make_falsy_type() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span()),
                Type::new(TypeKind::Literal(Literal::Boolean(false)), make_span()),
            ]),
            make_span(),
        );

        let falsy = make_falsy_type(&union_type).unwrap();

        if let TypeKind::Union(types) = &falsy.kind {
            assert_eq!(types.len(), 2); // nil and false
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_make_falsy_type_non_union() {
        let nil_type = Type::new(TypeKind::Primitive(PrimitiveType::Nil), make_span());
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());

        // Nil type should remain unchanged
        let result = make_falsy_type(&nil_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Nil)
        ));

        // String type should become Never
        let result = make_falsy_type(&string_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_exclude_type_from_union() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Boolean), make_span()),
            ]),
            make_span(),
        );

        let to_exclude = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        let result = exclude_type(&union_type, &to_exclude).unwrap();

        if let TypeKind::Union(types) = &result.kind {
            assert_eq!(types.len(), 2);
        } else {
            panic!("Expected union type");
        }
    }

    #[test]
    fn test_exclude_type_results_in_single() {
        let union_type = Type::new(
            TypeKind::Union(vec![
                Type::new(TypeKind::Primitive(PrimitiveType::String), make_span()),
                Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span()),
            ]),
            make_span(),
        );

        let to_exclude = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());
        let result = exclude_type(&union_type, &to_exclude).unwrap();

        // Should result in a single type
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));
    }

    #[test]
    fn test_exclude_all_types_becomes_never() {
        let union_type = Type::new(
            TypeKind::Union(vec![Type::new(
                TypeKind::Primitive(PrimitiveType::String),
                make_span(),
            )]),
            make_span(),
        );

        let to_exclude = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let result = exclude_type(&union_type, &to_exclude).unwrap();

        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_exclude_type_non_union() {
        let string_type = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number_type = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        // Exclude different type - should remain unchanged
        let result = exclude_type(&string_type, &number_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::String)
        ));

        // Exclude same type - should become Never
        let result = exclude_type(&string_type, &string_type).unwrap();
        assert!(matches!(
            result.kind,
            TypeKind::Primitive(PrimitiveType::Never)
        ));
    }

    #[test]
    fn test_types_equal() {
        let string1 = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let string2 = Type::new(TypeKind::Primitive(PrimitiveType::String), make_span());
        let number = Type::new(TypeKind::Primitive(PrimitiveType::Number), make_span());

        assert!(types_equal(&string1, &string2));
        assert!(!types_equal(&string1, &number));
    }

    #[test]
    fn test_typeof_string_to_type() {
        assert!(typeof_string_to_type("nil").is_some());
        assert!(typeof_string_to_type("boolean").is_some());
        assert!(typeof_string_to_type("number").is_some());
        assert!(typeof_string_to_type("string").is_some());
        assert!(typeof_string_to_type("table").is_some());
        assert!(typeof_string_to_type("unknown").is_none());
        assert!(typeof_string_to_type("function").is_none());
    }

    #[test]
    fn test_extract_nil_check_basic() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let x_id = interner.intern("x");

        // x == nil
        let left = Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };
        let right = Expression {
            kind: ExpressionKind::Literal(Literal::Nil),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = extract_nil_check(&interner, &left, &right);
        assert!(result.is_some());
        let (name, is_nil) = result.unwrap();
        assert_eq!(name, x_id);
        assert!(is_nil);
    }

    #[test]
    fn test_extract_nil_check_reversed() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let x_id = interner.intern("x");

        // nil == x
        let left = Expression {
            kind: ExpressionKind::Literal(Literal::Nil),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };
        let right = Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = extract_nil_check(&interner, &left, &right);
        assert!(result.is_some());
    }

    #[test]
    fn test_extract_nil_check_not_nil() {
        let interner = typedlua_parser::string_interner::StringInterner::new();
        let x_id = interner.intern("x");

        // x == "string" - not a nil check
        let left = Expression {
            kind: ExpressionKind::Identifier(x_id),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };
        let right = Expression {
            kind: ExpressionKind::Literal(Literal::String("hello".to_string())),
            span: make_span(),
            annotated_type: None,
            receiver_class: None,
        };

        let result = extract_nil_check(&interner, &left, &right);
        assert!(result.is_none());
    }
}
