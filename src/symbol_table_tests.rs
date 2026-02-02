#[cfg(test)]
mod tests {
    use super::super::symbol_table::{Scope, Symbol, SymbolKind, SymbolTable};
    use typedlua_parser::ast::types::{PrimitiveType, Type, TypeKind};
    use typedlua_parser::span::Span;

    fn create_test_symbol(name: &str, kind: SymbolKind) -> Symbol {
        Symbol::new(
            name.to_string(),
            kind,
            Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default()),
            Span::default(),
        )
    }

    fn create_test_symbol_with_type(name: &str, kind: SymbolKind, typ: Type) -> Symbol {
        Symbol::new(name.to_string(), kind, typ, Span::default())
    }

    // ========================================================================
    // Scope Tests
    // ========================================================================

    #[test]
    fn test_scope_new() {
        let scope = Scope::new();
        assert!(scope.lookup_local("anything").is_none());
    }

    #[test]
    fn test_scope_declare_success() {
        let mut scope = Scope::new();
        let symbol = create_test_symbol("x", SymbolKind::Variable);

        assert!(scope.declare(symbol).is_ok());
        assert!(scope.lookup_local("x").is_some());
    }

    #[test]
    fn test_scope_declare_duplicate() {
        let mut scope = Scope::new();
        let symbol1 = create_test_symbol("x", SymbolKind::Variable);
        let symbol2 = create_test_symbol("x", SymbolKind::Variable);

        assert!(scope.declare(symbol1).is_ok());
        let result = scope.declare(symbol2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already declared"));
    }

    #[test]
    fn test_scope_lookup_local() {
        let mut scope = Scope::new();
        let symbol = create_test_symbol("local_var", SymbolKind::Variable);

        scope.declare(symbol).unwrap();
        assert!(scope.lookup_local("local_var").is_some());
        assert!(scope.lookup_local("nonexistent").is_none());
    }

    #[test]
    fn test_scope_lookup_is_local_only() {
        // Scope::lookup() now only checks local symbols.
        // Parent scope lookups are done through SymbolTable::lookup() stack walking.
        let mut scope = Scope::new();
        let symbol = create_test_symbol("my_var", SymbolKind::Variable);
        scope.declare(symbol).unwrap();

        assert!(scope.lookup("my_var").is_some());
        assert!(scope.lookup("nonexistent").is_none());
    }

    #[test]
    fn test_symbol_table_parent_lookup_via_stack() {
        // Parent scope lookups work through SymbolTable's stack-walking approach
        let mut table = SymbolTable::new();

        let parent_symbol = create_test_symbol("parent_var", SymbolKind::Variable);
        table.declare(parent_symbol).unwrap();

        table.enter_scope();
        let child_symbol = create_test_symbol("child_var", SymbolKind::Variable);
        table.declare(child_symbol).unwrap();

        // Should see both parent and child symbols
        assert!(table.lookup("parent_var").is_some());
        assert!(table.lookup("child_var").is_some());
        assert!(table.lookup("nonexistent").is_none());

        table.exit_scope();

        // After exiting, child symbols are gone
        assert!(table.lookup("parent_var").is_some());
        assert!(table.lookup("child_var").is_none());
    }

    #[test]
    fn test_symbol_table_shadowing_via_stack() {
        let mut table = SymbolTable::new();

        let parent_symbol = create_test_symbol("x", SymbolKind::Variable);
        table.declare(parent_symbol).unwrap();

        table.enter_scope();
        let child_symbol = create_test_symbol_with_type(
            "x",
            SymbolKind::Const,
            Type::new(TypeKind::Primitive(PrimitiveType::String), Span::default()),
        );
        table.declare(child_symbol).unwrap();

        // Inner scope shadows outer
        let found = table.lookup("x").unwrap();
        assert_eq!(found.kind, SymbolKind::Const);

        table.exit_scope();

        // Outer scope restored
        let found = table.lookup("x").unwrap();
        assert_eq!(found.kind, SymbolKind::Variable);
    }

    #[test]
    fn test_scope_symbols_iterator() {
        let mut scope = Scope::new();
        scope
            .declare(create_test_symbol("a", SymbolKind::Variable))
            .unwrap();
        scope
            .declare(create_test_symbol("b", SymbolKind::Function))
            .unwrap();
        scope
            .declare(create_test_symbol("c", SymbolKind::Class))
            .unwrap();

        let symbols: Vec<_> = scope.symbols().collect();
        assert_eq!(symbols.len(), 3);
    }

    // ========================================================================
    // SymbolTable Tests
    // ========================================================================

    #[test]
    fn test_symbol_table_new() {
        let table = SymbolTable::new();
        assert!(table.lookup("anything").is_none());
    }

    #[test]
    fn test_symbol_table_declare_and_lookup() {
        let mut table = SymbolTable::new();
        let symbol = create_test_symbol("my_var", SymbolKind::Variable);

        table.declare(symbol).unwrap();
        assert!(table.lookup("my_var").is_some());
        assert!(table.lookup("nonexistent").is_none());
    }

    #[test]
    fn test_symbol_table_declare_duplicate() {
        let mut table = SymbolTable::new();
        let symbol1 = create_test_symbol("x", SymbolKind::Variable);
        let symbol2 = create_test_symbol("x", SymbolKind::Variable);

        table.declare(symbol1).unwrap();
        let result = table.declare(symbol2);
        assert!(result.is_err());
    }

    #[test]
    fn test_symbol_table_enter_exit_scope() {
        let mut table = SymbolTable::new();

        // Declare in outer scope
        table
            .declare(create_test_symbol("outer", SymbolKind::Variable))
            .unwrap();

        // Enter inner scope
        table.enter_scope();
        table
            .declare(create_test_symbol("inner", SymbolKind::Variable))
            .unwrap();

        // Should see both
        assert!(table.lookup("outer").is_some());
        assert!(table.lookup("inner").is_some());

        // Exit scope
        table.exit_scope();

        // Should only see outer
        assert!(table.lookup("outer").is_some());
        assert!(table.lookup("inner").is_none());
    }

    #[test]
    fn test_symbol_table_nested_scopes() {
        let mut table = SymbolTable::new();

        // Level 0
        table
            .declare(create_test_symbol("level0", SymbolKind::Variable))
            .unwrap();

        // Level 1
        table.enter_scope();
        table
            .declare(create_test_symbol("level1", SymbolKind::Variable))
            .unwrap();

        // Level 2
        table.enter_scope();
        table
            .declare(create_test_symbol("level2", SymbolKind::Variable))
            .unwrap();

        // Should see all three levels
        assert!(table.lookup("level0").is_some());
        assert!(table.lookup("level1").is_some());
        assert!(table.lookup("level2").is_some());

        // Exit to level 1
        table.exit_scope();
        assert!(table.lookup("level0").is_some());
        assert!(table.lookup("level1").is_some());
        assert!(table.lookup("level2").is_none());

        // Exit to level 0
        table.exit_scope();
        assert!(table.lookup("level0").is_some());
        assert!(table.lookup("level1").is_none());
        assert!(table.lookup("level2").is_none());
    }

    #[test]
    fn test_symbol_table_shadowing() {
        let mut table = SymbolTable::new();

        // Declare outer
        table
            .declare(create_test_symbol_with_type(
                "x",
                SymbolKind::Variable,
                Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default()),
            ))
            .unwrap();

        // Enter inner scope and shadow
        table.enter_scope();
        table
            .declare(create_test_symbol_with_type(
                "x",
                SymbolKind::Const,
                Type::new(TypeKind::Primitive(PrimitiveType::String), Span::default()),
            ))
            .unwrap();

        let found = table.lookup("x").unwrap();
        assert_eq!(found.kind, SymbolKind::Const);

        // Exit scope, should see outer again
        table.exit_scope();
        let found = table.lookup("x").unwrap();
        assert_eq!(found.kind, SymbolKind::Variable);
    }

    #[test]
    fn test_symbol_table_lookup_local() {
        let mut table = SymbolTable::new();

        table
            .declare(create_test_symbol("outer", SymbolKind::Variable))
            .unwrap();
        table.enter_scope();
        table
            .declare(create_test_symbol("inner", SymbolKind::Variable))
            .unwrap();

        // lookup_local should only see current scope
        assert!(table.lookup_local("inner").is_some());
        assert!(table.lookup_local("outer").is_none()); // Not in current scope
    }

    #[test]
    fn test_symbol_table_add_reference() {
        let mut table = SymbolTable::new();
        let symbol = create_test_symbol("my_var", SymbolKind::Variable);
        table.declare(symbol).unwrap();

        let span = Span::new(10, 20, 1, 0);
        assert!(table.add_reference("my_var", span));

        let found = table.lookup("my_var").unwrap();
        assert_eq!(found.references.len(), 1);
        assert_eq!(found.references[0].start, 10);
        assert_eq!(found.references[0].end, 20);
    }

    #[test]
    fn test_symbol_table_add_reference_in_nested_scope() {
        let mut table = SymbolTable::new();

        table
            .declare(create_test_symbol("outer", SymbolKind::Variable))
            .unwrap();
        table.enter_scope();

        // References added in nested scope modify the actual parent scope symbol
        let span = Span::new(5, 10, 1, 0);
        assert!(table.add_reference("outer", span));

        // After exiting the scope, the reference persists on the parent symbol
        table.exit_scope();
        let found = table.lookup("outer").unwrap();
        assert_eq!(found.references.len(), 1);
        assert_eq!(found.references[0].start, 5);
    }

    #[test]
    fn test_symbol_table_add_reference_not_found() {
        let mut table = SymbolTable::new();
        let span = Span::new(10, 20, 1, 0);
        assert!(!table.add_reference("nonexistent", span));
    }

    #[test]
    fn test_symbol_table_all_visible_symbols() {
        let mut table = SymbolTable::new();

        table
            .declare(create_test_symbol("a", SymbolKind::Variable))
            .unwrap();
        table.enter_scope();
        table
            .declare(create_test_symbol("b", SymbolKind::Function))
            .unwrap();
        table.enter_scope();
        table
            .declare(create_test_symbol("c", SymbolKind::Class))
            .unwrap();

        let visible = table.all_visible_symbols();
        assert_eq!(visible.len(), 3);
        assert!(visible.contains_key("a"));
        assert!(visible.contains_key("b"));
        assert!(visible.contains_key("c"));
    }

    #[test]
    fn test_symbol_table_all_visible_symbols_shadowing() {
        let mut table = SymbolTable::new();

        table
            .declare(create_test_symbol_with_type(
                "x",
                SymbolKind::Variable,
                Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default()),
            ))
            .unwrap();
        table.enter_scope();
        table
            .declare(create_test_symbol_with_type(
                "x",
                SymbolKind::Const,
                Type::new(TypeKind::Primitive(PrimitiveType::String), Span::default()),
            ))
            .unwrap();

        let visible = table.all_visible_symbols();
        assert_eq!(visible.len(), 1);
        let x = visible.get("x").unwrap();
        assert_eq!(x.kind, SymbolKind::Const); // Should see shadowed version
    }

    #[test]
    fn test_symbol_table_current_scope() {
        let mut table = SymbolTable::new();

        table
            .declare(create_test_symbol("outer", SymbolKind::Variable))
            .unwrap();
        table.enter_scope();
        table
            .declare(create_test_symbol("inner", SymbolKind::Variable))
            .unwrap();

        let current = table.current_scope();
        assert!(current.lookup_local("inner").is_some());
        // current_scope only shows current scope, not parent
    }

    // ========================================================================
    // Symbol Tests
    // ========================================================================

    #[test]
    fn test_symbol_new() {
        let typ = Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default());
        let symbol = Symbol::new(
            "my_var".to_string(),
            SymbolKind::Variable,
            typ,
            Span::new(0, 10, 1, 0),
        );

        assert_eq!(symbol.name, "my_var");
        assert_eq!(symbol.kind, SymbolKind::Variable);
        assert!(!symbol.is_exported);
        assert!(symbol.references.is_empty());
    }

    #[test]
    fn test_symbol_add_reference() {
        let typ = Type::new(TypeKind::Primitive(PrimitiveType::Number), Span::default());
        let mut symbol = Symbol::new(
            "my_var".to_string(),
            SymbolKind::Variable,
            typ,
            Span::new(0, 10, 1, 0),
        );

        symbol.add_reference(Span::new(20, 30, 1, 0));
        symbol.add_reference(Span::new(40, 50, 1, 0));

        assert_eq!(symbol.references.len(), 2);
        assert_eq!(symbol.references[0].start, 20);
        assert_eq!(symbol.references[1].start, 40);
    }

    #[test]
    fn test_symbol_kinds() {
        let kinds = vec![
            SymbolKind::Variable,
            SymbolKind::Const,
            SymbolKind::Function,
            SymbolKind::Class,
            SymbolKind::Interface,
            SymbolKind::TypeAlias,
            SymbolKind::Enum,
            SymbolKind::Parameter,
            SymbolKind::Namespace,
        ];

        for kind in kinds {
            let symbol = create_test_symbol("test", kind);
            assert_eq!(symbol.kind, kind);
        }
    }

    // ========================================================================
    // Edge Cases
    // ========================================================================

    #[test]
    fn test_exit_scope_at_root() {
        let mut table = SymbolTable::new();
        table.exit_scope(); // Should not panic
        assert!(table.lookup("anything").is_none());
    }

    #[test]
    fn test_empty_scope() {
        let scope = Scope::new();
        let symbols: Vec<_> = scope.symbols().collect();
        assert!(symbols.is_empty());
    }

    #[test]
    fn test_multiple_references_same_symbol() {
        let mut table = SymbolTable::new();
        table
            .declare(create_test_symbol("var", SymbolKind::Variable))
            .unwrap();

        for i in 0..100 {
            table.add_reference("var", Span::new(i * 10, i * 10 + 5, 1, 0));
        }

        let found = table.lookup("var").unwrap();
        assert_eq!(found.references.len(), 100);
    }

    #[test]
    fn test_declare_many_symbols() {
        let mut table = SymbolTable::new();

        for i in 0..1000 {
            let name = format!("var_{}", i);
            let symbol = create_test_symbol(&name, SymbolKind::Variable);
            table.declare(symbol).unwrap();
        }

        let visible = table.all_visible_symbols();
        assert_eq!(visible.len(), 1000);
    }

    #[test]
    fn test_deeply_nested_scopes() {
        let mut table = SymbolTable::new();

        // Create 100 nested scopes
        for i in 0..100 {
            table.enter_scope();
            let name = format!("level_{}", i);
            table
                .declare(create_test_symbol(&name, SymbolKind::Variable))
                .unwrap();
        }

        // Should be able to see all symbols from innermost scope
        for i in 0..100 {
            let name = format!("level_{}", i);
            assert!(table.lookup(&name).is_some());
        }

        // Exit all scopes
        for _ in 0..100 {
            table.exit_scope();
        }

        // Should be empty now
        assert!(table.all_visible_symbols().is_empty());
    }

    #[test]
    fn test_symbol_name_with_special_chars() {
        let mut table = SymbolTable::new();
        let names = vec!["x", "_x", "x1", "x_y", "X", "long_name_here"];

        for name in &names {
            let symbol = create_test_symbol(name, SymbolKind::Variable);
            table.declare(symbol).unwrap();
        }

        for name in &names {
            assert!(table.lookup(name).is_some());
        }
    }
}
