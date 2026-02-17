use luanext_parser::ast::types::Type;
use luanext_parser::span::Span;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// Kind of symbol (variable, function, class, etc.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolKind {
    Variable,
    Const,
    Function,
    Class,
    Interface,
    TypeAlias,
    Enum,
    Parameter,
    Namespace,
}

/// A symbol in the symbol table
#[derive(Debug, Clone)]
pub struct Symbol<'arena> {
    pub name: String,
    pub kind: SymbolKind,
    pub typ: Type<'arena>,
    pub span: Span,
    pub is_exported: bool,
    pub references: Vec<Span>,
}

impl<'arena> Symbol<'arena> {
    pub fn new(name: String, kind: SymbolKind, typ: Type<'arena>, span: Span) -> Self {
        Self {
            name,
            kind,
            typ,
            span,
            is_exported: false,
            references: Vec::new(),
        }
    }

    /// Add a reference to this symbol
    pub fn add_reference(&mut self, span: Span) {
        self.references.push(span);
    }
}

/// A scope containing symbols
#[derive(Debug, Clone)]
pub struct Scope<'arena> {
    symbols: FxHashMap<String, Symbol<'arena>>,
}

impl<'arena> Scope<'arena> {
    pub fn new() -> Self {
        Self {
            symbols: FxHashMap::with_capacity_and_hasher(32, Default::default()),
        }
    }

    /// Declare a symbol in this scope
    pub fn declare(&mut self, symbol: Symbol<'arena>) -> Result<(), String> {
        if self.symbols.contains_key(&symbol.name) {
            return Err(format!(
                "Symbol '{}' already declared in this scope",
                symbol.name
            ));
        }
        self.symbols.insert(symbol.name.clone(), symbol);
        Ok(())
    }

    /// Look up a symbol in this scope only
    pub fn lookup(&self, name: &str) -> Option<&Symbol<'arena>> {
        self.symbols.get(name)
    }

    /// Look up a symbol only in this scope (not parent scopes)
    pub fn lookup_local(&self, name: &str) -> Option<&Symbol<'arena>> {
        self.symbols.get(name)
    }

    /// Get all symbols in this scope
    pub fn symbols(&self) -> impl Iterator<Item = &Symbol<'arena>> {
        self.symbols.values()
    }
}

impl<'arena> Default for Scope<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

/// Symbol table managing scopes
#[derive(Debug)]
pub struct SymbolTable<'arena> {
    current_scope: Scope<'arena>,
    scope_stack: Vec<Scope<'arena>>,
}

impl<'arena> SymbolTable<'arena> {
    pub fn new() -> Self {
        Self {
            current_scope: Scope::new(),
            scope_stack: Vec::new(),
        }
    }

    /// Enter a new scope (O(1) - no cloning)
    pub fn enter_scope(&mut self) {
        let parent = std::mem::take(&mut self.current_scope);
        self.scope_stack.push(parent);
    }

    /// Exit current scope
    pub fn exit_scope(&mut self) {
        if let Some(parent) = self.scope_stack.pop() {
            self.current_scope = parent;
        }
    }

    /// Get the current scope depth (0 = global scope, >0 = nested scopes)
    pub fn scope_depth(&self) -> usize {
        self.scope_stack.len()
    }

    /// Declare a symbol in the current scope
    pub fn declare(&mut self, symbol: Symbol<'arena>) -> Result<(), String> {
        self.current_scope.declare(symbol)
    }

    /// Look up a symbol in current scope, then walk the scope stack (most recent first)
    pub fn lookup(&self, name: &str) -> Option<&Symbol<'arena>> {
        if let Some(symbol) = self.current_scope.symbols.get(name) {
            return Some(symbol);
        }
        for scope in self.scope_stack.iter().rev() {
            if let Some(symbol) = scope.symbols.get(name) {
                return Some(symbol);
            }
        }
        None
    }

    /// Look up a symbol only in the current scope
    pub fn lookup_local(&self, name: &str) -> Option<&Symbol<'arena>> {
        self.current_scope.lookup_local(name)
    }

    /// Add a reference to a symbol
    /// Returns true if the symbol was found and reference was added
    pub fn add_reference(&mut self, name: &str, span: Span) -> bool {
        // Try current scope first
        if let Some(symbol) = self.current_scope.symbols.get_mut(name) {
            symbol.add_reference(span);
            return true;
        }

        // Walk the scope stack (most recent first)
        for scope in self.scope_stack.iter_mut().rev() {
            if let Some(symbol) = scope.symbols.get_mut(name) {
                symbol.add_reference(span);
                return true;
            }
        }

        false
    }

    /// Get the current scope
    pub fn current_scope(&self) -> &Scope<'arena> {
        &self.current_scope
    }

    /// Mark a symbol as exported by name
    /// Returns true if the symbol was found and marked
    pub fn mark_exported(&mut self, name: &str) -> bool {
        // Try current scope first
        if let Some(symbol) = self.current_scope.symbols.get_mut(name) {
            symbol.is_exported = true;
            return true;
        }

        // Walk the scope stack (most recent first)
        for scope in self.scope_stack.iter_mut().rev() {
            if let Some(symbol) = scope.symbols.get_mut(name) {
                symbol.is_exported = true;
                return true;
            }
        }

        false
    }

    /// Get all symbols visible from the current scope (current + all parent scopes on stack)
    pub fn all_visible_symbols(&self) -> FxHashMap<String, &Symbol<'arena>> {
        let mut result = FxHashMap::default();

        // Add from oldest scope to newest so newer scopes shadow older ones
        for scope in &self.scope_stack {
            for (name, symbol) in &scope.symbols {
                result.insert(name.clone(), symbol);
            }
        }

        // Current scope shadows everything
        for (name, symbol) in &self.current_scope.symbols {
            result.insert(name.clone(), symbol);
        }

        result
    }
}

impl<'arena> Default for SymbolTable<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

/// Serializable representation of a symbol with scope depth
#[derive(Debug, Clone, Serialize)]
pub struct SerializableSymbol {
    pub name: String,
    pub kind: SymbolKind,
    pub typ: Type<'static>,
    pub span: Span,
    pub is_exported: bool,
    pub references: Vec<Span>,
    pub scope_depth: usize,
}

/// Serializable representation of SymbolTable (flattened scopes)
#[derive(Debug, Clone, Serialize)]
pub struct SerializableSymbolTable {
    pub symbols: Vec<SerializableSymbol>,
}

// NOTE: to_serializable/from_serializable removed during arena migration.
// Export type serialization is now handled by SerializableModuleExports in
// luanext_core::cache::serializable_types, which converts Type<'arena> to
// owned SerializableType for cache persistence.

#[cfg(test)]
mod tests {
    use super::*;
    use luanext_parser::ast::types::{PrimitiveType, TypeKind};

    fn make_test_type() -> Type<'static> {
        Type::new(
            TypeKind::Primitive(PrimitiveType::Number),
            Span::new(0, 0, 0, 0),
        )
    }

    #[test]
    fn test_scope_declare_and_lookup() {
        let mut scope = Scope::new();
        let symbol = Symbol::new(
            "x".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );

        scope.declare(symbol).unwrap();
        assert!(scope.lookup("x").is_some());
        assert!(scope.lookup("y").is_none());
    }

    #[test]
    fn test_scope_duplicate_declaration() {
        let mut scope = Scope::new();
        let symbol1 = Symbol::new(
            "x".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );
        let symbol2 = Symbol::new(
            "x".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );

        scope.declare(symbol1).unwrap();
        assert!(scope.declare(symbol2).is_err());
    }

    #[test]
    fn test_symbol_table_scopes() {
        let mut table = SymbolTable::new();

        // Declare in global scope
        let symbol1 = Symbol::new(
            "x".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );
        table.declare(symbol1).unwrap();

        // Enter new scope
        table.enter_scope();

        // Should still see x from parent scope via stack walk
        assert!(table.lookup("x").is_some());

        // Declare y in inner scope
        let symbol2 = Symbol::new(
            "y".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );
        table.declare(symbol2).unwrap();

        assert!(table.lookup("y").is_some());

        // Exit scope
        table.exit_scope();

        // y should no longer be visible
        assert!(table.lookup("y").is_none());
        // x should still be visible
        assert!(table.lookup("x").is_some());
    }

    #[test]
    fn test_symbol_table_shadowing() {
        let mut table = SymbolTable::new();

        // Declare x in global scope
        let symbol1 = Symbol::new(
            "x".to_string(),
            SymbolKind::Variable,
            make_test_type(),
            Span::new(0, 0, 0, 0),
        );
        table.declare(symbol1).unwrap();

        // Enter new scope and shadow x
        table.enter_scope();
        let symbol2 = Symbol::new(
            "x".to_string(),
            SymbolKind::Const,
            make_test_type(),
            Span::new(1, 1, 1, 1),
        );
        table.declare(symbol2).unwrap();

        // Should see the inner x
        let x = table.lookup("x").unwrap();
        assert_eq!(x.kind, SymbolKind::Const);

        // Exit scope
        table.exit_scope();

        // Should see the outer x again
        let x = table.lookup("x").unwrap();
        assert_eq!(x.kind, SymbolKind::Variable);
    }
}
