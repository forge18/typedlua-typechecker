# Type Checker Refactoring Progress

## Overview

This document tracks the ongoing refactoring of the monolithic `type_checker.rs` into a modular, phase-based architecture. The goal is to reduce cognitive load and improve maintainability by extracting self-contained functionality into dedicated modules.

## Current Status (2026-02-02)

### Line Count Reduction

| File | Original | Current | Reduction | Percentage |
|------|----------|---------|-----------|------------|
| **type_checker.rs** | 4,661 | 3,887 | -774 | -16.6% |

**Target**: ~600 lines (thin coordinator)
**Progress**: 774/4,061 lines extracted (19% of target)
**Remaining**: ~3,287 lines to extract

### Modules Created

#### Phase Modules (src/phases/)

1. **declaration_phase.rs** (369 lines)
   - `register_function_signature()` - Function signature registration for forward references
   - `declare_pattern()` - Recursive pattern destructuring (identifier, array, object, or-patterns)
   - `register_declare_function()` - Ambient function declarations
   - `register_declare_const()` - Ambient constant declarations
   - `register_declare_namespace()` - Namespace declarations with object type generation

2. **module_phase.rs** (446 lines)
   - `extract_exports()` - Export statement analysis and ModuleExports building
   - `check_import_statement()` - All import types (default, named, type-only, namespace, mixed)
   - `resolve_import_type()` - Import type resolution with dependency tracking
   - Handles re-exports from other modules

3. **validation_phase.rs** (518 lines)
   - `validate_interface_members()` - Duplicate property name checking
   - `validate_index_signature()` - Class property conformance to index signatures
   - `check_abstract_methods_implemented()` - Abstract method implementation verification
   - `check_method_override()` - Method override validation (contravariance/covariance)
   - `check_decorators()` - Decorator validation (kept in type_checker.rs due to borrow checker)
   - `check_decorator_expression()` - Decorator expression checking (kept in type_checker.rs)

**Total Phase Code**: 1,333 lines

#### Helper Modules (src/helpers/)

1. **type_utilities.rs** (241 lines with tests)
   - `widen_type()` - Literal type widening to base primitives
   - `is_boolean_type()` - Boolean type checking
   - `operator_kind_name()` - Operator to Lua metamethod mapping
   - `type_to_string()` - Human-readable type strings for error messages

#### State Modules (src/state/)

1. **stdlib_loader.rs** (160 lines)
   - `parse_stdlib_files()` - Pure stdlib parsing without type checking
   - Supports Lua 5.1, 5.2, 5.3, 5.4
   - Independently testable with 3 unit tests

### Visitor Consolidation

**Completed**: Moved `src/narrowing.rs` → `src/visitors/narrowing.rs` for consistency

All visitor pattern code now consolidated under `src/visitors/`:
- `narrowing.rs` (1,039 lines)
- `inference.rs` (2,305 lines)
- `access_control.rs` (333 lines)

### Delegations in type_checker.rs

Successfully delegated these methods to phase modules:

#### Declaration Phase
- `register_function_signature()` → declaration_phase
- `declare_pattern()` → declaration_phase
- `register_declare_function()` → declaration_phase
- `register_declare_const()` → declaration_phase
- `register_declare_namespace()` → declaration_phase

#### Module Phase
- `check_import_statement()` → module_phase
- Export extraction logic → module_phase

#### Validation Phase
- `validate_interface_members()` → validation_phase
- `validate_index_signature()` → validation_phase
- `check_abstract_methods_implemented()` → validation_phase
- `check_method_override()` → validation_phase

**Note**: `check_decorators` and `check_decorator_expression` remain in type_checker.rs due to Rust borrow checker constraints (require mutable self for expression type inference).

## Design Patterns

### Stateless Phase Functions

All extracted phase functions follow the pattern:
- Take explicit context parameters (symbol_table, type_env, access_control, interner, etc.)
- No encapsulated state
- Pure functions where possible
- Enables independent testing and flexible orchestration

Example:
```rust
pub fn register_function_signature(
    decl: &FunctionDeclaration,
    symbol_table: &mut SymbolTable,
    interner: &StringInterner,
) -> Result<(), TypeCheckError>
```

### Delegation Pattern

Methods in type_checker.rs delegate to phase modules:

```rust
fn register_function_signature(&mut self, decl: &FunctionDeclaration)
    -> Result<(), TypeCheckError>
{
    phases::declaration_phase::register_function_signature(
        decl,
        &mut self.symbol_table,
        self.interner,
    )
}
```

## Testing

✅ **All 400 tests passing** after each refactoring step

## Next Steps

### Remaining Extraction Opportunities

To reach the ~600-line coordinator target, approximately 3,287 more lines need extraction:

1. **Statement Checking Phase** (~800-1,000 lines estimated)
   - `check_variable_declaration()`
   - `check_if_statement()`
   - `check_while_statement()`
   - `check_for_statement()`
   - `check_return_statement()`
   - `check_throw_statement()`
   - `check_try_statement()`

2. **Type Resolution Helpers** (~300-400 lines estimated)
   - `resolve_type_reference()`
   - `evaluate_type()`
   - `deep_resolve_type()`

3. **Declaration Checking Phase** (~1,500+ lines estimated)
   - `check_class_declaration()` (~515 lines!)
   - `check_interface_declaration()`
   - `check_enum_declaration()`
   - `check_rich_enum_declaration()`
   - `check_type_alias()`

4. **Remaining Validation** (~200 lines)
   - `check_implements_assignable()`
   - Class member checking

### Challenges

1. **Borrow Checker Constraints**: Some methods require mutable access to multiple self fields simultaneously, making extraction difficult
2. **Deep Coupling**: Many methods call other methods that also need extraction
3. **State Management**: Some methods depend heavily on type_checker's mutable state

### Strategy

Continue extracting in this order:
1. ✅ Pure utility functions (type_utilities) - **DONE**
2. ✅ Module-level operations (imports/exports) - **DONE**
3. ✅ Symbol declarations (forward references) - **DONE**
4. ✅ Validation operations - **PARTIALLY DONE**
5. Statement checking logic - **NEXT**
6. Type resolution helpers
7. Complex declaration checking (classes, interfaces, enums)
8. Final coordinator simplification

## Benefits Achieved

1. **Improved Testability**: Phase functions can be tested independently
2. **Better Separation of Concerns**: Each phase has a clear, focused responsibility
3. **Reduced Cognitive Load**: Smaller, focused modules easier to understand
4. **Code Reusability**: Phase functions can be used by LSP, static analysis tools, etc.
5. **Easier Maintenance**: Changes to one phase don't affect others

## Metrics

- **Methods in type_checker.rs**: 84 (down from ~100+)
- **Average method size**: ~46 lines (improving, but still many large methods)
- **Largest remaining method**: `check_class_declaration()` (~515 lines)
- **Test Coverage**: 100% passing (400 tests)
