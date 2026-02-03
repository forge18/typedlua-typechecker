# Code Organization Review

**Date:** 2026-02-01
**Scope:** TODO.md Section 7.2 - Code Organization
**Status:** Review Complete - Implementation Pending

## Executive Summary

Comprehensive review of TypedLua codebase organization covering:

- Architecture modularity and cognitive load
- Naming conventions
- DRY (Don't Repeat Yourself) and YAGNI (You Aren't Gonna Need It) principles
- File structure and readability
- Dependency Injection best practices

### Overall Assessment

The TypedLua codebase demonstrates **excellent inter-crate modularity** with clear separation between parser, core, CLI, and LSP. Naming conventions are perfect (100% Rust-compliant), and the DI pattern in `core/di.rs` is exemplary.

**However**, there are significant opportunities for improvement:

- **HIGH**: Code duplication in LSP providers (DRY violations)
- **HIGH**: Type checker cognitive load (4,603-line god object)
- **MEDIUM**: Inconsistent DI application in LSP providers
- **MEDIUM**: Large optimizer file needs decomposition

---

## Critical Issues & Solutions

### Issue #1: Duplicated `get_word_at_position()` Method

**Severity:** 🔴 HIGH
**Files Affected:** 4 providers

#### Problem

Nearly identical 37-line word-extraction method duplicated across:

- [hover.rs:120-156](../crates/typedlua-lsp/src/providers/hover.rs#L120-L156)
- [definition.rs:346-382](../crates/typedlua-lsp/src/providers/definition.rs#L346-L382)
- `references.rs`
- `rename.rs`

Each implements identical word-boundary detection logic. Any bug fix requires updating 4 locations.

#### Solution

**Extract to shared utility module**

Create `crates/typedlua-lsp/src/text_utils.rs`:

```rust
pub fn get_word_at_position(document: &Document, position: Position) -> Option<String> {
    // Consolidated implementation
}
```

Update providers to use:

```rust
use crate::text_utils;
// ...
let word = text_utils::get_word_at_position(document, position)?;
```

#### Effort

**Low** - ~2 hours

- Create text_utils.rs
- Move implementation
- Update 4 call sites
- Test

---

### Issue #2: Parser/Lexer Initialization Duplication

**Severity:** 🔴 HIGH
**Files Affected:** 13 providers (17 instances)

#### Problem

This 4-line initialization pattern repeats across all providers:

```rust
let handler = Arc::new(CollectingDiagnosticHandler::new());
let (interner, common_ids) = StringInterner::new_with_common_identifiers();
let mut lexer = Lexer::new(&document.text, handler.clone(), &interner);
let tokens = lexer.tokenize().ok()?;
```

Found in: `hover.rs`, `definition.rs`, `completion.rs`, `signature_help.rs`, `diagnostics.rs`, `semantic_tokens.rs`, `code_actions.rs`, and 6 more.

Changes to initialization strategy require updating 17 locations.

#### Solution

**Create ParserService for shared initialization**

Create `crates/typedlua-lsp/src/parser_service.rs`:

```rust
pub struct ParserService {
    interner: StringInterner,
    common_ids: CommonIdentifiers,
}

impl ParserService {
    pub fn new() -> Self {
        let (interner, common_ids) = StringInterner::new_with_common_identifiers();
        Self { interner, common_ids }
    }

    pub fn parse_document(&self, text: &str) -> Result<ParseResult, ParseError> {
        let handler = Arc::new(CollectingDiagnosticHandler::new());
        let mut lexer = Lexer::new(text, handler.clone(), &self.interner);
        let tokens = lexer.tokenize()?;
        // ... return tokens + metadata
        Ok(ParseResult { tokens, handler, /* ... */ })
    }
}
```

#### Effort

**Medium** - ~1 day

- Create ParserService
- Update 13 providers
- Test all LSP features

---

### Issue #3: Provider DI Violations

**Severity:** 🟡 MEDIUM
**Files Affected:** All 13 LSP providers + message_handler.rs

#### Problem

Providers create their own dependencies instead of receiving them via constructor:

```rust
impl HoverProvider {
    pub fn handle_request(...) {
        let handler = Arc::new(CollectingDiagnosticHandler::new());  // Hardcoded!
        let (interner, _) = StringInterner::new_with_common_identifiers();
        // ...
    }
}
```

And in message_handler.rs:

```rust
pub fn new() -> Self {
    Self {
        diagnostics_provider: DiagnosticsProvider::new(),  // Creates deps
        completion_provider: CompletionProvider::new(),
        // ...
    }
}
```

**Impact:**

- Cannot unit test providers in isolation
- Violates DI pattern established in `core/di.rs`
- Causes `#[allow(clippy::too_many_arguments)]` warnings

#### Solution

**Constructor Injection with ParserService**

```rust
// Provider with injected dependencies
pub struct HoverProvider {
    parser: Arc<ParserService>,
}

impl HoverProvider {
    pub fn new(parser: Arc<ParserService>) -> Self {
        Self { parser }
    }

    pub fn handle_request(&self, document: &Document, position: Position) -> Option<Hover> {
        let parse_result = self.parser.parse_document(&document.text)?;
        // Use parse_result...
    }
}

// MessageHandler with DI
impl MessageHandler {
    pub fn new(parser: Arc<ParserService>) -> Self {
        Self {
            diagnostics_provider: DiagnosticsProvider::new(parser.clone()),
            completion_provider: CompletionProvider::new(parser.clone()),
            hover_provider: HoverProvider::new(parser.clone()),
            // ...
        }
    }
}
```

#### Effort

**Medium** - ~2 days

- Update all 13 provider constructors
- Update MessageHandler instantiation
- Add unit tests for providers
- Update integration tests

---

### Issue #4: `type_checker.rs` God Object

**Severity:** 🔴 HIGH (Architectural)
**File:** [type_checker.rs](../crates/typedlua-core/src/typechecker/type_checker.rs) (4,603 lines)

#### Problem

Monolithic file with high cognitive load:

- Manages 8+ internal state machines
- Instantiates visitor patterns internally
- Mixes concerns: stdlib loading, module resolution, type checking, export tracking
- 50+ public methods
- Cannot test individual phases in isolation

#### Solution

**Comprehensive Three-Part Refactoring**

See detailed design in [Type Checker Refactoring Plan](#type-checker-refactoring-plan) below.

Summary:

1. **Lazy Stdlib Loading** - Make stdlib explicit, enable lightweight instances
2. **Extract Visitors** - All visitors in dedicated module
3. **Phase-Based Decomposition** - Split into InferencePhase, NarrowingPhase, ValidationPhase, ModulePhase

**Target:** Reduce type_checker.rs from 4,603 lines → ~600 lines coordinator

#### Effort

**High** - ~2-3 weeks

- Incremental refactoring across 5 phases
- Continuous integration testing
- See detailed migration strategy below

---

### Issue #5: `optimizer/passes.rs` Large File

**Severity:** 🟡 MEDIUM
**File:** [passes.rs](../crates/typedlua-core/src/optimizer/passes.rs) (5,069 lines)

#### Problem

Contains 10+ optimization pass implementations in a single file:

- Constant folding
- Dead code elimination
- Operator inlining
- Aggressive inlining
- Devirtualization
- And more...

Less severe than type_checker (passes are independent), but hard to navigate.

#### Solution

**One File Per Pass**

Restructure as:

```
optimizer/
├── mod.rs
├── optimization_pass.rs  # Trait definition
└── passes/
    ├── mod.rs
    ├── constant_folding.rs
    ├── dead_code_elimination.rs
    ├── operator_inlining.rs
    ├── aggressive_inlining.rs
    ├── devirtualization.rs
    ├── function_inlining.rs
    ├── string_concatenation.rs
    └── [other passes...]
```

Each pass file:

```rust
// passes/constant_folding.rs
use super::OptimizationPass;

pub struct ConstantFoldingPass;

impl OptimizationPass for ConstantFoldingPass {
    fn optimize(&mut self, program: &mut Program) -> Result<(), OptimizationError> {
        // Implementation
    }
}
```

#### Effort

**Medium** - ~1 week

- Extract each pass to separate file
- Update mod.rs exports
- Verify all optimizer tests pass

---

### Issue #6: Policy-Violating `#[allow(...)]` Directives

**Severity:** 🟡 MEDIUM
**Files:** 18 instances across codebase

#### Problem

Project policy ([CLAUDE.md](../CLAUDE.md)) forbids `#[allow(clippy::...)]` / `#[allow(dead_code)]` except in tests, but 18 violations exist:

- `#[allow(dead_code)]` on seemingly unused fields
- `#[allow(clippy::too_many_arguments)]` on provider methods (7 instances)
- `#[allow(dead_code)]` on placeholder methods like `completion.rs:347 resolve()`

#### Solution

**Audit & Fix Each Instance**

**Category 1: Too Many Arguments** (7 instances in providers)

- **Root Cause:** Providers pass many parameters instead of using DI
- **Fix:** Resolves automatically when Issue #3 (Provider DI) is fixed
- **Files:** hover.rs, definition.rs, completion.rs, etc.

**Category 2: Dead Code - Placeholders**

```rust
#[allow(dead_code)]
fn resolve(&self, item: CompletionItem) -> Option<CompletionItem> {
    // Would need full type information
    None
}
```

- **Fix:** Either implement or remove. If keeping for future:

```rust
#[cfg_attr(not(feature = "full_completion"), allow(dead_code))]
fn resolve(&self, item: CompletionItem) -> Option<CompletionItem> {
    todo!("Requires type checker integration")
}
```

**Category 3: Dead Code - Truly Unused**

- **Fix:** Delete the code entirely

**Category 4: Legitimate Test-Related**

- **Fix:** Ensure inside `#[cfg(test)]` blocks (allowed by policy)

#### Effort

**Low-Medium** - ~1 day

- Audit all 18 instances
- Fix or justify each
- Most resolve via DI refactoring

---

## Type Checker Refactoring Plan

### Overview

Comprehensive refactoring of [type_checker.rs](../crates/typedlua-core/src/typechecker/type_checker.rs) from 4,603-line god object to modular phase-based architecture.

### Proposed Structure

```
typechecker/
├── mod.rs                          # Public exports
├── type_checker.rs                 # Coordinator (~600 lines) ⬅ Main file
│
├── state/
│   ├── mod.rs
│   ├── type_checker_state.rs      # Shared state (~200 lines)
│   └── stdlib_loader.rs            # Stdlib loading (~300 lines)
│
├── phases/
│   ├── mod.rs
│   ├── inference_phase.rs          # Type inference (~800 lines)
│   ├── narrowing_phase.rs          # Type narrowing (~400 lines)
│   ├── validation_phase.rs         # Validation + access control (~800 lines)
│   ├── module_phase.rs             # Import/export handling (~500 lines)
│   └── declaration_phase.rs        # Declaration registration (~400 lines)
│
├── visitors/                       # Existing + consolidated
│   ├── mod.rs
│   ├── inference.rs                # Existing (~2300 lines)
│   ├── access_control.rs           # Existing (~334 lines)
│   └── narrowing.rs                # Moved from typechecker/narrowing.rs
│
├── helpers/                        # Extracted utilities
│   ├── mod.rs
│   ├── pattern_checker.rs          # Pattern helpers (~300 lines)
│   ├── type_resolver.rs            # Type resolution (~200 lines)
│   └── export_extractor.rs         # Export extraction (~200 lines)
│
└── [existing files unchanged]
    ├── symbol_table.rs
    ├── type_environment.rs
    ├── type_compat.rs
    ├── generics.rs
    ├── utility_types.rs
    └── tests.rs
```

### Three-Part Implementation

#### Part 1: Lazy Stdlib Loading

**Current Problem:**

```rust
// TypeChecker::new() automatically loads stdlib
if let Err(e) = checker.load_stdlib() {
    eprintln!("Warning: Failed to load stdlib: {}", e);
}
checker.register_minimal_stdlib();
```

All TypeChecker instances are heavy, cannot create lightweight instances for testing.

**Solution:**

```rust
impl TypeChecker {
    pub fn new(...) -> Self {
        // No stdlib loading
        Self { ... }
    }

    pub fn with_stdlib(mut self) -> Result<Self, String> {
        self.load_stdlib()?;
        self.register_minimal_stdlib();
        Ok(self)
    }

    // Backward compatibility
    pub fn new_with_stdlib(...) -> Result<Self, String> {
        Self::new(...).with_stdlib()
    }
}
```

**Migration:** Update 50+ test files to use `new_with_stdlib()`.

#### Part 2: Extract Visitors

**Goal:** Make all visitor instantiation explicit.

**Create TypeCheckerState:**

```rust
pub struct TypeCheckerState<'a> {
    pub symbol_table: SymbolTable,
    pub type_env: TypeEnvironment,
    pub narrowing: TypeNarrower,
    pub access_control: AccessControl,
    pub options: CompilerOptions,
    pub diagnostic_handler: Arc<dyn DiagnosticHandler>,
    pub interner: &'a StringInterner,
    pub common: &'a CommonIdentifiers,
    // Module-related
    pub module_registry: Option<Arc<ModuleRegistry>>,
    pub current_module_id: Option<ModuleId>,
    pub module_resolver: Option<Arc<ModuleResolver>>,
    // Tracking
    pub class_type_params: FxHashMap<String, Vec<TypeParameter>>,
    pub class_parents: FxHashMap<String, String>,
    pub exported_names: HashSet<String>,
}
```

All fields move from TypeChecker to TypeCheckerState.

#### Part 3: Phase-Based Decomposition

**Create distinct phases:**

```rust
// phases/inference_phase.rs
pub struct InferencePhase<'a> {
    state: &'a mut TypeCheckerState<'a>,
}

impl<'a> InferencePhase<'a> {
    pub fn check_variable_declaration(&mut self, decl: &mut VariableDeclaration)
        -> Result<(), TypeCheckError> {
        // Create TypeInferrer on-demand
        let mut inferrer = TypeInferrer::new(
            &mut self.state.symbol_table,
            &mut self.state.type_env,
            self.state.narrowing.get_context_mut(),
            &self.state.access_control,
            self.state.interner,
            &self.state.diagnostic_handler,
        );
        inferrer.check_variable_declaration(decl)
    }
}
```

**TypeChecker becomes coordinator:**

```rust
pub struct TypeChecker<'a> {
    state: TypeCheckerState<'a>,
}

impl<'a> TypeChecker<'a> {
    fn check_statement(&mut self, stmt: &mut Statement)
        -> Result<(), TypeCheckError> {
        match stmt {
            Statement::Variable(decl) => {
                let mut phase = InferencePhase::new(&mut self.state);
                phase.check_variable_declaration(decl)
            }
            Statement::Class(decl) => {
                let mut phase = ValidationPhase::new(&mut self.state);
                phase.check_class_declaration(decl)
            }
            // ... delegate to phases
        }
    }
}
```

### Migration Strategy

**Incremental Refactoring (Recommended):**

1. **Phase 1: Lazy Stdlib** (1-2 days)
   - Add `with_stdlib()` method
   - Update tests with automated search/replace
   - Keep automatic loading with deprecation warning

2. **Phase 2: Extract State** (2-3 days)
   - Create `state/type_checker_state.rs`
   - Move all fields to TypeCheckerState
   - Update TypeChecker to use `self.state.field`
   - Extract stdlib loading to `state/stdlib_loader.rs`

3. **Phase 3: Extract Helpers** (2-3 days)
   - Create `helpers/` module
   - Move pattern checking to `pattern_checker.rs`
   - Move export logic to `export_extractor.rs`
   - Move type resolution to `type_resolver.rs`

4. **Phase 4: Create Phases** (3-4 days)
   - Create `phases/` structure
   - Move inference methods to InferencePhase
   - Move validation methods to ValidationPhase
   - Move module methods to ModulePhase
   - Update TypeChecker to delegate

5. **Phase 5: Consolidate Visitors** (1-2 days)
   - Move `narrowing.rs` to `visitors/narrowing.rs`
   - Update `visitors/mod.rs` exports
   - Ensure consistent patterns

**Total Time:** ~2-3 weeks with continuous testing

### Testing Strategy

1. **Unit Tests for Phases:**

```rust
#[test]
fn test_inference_phase_variable_declaration() {
    let state = create_test_state();
    let mut phase = InferencePhase::new(&mut state);
    let result = phase.check_variable_declaration(&decl);
    assert!(result.is_ok());
}
```

1. **Integration Tests:** Keep existing 50+ tests, ensure all pass after each phase

2. **Regression Testing:**

```bash
cargo test --package typedlua-core > baseline.txt
# After each phase
cargo test --package typedlua-core > current.txt
diff baseline.txt current.txt
```

1. **Coverage Tracking:**

```bash
cargo tarpaulin --out Html --output-dir coverage/
```

Target: Maintain 70%+ throughout

### Backward Compatibility

All 10 existing public methods maintain identical signatures:

```rust
pub fn new(...) -> Self
pub fn with_options(self, options: CompilerOptions) -> Self
pub fn check_program(&mut self, program: &mut Program) -> Result<(), TypeCheckError>
pub fn extract_exports(&self, program: &Program) -> ModuleExports
pub fn get_module_dependencies(&self) -> &[PathBuf]
pub fn new_with_module_support(...) -> Self
// ... etc.
```

### Critical Files

1. `/crates/typedlua-core/src/typechecker/type_checker.rs` - Main refactoring target
2. `/crates/typedlua-core/src/typechecker/visitors/inference.rs` - Pattern reference
3. `/crates/typedlua-core/src/typechecker/visitors/access_control.rs` - Pattern reference
4. `/crates/typedlua-core/src/di.rs` - DI pattern reference
5. `/crates/typedlua-core/src/typechecker/tests.rs` - Test compatibility guide

---

## Architecture Review Results

### Strengths

#### Inter-Crate Modularity ✅

- **Excellent** separation: 6 crates with clear responsibilities
- Acyclic dependencies: cli → core → parser (correct layering)
- LSP optionally decoupled via feature-gating
- Parser has zero dependencies on core

#### Naming Conventions ✅

- **Perfect** adherence to Rust standards
- 100% snake_case files, PascalCase types
- Self-documenting module names
- Clear, descriptive identifiers

#### DI Pattern (Core) ✅

- Exemplary `core/di.rs` Container pattern
- Arc-based dependency injection
- Trait abstractions (DiagnosticHandler, FileSystem)
- Excellent testability

#### Code Generation ✅

- Well-modularized by feature (classes, enums, decorators)
- Clean strategy pattern for Lua versions
- Builder pattern for configuration

### Weaknesses

#### Type Checker Complexity ⚠️

- 4,603-line god object
- High cognitive load
- Mixed concerns
- Hard to test phases independently

#### LSP Provider Duplication ⚠️

- Word extraction duplicated 4x
- Parser initialization duplicated 17x

#### Inconsistent DI Application ⚠️

- Core uses DI excellently
- LSP providers violate DI principles
- Creates hardcoded dependencies

#### Large Files ⚠️

- `optimizer/passes.rs` (5,069 lines)
- `type_checker.rs` (4,603 lines)
- `parser/statement.rs` (3,613 lines)

---

## Implementation Roadmap

### Phase 1: Quick Wins (1 week)

**Priority: HIGH | Effort: LOW-MEDIUM**

1. ✅ Extract `get_word_at_position()` to text_utils.rs (~2 hours)
2. ✅ Create `ParserService` for shared initialization (~1 day)
3. ✅ Audit and fix `#[allow(...)]` directives (~1 day)

**Impact:** Eliminates most DRY violations, cleaner codebase

### Phase 2: Type Checker Refactoring (2-3 weeks)

**Priority: HIGH | Effort: HIGH**

1. ✅ Lazy stdlib loading (~2 days)
2. ✅ Extract state (~3 days)
3. ✅ Extract helpers (~3 days)
4. ✅ Create phases (~4 days)
5. ✅ Consolidate visitors (~2 days)

**Impact:** Dramatically reduced cognitive load, improved testability, better maintainability

### Phase 3: Optimizer Restructuring (1 week)

**Priority: MEDIUM | Effort: MEDIUM**

1. ✅ Extract each pass to separate file (~3 days)
2. ✅ Update module exports (~1 day)
3. ✅ Verify all tests pass (~1 day)

**Impact:** Better navigation, cleaner structure, easier to add passes

---

## Success Metrics

### Code Quality

- ✅ All files <1500 lines (except well-justified cases)
- ✅ Zero DRY violations in shared code paths
- ✅ Zero policy-violating `#[allow(...)]` directives
- ✅ Consistent DI application across all crates

### Testability

- ✅ 70%+ test coverage maintained throughout
- ✅ All providers unit testable in isolation
- ✅ Type checker phases independently testable
- ✅ Zero test regressions

### Maintainability

- ✅ Cognitive load <1000 lines per critical file
- ✅ Clear separation of concerns
- ✅ Self-documenting code structure
- ✅ Easy for new contributors to understand

### Performance

- ✅ No compilation time regression
- ✅ No runtime performance regression
- ✅ Benchmark before/after each major refactoring

---

## Appendix: File Size Analysis

### Current Large Files

| File | Lines | Status | Action |
|------|-------|--------|--------|
| optimizer/passes.rs | 5,069 | ⚠️ Too Large | Split into passes/ directory |
| type_checker.rs | 4,603 | ⚠️ Too Large | Comprehensive refactoring |
| parser/statement.rs | 3,613 | ⚠️ Large | Acceptable for complex grammar |
| visitors/inference.rs | 2,305 | ✅ OK | Well-scoped visitor |
| parser/expression.rs | 1,922 | ✅ OK | Complex grammar parsing |
| parser/types.rs | 1,506 | ✅ OK | TypeScript-style types |
| codegen/mod.rs | 1,341 | ✅ OK | Core generator logic |
| diagnostics.rs | 1,013 | ✅ OK | Comprehensive diagnostics |
| codegen/expressions.rs | 984 | ✅ OK | Expression codegen |

### Target State

| File | Current | Target | Change |
|------|---------|--------|--------|
| type_checker.rs | 4,603 | ~600 | -87% |
| optimizer/passes.rs | 5,069 | ~200 | -96% (split) |
| (new) phases/inference_phase.rs | - | ~800 | +800 |
| (new) phases/validation_phase.rs | - | ~800 | +800 |
| (new) phases/module_phase.rs | - | ~500 | +500 |

---

## References

- [ARCHITECTURE.md](ARCHITECTURE.md) - Overall system architecture
- [CLAUDE.md](../CLAUDE.md) - Project guidelines and policies
- [core/di.rs](../crates/typedlua-core/src/di.rs) - DI pattern reference
- [message_handler.rs](../crates/typedlua-lsp/src/message_handler.rs) - Current LSP implementation

---

**Next Steps:**

1. Review this document with the team
2. Prioritize implementation phases
3. Create tracking issues for each phase
4. Begin Phase 1: Quick Wins

Agent is calibrated...

