# TypedLua Typechecker

A standalone type checker for TypedLua, extracted from typedlua-core.

## About

This project provides comprehensive type checking for TypedLua, including:

- **Type compatibility checking** - Structural and nominal type compatibility
- **Generic types** - Full support for type parameters and constraints
- **Type narrowing** - Control flow-based type refinement
- **Utility types** - Pick, Omit, Keyof, conditional types, mapped types
- **Symbol tracking** - Complete symbol table with scope management
- **Module system** - Multi-module compilation with dependency resolution
- **Standard library** - Built-in type definitions

## Project Structure

```text
src/
├── lib.rs              # Public API
├── type_checker.rs     # Main TypeChecker implementation
├── symbol_table.rs     # Symbol tracking and scoping
├── type_compat.rs      # Type compatibility checking
├── type_environment.rs # Type environment management
├── generics.rs         # Generic type handling
├── narrowing.rs        # Control flow type narrowing
├── utility_types.rs    # Utility type evaluation
├── state/              # Type checker state management
├── visitors/           # AST visitor patterns
│   ├── access_control.rs
│   └── inference.rs
├── module_resolver/    # Module resolution
├── stdlib/             # Standard library definitions
├── config.rs           # Compiler configuration
├── diagnostics.rs      # Error reporting
└── fs.rs               # File system abstraction
```

## Dependencies

- `typedlua-parser` - AST and parsing infrastructure
- `rustc-hash` - Fast hashing for internal data structures
- `serde` - Serialization support
- `indexmap` - Ordered maps for deterministic output
- `thiserror` - Error handling

## Installation

```bash
cargo build --release
```

## Development

```bash
# Run tests
cargo test

# Build
cargo build

# Format code
cargo fmt

# Lint
cargo clippy
```

## License

See [LICENSE](LICENSE) for details.
