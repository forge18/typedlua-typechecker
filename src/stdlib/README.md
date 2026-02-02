# TypedLua Standard Library Definitions

This directory contains TypeScript-style type definition files (`.d.tl`) for Lua's standard library.

## Structure

- **`builtins.d.tl`** - Built-in global functions (print, type, assert, etc.)
- **`lua51.d.tl`** - Lua 5.1 standard library
- **`lua52.d.tl`** - Lua 5.2 standard library
- **`lua53.d.tl`** - Lua 5.3 standard library
- **`lua54.d.tl`** - Lua 5.4 standard library

## Usage

The compiler automatically loads the appropriate stdlib definitions based on the target Lua version specified in the project configuration.

## Format

These files use TypedLua's declaration syntax to define types for Lua's standard library:

```lua
-- Example from builtins.d.tl
declare function print(...args: any): void
declare function type(value: any): string
declare function tostring(value: any): string
declare function tonumber(value: string | number, base?: number): number | nil

-- Example from lua54.d.tl (string library)
declare namespace string {
    function upper(s: string): string
    function lower(s: string): string
    function len(s: string): number
    function sub(s: string, i: number, j?: number): string
    function find(s: string, pattern: string, init?: number, plain?: boolean): number | nil, number | nil
    function gsub(s: string, pattern: string, repl: string | table | function, n?: number): string, number
}
```

## Coverage

### Lua 5.1
- ✅ Built-in functions
- ✅ String library
- ✅ Table library
- ✅ Math library
- ✅ I/O library
- ✅ OS library
- ✅ Package library
- ✅ Coroutine library
- ✅ Debug library

### Lua 5.2+
Includes all 5.1 features plus version-specific additions:
- Lua 5.2: `bit32`, updated `string.pack`/`unpack`
- Lua 5.3: Integer division, bitwise operators
- Lua 5.4: `<const>`, `<close>`, `warn()`

## Contributing

When adding new definitions:
1. Follow existing naming conventions
2. Include JSDoc-style comments for documentation
3. Mark optional parameters with `?`
4. Use union types for multiple return values
5. Add version-specific features to the correct file

## References

- [Lua 5.1 Reference Manual](https://www.lua.org/manual/5.1/)
- [Lua 5.2 Reference Manual](https://www.lua.org/manual/5.2/)
- [Lua 5.3 Reference Manual](https://www.lua.org/manual/5.3/)
- [Lua 5.4 Reference Manual](https://www.lua.org/manual/5.4/)
