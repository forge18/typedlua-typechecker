-- TypedLua Standard Library: Built-in Functions
-- These are global functions available in all Lua versions

-- Utility type aliases
declare type Nullable<T> = T | nil

---
-- Prints the values to standard output.
-- Automatically converts values to strings using tostring().
-- @param ...args Values to print
declare function print(...args: unknown): void

---
-- Returns the type of the value as a string.
-- Possible return values: "nil", "boolean", "number", "string", "function", "table", "thread", "userdata"
-- @param value The value to check
-- @returns The type name as a string
declare function type(value: unknown): string

---
-- Converts a value to a string.
-- If the value has a __tostring metamethod, it will be called.
-- @param value The value to convert
-- @returns String representation of the value
declare function tostring(value: unknown): string

---
-- Converts a string or number to a number.
-- @param value The string or number to convert
-- @param base Optional base for conversion (2-36), default is 10
-- @returns The number, or nil if conversion failed
declare function tonumber(value: string | number, base?: number): Nullable<number>

---
-- Raises an error with the given message.
-- Never returns.
-- @param message Error message (can be unknown type)
-- @param level Optional stack level for error reporting (default: 1)
declare function error(message: unknown, level?: number): never

---
-- Checks if a condition is true. If not, raises an error.
-- @param condition The condition to check
-- @param message Optional error message
-- @returns The condition value if true
declare function assert<T>(condition: T, message?: string): T

---
-- Returns the length of a string or table.
-- For tables, returns the border (last consecutive integer index starting from 1).
-- For strings, returns the number of bytes.
-- @param value String or table to measure
-- @returns The length
declare function len(value: string | table): number

---
-- Alternative syntax for len() using the # operator
-- @param value String or table to measure
-- @returns The length
declare function rawlen(value: string | table): number

---
-- Returns an iterator function for generic for loops.
-- @param table The table to iterate
-- @returns Iterator function, table, and starting key
declare function pairs<K, V>(table: { [K]: V }): ((table: { [K]: V }, key?: K) -> (Nullable<K>, Nullable<V>), { [K]: V }, nil)

---
-- Returns an iterator function for sequential integer keys.
-- Iterates from index 1 to the table length.
-- @param table The table to iterate
-- @returns Iterator function, table, and starting index
declare function ipairs<V>(table: V[]): ((table: V[], index: number) -> (Nullable<number>, Nullable<V>), V[], 0)

---
-- Returns the next key-value pair in a table.
-- Used internally by pairs().
-- @param table The table to iterate
-- @param key The current key (nil to start)
-- @returns Next key and value, or nil if no more
declare function next<K, V>(table: { [K]: V }, key?: K): (Nullable<K>, Nullable<V>)

---
-- Sets or gets a metatable for a table.
-- @param table The table to modify
-- @param metatable The new metatable, or nil to remove
-- @returns The table
declare function setmetatable<T extends table, M extends table>(table: T, metatable: Nullable<M>): T & { __metatable?: M }

---
-- Gets the metatable of a table or other value.
-- If the metatable has a __metatable field, returns that instead.
-- @param value The value to inspect
-- @returns The metatable or nil
declare function getmetatable<T>(value: T): Nullable<table>

---
-- Performs a raw table get, bypassing metamethods.
-- @param table The table to access
-- @param key The key to look up
-- @returns The value at the key
declare function rawget<K, V>(table: { [K]: V }, key: K): Nullable<V>

---
-- Performs a raw table set, bypassing metamethods.
-- @param table The table to modify
-- @param key The key to set
-- @param value The value to store
-- @returns The table
declare function rawset<K, V>(table: { [K]: V }, key: K, value: V): { [K]: V }

---
-- Compares two values for equality, bypassing metamethods.
-- @param v1 First value
-- @param v2 Second value
-- @returns true if equal
declare function rawequal<T>(v1: T, v2: T): boolean

---
-- Selects arguments from a variable argument list.
-- If index is a number, returns all arguments from that index.
-- If index is "#", returns the count of arguments.
-- @param index The starting index or "#"
-- @param ...args The arguments
-- @returns Selected arguments
declare function select<T>(index: number | "#", ...args: T[]): unknown

---
-- Loads a chunk from a string or function.
-- Returns the compiled chunk as a function, or nil plus error message.
-- @param chunk String containing Lua code, or function returning code pieces
-- @param chunkname Optional name for error messages (default: chunk)
-- @param mode Optional mode: "t" for text, "b" for binary, "bt" for both (default: "bt")
-- @param env Optional environment table
-- @returns Compiled function or nil, plus error message
declare function load(
    chunk: string | (() -> Nullable<string>),
    chunkname?: string,
    mode?: "t" | "b" | "bt",
    env?: table
): (Nullable<() -> unknown>, Nullable<string>)

---
-- Loads a chunk from a file.
-- @param filename The file to load (nil for stdin)
-- @param mode Optional mode: "t" for text, "b" for binary, "bt" for both
-- @param env Optional environment table
-- @returns Compiled function or nil, plus error message
declare function loadfile(
    filename?: string,
    mode?: "t" | "b" | "bt",
    env?: table
): (Nullable<() -> unknown>, Nullable<string>)

---
-- Loads and executes a Lua file.
-- Removed in Lua 5.2+ (security risk).
-- @param filename The file to execute
-- @returns Return values from the executed chunk
declare function dofile(filename?: string): ...unknown

---
-- Executes a string as Lua code.
-- Removed in Lua 5.2+ (security risk, use load() instead).
-- @param code The Lua code to execute
-- @returns Return values from the executed code
declare function loadstring(code: string): ...unknown

---
-- Calls a function in protected mode.
-- Catches any errors and returns success status plus results or error.
-- @param func The function to call
-- @param ...args Arguments to pass to the function
-- @returns Success status, then results or error message
declare function pcall<T extends unknown[], R extends unknown[]>(
    func: (...args: T) -> ...R,
    ...args: T
): (true, ...R) | (false, string)

---
-- Calls a function with a custom error handler.
-- @param func The function to call
-- @param errorHandler Function to handle errors
-- @param ...args Arguments to pass to the function
-- @returns Results from func, or results from errorHandler
declare function xpcall<T extends unknown[], R extends unknown[]>(
    func: (...args: T) -> ...R,
    errorHandler: (error: unknown) -> unknown,
    ...args: T
): ...unknown

---
-- Returns multiple values from a list.
-- Helper for returning table contents as multiple values.
-- @param list The table to unpack
-- @param i Optional starting index (default: 1)
-- @param j Optional ending index (default: #list)
-- @returns Multiple values from the table
declare function unpack<T>(list: T[], i?: number, j?: number): ...T

---
-- Collects all arguments into a table.
-- In Lua 5.2+, moved to table.pack().
-- @param ...args Values to pack
-- @returns Table with values and 'n' field for count
declare function pack<T>(...args: T[]): { n: number, [number]: T }

---
-- Gets or sets the environment of a function or stack level.
-- Removed in Lua 5.2+ (replaced by _ENV).
-- @param funcOrLevel Function or stack level (0 = current, 1 = caller, etc.)
-- @returns The environment table
declare function getfenv(funcOrLevel?: callable | number): table

---
-- Sets the environment of a function or stack level.
-- Removed in Lua 5.2+ (replaced by _ENV).
-- @param funcOrLevel Function or stack level
-- @param table The new environment
-- @returns The function
declare function setfenv(funcOrLevel: callable | number, table: table): callable

---
-- Collects garbage.
-- @param opt Operation: "collect", "stop", "restart", "count", "step", "setpause", "setstepmul", "isrunning"
-- @param arg Optional argument for some operations
-- @returns Operation-dependent return value
declare function collectgarbage(opt?: "collect" | "stop" | "restart" | "count" | "step" | "setpause" | "setstepmul" | "isrunning", arg?: number): unknown

-- Global tables (defined in separate files)
declare const _G: table
declare const _VERSION: string

-- Module system (defined in separate file)
declare function require(modname: string): unknown
