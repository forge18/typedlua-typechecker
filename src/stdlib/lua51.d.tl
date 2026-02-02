-- TypedLua Standard Library: Lua 5.1
-- Complete type definitions for all Lua 5.1 standard libraries

-- ============================================================================
-- String Library
-- ============================================================================

declare namespace string {
  ---
  -- Converts string to uppercase.
  -- @param s The string to convert
  -- @returns Uppercase version of the string
  export function upper(s: string): string

  ---
  -- Converts string to lowercase.
  -- @param s The string to convert
  -- @returns Lowercase version of the string
  export function lower(s: string): string

  ---
  -- Returns the length of a string.
  -- @param s The string to measure
  -- @returns The length in bytes
  export function len(s: string): number

  ---
  -- Extracts a substring.
  -- @param s The source string
  -- @param i Starting index (1-based, negative counts from end)
  -- @param j Optional ending index (default: -1, end of string)
  -- @returns The substring
  export function sub(s: string, i: number, j?: number): string

  ---
  -- Finds a pattern in a string.
  -- @param s The string to search in
  -- @param pattern The pattern to find
  -- @param init Optional starting position (default: 1)
  -- @param plain If true, pattern is treated as plain text
  -- @returns Start and end indices of match, or nil if not found
  export function find(s: string, pattern: string, init?: number, plain?: boolean): (number, number) | (nil, nil)

  ---
  -- Matches a pattern against a string.
  -- @param s The string to match against
  -- @param pattern The pattern to match
  -- @param init Optional starting position
  -- @returns Captured substrings or whole match
  export function match(s: string, pattern: string, init?: number): ...string[]

  ---
  -- Returns an iterator for pattern matches.
  -- @param s The string to search in
  -- @param pattern The pattern to match
  -- @returns Iterator function
  export function gmatch(s: string, pattern: string): () -> ...string[]

  ---
  -- Substitutes pattern matches with replacement.
  -- @param s The source string
  -- @param pattern The pattern to match
  -- @param repl Replacement string, table, or function
  -- @param n Optional max number of substitutions
  -- @returns Modified string and number of substitutions made
  export function gsub(s: string, pattern: string, repl: string | table | ((match: string) -> string), n?: number): (string, number)

  ---
  -- Reverses a string.
  -- @param s The string to reverse
  -- @returns Reversed string
  export function reverse(s: string): string

  ---
  -- Repeats a string n times.
  -- @param s The string to repeat
  -- @param n Number of repetitions
  -- @returns Repeated string
  export function rep(s: string, n: number): string

  ---
  -- Formats a string using printf-style format specifiers.
  -- @param formatstring Format string with % specifiers
  -- @param ...args Values to format
  -- @returns Formatted string
  export function format(formatstring: string, ...args: unknown[]): string

  ---
  -- Returns byte values of characters.
  -- @param s The source string
  -- @param i Optional starting index (default: 1)
  -- @param j Optional ending index (default: i)
  -- @returns Byte values
  export function byte(s: string, i?: number, j?: number): ...number[]

  ---
  -- Converts byte values to a string.
  -- @param ...bytes Byte values to convert
  -- @returns String from bytes
  export function char(...bytes: number[]): string
}

-- ============================================================================
-- Table Library
-- ============================================================================

declare namespace table {
  ---
  -- Inserts an element into a table.
  -- @param list The table to modify
  -- @param pos Optional position to insert at (default: end)
  -- @param value The value to insert
  export function insert<T>(list: T[], pos: number, value: T): void
  export function insert<T>(list: T[], value: T): void

  ---
  -- Removes an element from a table.
  -- @param list The table to modify
  -- @param pos Optional position to remove (default: end)
  -- @returns The removed value
  export function remove<T>(list: T[], pos?: number): Nullable<T>

  ---
  -- Concatenates table elements into a string.
  -- @param list Table of strings or numbers
  -- @param sep Optional separator (default: empty string)
  -- @param i Optional starting index (default: 1)
  -- @param j Optional ending index (default: #list)
  -- @returns Concatenated string
  export function concat(list: (string | number)[], sep?: string, i?: number, j?: number): string

  ---
  -- Sorts table elements in place.
  -- @param list The table to sort
  -- @param comp Optional comparison function (default: <)
  export function sort<T>(list: T[], comp?: (a: T, b: T) -> boolean): void

  ---
  -- Returns the maximum numeric index.
  -- Deprecated in Lua 5.1, use # operator instead.
  -- @param table The table to check
  -- @returns Maximum index
  export function maxn(table: table): number

  ---
  -- Executes a function for each element.
  -- Deprecated in Lua 5.2+.
  -- @param table The table to iterate
  -- @param func Function to call for each element
  export function foreach<K, V>(table: { [K]: V }, func: (key: K, value: V) -> void): void

  ---
  -- Executes a function for each numeric index.
  -- Deprecated in Lua 5.2+.
  -- @param table The table to iterate
  -- @param func Function to call for each element
  export function foreachi<T>(table: T[], func: (index: number, value: T) -> void): void
}

-- ============================================================================
-- Math Library
-- ============================================================================

declare namespace math {
  ---
  -- Returns the absolute value of a number.
  export function abs(x: number): number

  ---
  -- Returns the arc cosine of x (in radians).
  export function acos(x: number): number

  ---
  -- Returns the arc sine of x (in radians).
  export function asin(x: number): number

  ---
  -- Returns the arc tangent of x (in radians).
  export function atan(x: number): number

  ---
  -- Returns the arc tangent of y/x (in radians).
  export function atan2(y: number, x: number): number

  ---
  -- Returns the smallest integer >= x.
  export function ceil(x: number): number

  ---
  -- Returns the cosine of x (in radians).
  export function cos(x: number): number

  ---
  -- Returns the hyperbolic cosine of x.
  export function cosh(x: number): number

  ---
  -- Converts from radians to degrees.
  export function deg(x: number): number

  ---
  -- Returns e^x.
  export function exp(x: number): number

  ---
  -- Returns the largest integer <= x.
  export function floor(x: number): number

  ---
  -- Returns the remainder of x/y.
  export function fmod(x: number, y: number): number

  ---
  -- Extracts mantissa and exponent.
  -- @returns Mantissa (0.5 <= m < 1) and exponent (x = m * 2^e)
  export function frexp(x: number): (number, number)

  ---
  -- Returns a huge value (infinity).
  export const huge: number

  ---
  -- Returns m * 2^e.
  export function ldexp(m: number, e: number): number

  ---
  -- Returns the natural logarithm of x.
  export function log(x: number): number

  ---
  -- Returns the base-10 logarithm of x.
  export function log10(x: number): number

  ---
  -- Returns the maximum value among arguments.
  export function max(...args: number[]): number

  ---
  -- Returns the minimum value among arguments.
  export function min(...args: number[]): number

  ---
  -- Returns the integral and fractional parts of x.
  export function modf(x: number): (number, number)

  ---
  -- The value of pi.
  export const pi: number

  ---
  -- Returns x^y.
  export function pow(x: number, y: number): number

  ---
  -- Converts from degrees to radians.
  export function rad(x: number): number

  ---
  -- Returns a pseudo-random number.
  -- With no args: [0, 1)
  -- With m: [1, m]
  -- With m, n: [m, n]
  export function random(): number
  export function random(m: number): number
  export function random(m: number, n: number): number

  ---
  -- Sets the seed for the random number generator.
  export function randomseed(x: number): void

  ---
  -- Returns the sine of x (in radians).
  export function sin(x: number): number

  ---
  -- Returns the hyperbolic sine of x.
  export function sinh(x: number): number

  ---
  -- Returns the square root of x.
  export function sqrt(x: number): number

  ---
  -- Returns the tangent of x (in radians).
  export function tan(x: number): number

  ---
  -- Returns the hyperbolic tangent of x.
  export function tanh(x: number): number
}

-- ============================================================================
-- I/O Library
-- ============================================================================

declare interface File {
  ---
  -- Closes a file.
  close(): boolean

  ---
  -- Flushes buffered data to file.
  flush(): boolean

  ---
  -- Returns an iterator for reading lines.
  lines(): () -> Nullable<string>

  ---
  -- Reads from file according to format.
  read(...formats: (string | number)[]): ...unknown[]

  ---
  -- Sets the file position.
  -- @param whence "set", "cur", or "end"
  -- @param offset Offset from whence
  -- @returns New position
  seek(whence?: "set" | "cur" | "end", offset?: number): number

  ---
  -- Sets buffering mode.
  -- @param mode "no", "full", or "line"
  -- @param size Optional buffer size
  setvbuf(mode: "no" | "full" | "line", size?: number): void

  ---
  -- Writes to file.
  write(...args: (string | number)[]): Nullable<File>
}

declare namespace io {
  ---
  -- Closes a file (or default output).
  export function close(file?: File): boolean

  ---
  -- Flushes the default output file.
  export function flush(): boolean

  ---
  -- Opens a file.
  -- @param filename File to open
  -- @param mode "r", "w", "a", "r+", "w+", "a+" (can add "b" for binary)
  -- @returns File handle or nil plus error message
  export function open(filename: string, mode?: string): Nullable<File>

  ---
  -- Sets default input file.
  export function input(file?: File | string): File

  ---
  -- Sets default output file.
  export function output(file?: File | string): File

  ---
  -- Returns an iterator for reading lines from a file.
  export function lines(filename?: string): () -> Nullable<string>

  ---
  -- Reads from default input.
  export function read(...formats: (string | number)[]): ...unknown[]

  ---
  -- Opens a file in read mode.
  export function tmpfile(): File

  ---
  -- Returns the type of a file handle.
  -- @returns "file", "closed file", or nil
  export function type(obj: unknown): Nullable<"file" | "closed file">

  ---
  -- Writes to default output.
  export function write(...args: (string | number)[]): Nullable<File>

  ---
  -- Opens a program for reading or writing.
  export function popen(prog: string, mode?: "r" | "w"): Nullable<File>

  ---
  -- Standard input file.
  export const stdin: File

  ---
  -- Standard output file.
  export const stdout: File

  ---
  -- Standard error file.
  export const stderr: File
}

-- ============================================================================
-- OS Library
-- ============================================================================

declare interface DateTable {
  year: number
  month: number
  day: number
  hour?: number
  min?: number
  sec?: number
  wday?: number
  yday?: number
  isdst?: boolean
}

declare namespace os {
  ---
  -- Returns the current time or formats a time.
  -- @param format Optional format string (* for table)
  -- @param time Optional time value
  -- @returns Formatted string or date table
  export function date(format?: string, time?: number): string | DateTable

  ---
  -- Returns the difference between two times.
  export function difftime(t2: number, t1: number): number

  ---
  -- Executes a system command.
  -- @returns Exit status or nil
  export function execute(command?: string): Nullable<number>

  ---
  -- Exits the program.
  export function exit(code?: number): never

  ---
  -- Gets an environment variable.
  export function getenv(varname: string): Nullable<string>

  ---
  -- Deletes a file.
  export function remove(filename: string): Nullable<boolean>

  ---
  -- Renames a file.
  export function rename(oldname: string, newname: string): Nullable<boolean>

  ---
  -- Sets the current locale.
  -- @param locale Locale string
  -- @param category Optional category
  -- @returns Locale name or nil
  export function setlocale(locale: string, category?: string): Nullable<string>

  ---
  -- Returns the current time.
  -- @param table Optional date table
  -- @returns Time value (seconds since epoch)
  export function time(table?: DateTable): number

  ---
  -- Returns a temporary filename.
  export function tmpname(): string

  ---
  -- Returns CPU time used by program.
  export function clock(): number
}

-- ============================================================================
-- Coroutine Library
-- ============================================================================

declare type coroutine = thread

declare namespace coroutine {
  ---
  -- Creates a new coroutine.
  -- @param func Function to run in coroutine
  -- @returns Coroutine object
  export function create(func: callable): coroutine

  ---
  -- Resumes a coroutine.
  -- @param co Coroutine to resume
  -- @param ...args Arguments to pass
  -- @returns Success status and return values or error
  export function resume(co: coroutine, ...args: unknown[]): (true, ...unknown[]) | (false, string)

  ---
  -- Returns the running coroutine.
  -- @returns Current coroutine or nil if in main thread
  export function running(): Nullable<coroutine>

  ---
  -- Returns the status of a coroutine.
  -- @returns "running", "suspended", "normal", or "dead"
  export function status(co: coroutine): "running" | "suspended" | "normal" | "dead"

  ---
  -- Creates a coroutine and returns a function to resume it.
  export function wrap(func: callable): (...args: unknown[]) -> ...unknown[]

  ---
  -- Suspends the current coroutine.
  export function yield(...args: unknown[]): ...unknown[]
}

-- ============================================================================
-- Debug Library
-- ============================================================================

declare interface DebugInfo {
  name?: string
  namewhat?: string
  what?: string
  source?: string
  currentline?: number
  nups?: number
  linedefined?: number
  lastlinedefined?: number
  short_src?: string
  func?: callable
}

declare namespace debug {
  ---
  -- Returns debug information about a function.
  export function getinfo(func: callable | number, what?: string): Nullable<DebugInfo>

  ---
  -- Gets a local variable.
  export function getlocal(level: number, local: number): Nullable<(string, unknown)>

  ---
  -- Gets a metatable.
  export function getmetatable(object: unknown): Nullable<table>

  ---
  -- Gets an upvalue.
  export function getupvalue(func: callable, up: number): Nullable<(string, unknown)>

  ---
  -- Sets a local variable.
  export function setlocal(level: number, local: number, value: unknown): Nullable<string>

  ---
  -- Sets a metatable.
  export function setmetatable(object: unknown, metatable: table): unknown

  ---
  -- Sets an upvalue.
  export function setupvalue(func: callable, up: number, value: unknown): Nullable<string>

  ---
  -- Returns a traceback string.
  export function traceback(message?: string, level?: number): string

  ---
  -- Sets a debug hook.
  export function sethook(hook: callable, mask: string, count?: number): void

  ---
  -- Gets the current hook.
  export function gethook(): (callable, string, number)
}

-- ============================================================================
-- Package Library
-- ============================================================================

declare namespace package {
  ---
  -- Table of loaded modules.
  export const loaded: { [string]: unknown }

  ---
  -- Table of module loaders.
  export const loaders: callable[]

  ---
  -- Path for searching Lua modules.
  export const path: string

  ---
  -- Path for searching C modules.
  export const cpath: string

  ---
  -- Preloaded modules.
  export const preload: { [string]: callable }

  ---
  -- Loads a module.
  export function loadlib(libname: string, funcname: string): Nullable<callable>

  ---
  -- Searches for a loader for a module.
  export function searchpath(name: string, path: string, sep?: string, rep?: string): Nullable<string>

  ---
  -- Configuration string.
  export const config: string
}
