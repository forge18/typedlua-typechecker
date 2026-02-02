-- TypedLua Standard Library: Lua 5.2
-- Complete type definitions for all Lua 5.2 standard libraries

-- ============================================================================
-- String Library
-- ============================================================================

declare namespace string {
  ---
  -- Converts string to uppercase.
  export function upper(s: string): string

  ---
  -- Converts string to lowercase.
  export function lower(s: string): string

  ---
  -- Returns the length of a string.
  export function len(s: string): number

  ---
  -- Extracts a substring.
  export function sub(s: string, i: number, j?: number): string

  ---
  -- Finds a pattern in a string.
  export function find(s: string, pattern: string, init?: number, plain?: boolean): (number, number) | (nil, nil)

  ---
  -- Matches a pattern against a string.
  export function match(s: string, pattern: string, init?: number): ...string[]

  ---
  -- Returns an iterator for pattern matches.
  export function gmatch(s: string, pattern: string): () -> ...string[]

  ---
  -- Substitutes pattern matches with replacement.
  export function gsub(s: string, pattern: string, repl: string | table | ((match: string) -> string), n?: number): (string, number)

  ---
  -- Reverses a string.
  export function reverse(s: string): string

  ---
  -- Repeats a string n times.
  export function rep(s: string, n: number, sep?: string): string

  ---
  -- Formats a string using printf-style format specifiers.
  export function format(formatstring: string, ...args: unknown[]): string

  ---
  -- Returns byte values of characters.
  export function byte(s: string, i?: number, j?: number): ...number[]

  ---
  -- Converts byte values to a string.
  export function char(...bytes: number[]): string
}

-- ============================================================================
-- Table Library
-- ============================================================================

declare namespace table {
  ---
  -- Inserts an element into a table.
  export function insert<T>(list: T[], pos: number, value: T): void
  export function insert<T>(list: T[], value: T): void

  ---
  -- Removes an element from a table.
  export function remove<T>(list: T[], pos?: number): Nullable<T>

  ---
  -- Concatenates table elements into a string.
  export function concat(list: (string | number)[], sep?: string, i?: number, j?: number): string

  ---
  -- Sorts table elements in place.
  export function sort<T>(list: T[], comp?: (a: T, b: T) -> boolean): void

  ---
  -- Packs values into a table with n field.
  -- New in Lua 5.2.
  export function pack<T>(...args: T[]): { n: number, [number]: T }

  ---
  -- Unpacks a table into multiple values.
  -- New in Lua 5.2 (was global in 5.1).
  export function unpack<T>(list: T[], i?: number, j?: number): ...T[]
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
  export function frexp(x: number): (number, number)

  ---
  -- Returns a huge value (infinity).
  export const huge: number

  ---
  -- Returns m * 2^e.
  export function ldexp(m: number, e: number): number

  ---
  -- Returns the natural logarithm of x.
  -- Can now accept optional base parameter in 5.2.
  export function log(x: number, base?: number): number

  ---
  -- Deprecated in Lua 5.2 (use log(x, 10)).
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
-- Bit32 Library (New in Lua 5.2)
-- ============================================================================

declare namespace bit32 {
  ---
  -- Returns the bitwise AND of its operands.
  export function band(...args: number[]): number

  ---
  -- Returns the bitwise OR of its operands.
  export function bor(...args: number[]): number

  ---
  -- Returns the bitwise XOR of its operands.
  export function bxor(...args: number[]): number

  ---
  -- Returns the bitwise NOT of x.
  export function bnot(x: number): number

  ---
  -- Returns the bitwise test (all bits set in mask are set in x).
  export function btest(...args: number[]): boolean

  ---
  -- Returns x shifted left by disp bits.
  export function lshift(x: number, disp: number): number

  ---
  -- Returns x shifted right by disp bits (logical shift).
  export function rshift(x: number, disp: number): number

  ---
  -- Returns x rotated left by disp bits.
  export function lrotate(x: number, disp: number): number

  ---
  -- Returns x rotated right by disp bits.
  export function rrotate(x: number, disp: number): number

  ---
  -- Arithmetic right shift.
  export function arshift(x: number, disp: number): number

  ---
  -- Extracts bits from field to width.
  export function extract(n: number, field: number, width?: number): number

  ---
  -- Replaces bits in n with v.
  export function replace(n: number, v: number, field: number, width?: number): number
}

-- ============================================================================
-- I/O Library
-- ============================================================================

declare interface File {
  close(): boolean
  flush(): boolean
  lines(...formats: (string | number)[]): () -> ...unknown[]
  read(...formats: (string | number)[]): ...unknown[]
  seek(whence?: "set" | "cur" | "end", offset?: number): number
  setvbuf(mode: "no" | "full" | "line", size?: number): void
  write(...args: (string | number)[]): Nullable<File>
}

declare namespace io {
  export function close(file?: File): boolean
  export function flush(): boolean
  export function open(filename: string, mode?: string): Nullable<File>
  export function input(file?: File | string): File
  export function output(file?: File | string): File
  export function lines(filename?: string, ...formats: (string | number)[]): () -> ...unknown[]
  export function read(...formats: (string | number)[]): ...unknown[]
  export function tmpfile(): File
  export function type(obj: unknown): Nullable<"file" | "closed file">
  export function write(...args: (string | number)[]): Nullable<File>
  export function popen(prog: string, mode?: "r" | "w"): Nullable<File>

  export const stdin: File
  export const stdout: File
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
  export function date(format?: string, time?: number): string | DateTable
  export function difftime(t2: number, t1: number): number
  export function execute(command?: string): Nullable<(boolean, "exit" | "signal", number)>
  export function exit(code?: number | boolean, close?: boolean): never
  export function getenv(varname: string): Nullable<string>
  export function remove(filename: string): Nullable<boolean>
  export function rename(oldname: string, newname: string): Nullable<boolean>
  export function setlocale(locale: string, category?: string): Nullable<string>
  export function time(table?: DateTable): number
  export function tmpname(): string
  export function clock(): number
}

-- ============================================================================
-- Coroutine Library
-- ============================================================================

declare type coroutine = thread

declare namespace coroutine {
  export function create(func: callable): coroutine
  export function resume(co: coroutine, ...args: unknown[]): (true, ...unknown[]) | (false, string)
  export function running(): (Nullable<coroutine>, boolean)
  export function status(co: coroutine): "running" | "suspended" | "normal" | "dead"
  export function wrap(func: callable): (...args: unknown[]) -> ...unknown[]
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
  nparams?: number
  isvararg?: boolean
  linedefined?: number
  lastlinedefined?: number
  short_src?: string
  func?: callable
  activelines?: table
}

declare namespace debug {
  export function debug(): void
  export function getfenv(o: unknown): table
  export function gethook(thread?: thread): (callable, string, number)
  export function getinfo(thread: thread, func: callable | number, what?: string): Nullable<DebugInfo>
  export function getinfo(func: callable | number, what?: string): Nullable<DebugInfo>
  export function getlocal(thread: thread, level: number, local: number): Nullable<(string, unknown)>
  export function getlocal(level: number, local: number): Nullable<(string, unknown)>
  export function getmetatable(object: unknown): Nullable<table>
  export function getregistry(): table
  export function getupvalue(func: callable, up: number): Nullable<(string, unknown)>
  export function getuservalue(u: userdata): unknown
  export function setfenv(o: unknown, table: table): unknown
  export function sethook(thread: thread, hook: callable, mask: string, count?: number): void
  export function sethook(hook: callable, mask: string, count?: number): void
  export function setlocal(thread: thread, level: number, local: number, value: unknown): Nullable<string>
  export function setlocal(level: number, local: number, value: unknown): Nullable<string>
  export function setmetatable(object: unknown, metatable: table): unknown
  export function setupvalue(func: callable, up: number, value: unknown): Nullable<string>
  export function setuservalue(u: userdata, value: unknown): userdata
  export function traceback(thread: thread, message?: string, level?: number): string
  export function traceback(message?: string, level?: number): string
  export function upvalueid(func: callable, n: number): unknown
  export function upvaluejoin(f1: callable, n1: number, f2: callable, n2: number): void
}

-- ============================================================================
-- Package Library
-- ============================================================================

declare namespace package {
  export const loaded: { [string]: unknown }
  export const preload: { [string]: callable }
  export const path: string
  export const cpath: string
  export const config: string

  ---
  -- Searchers (renamed from loaders in 5.1).
  export const searchers: callable[]

  export function loadlib(libname: string, funcname: string): Nullable<callable>
  export function searchpath(name: string, path: string, sep?: string, rep?: string): Nullable<(string, string)>
}
