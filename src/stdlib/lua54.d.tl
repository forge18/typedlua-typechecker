-- TypedLua Standard Library: Lua 5.4
-- Complete type definitions for all Lua 5.4 standard libraries

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
  -- Repeats a string n times with optional separator.
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

  ---
  -- Dumps a function as a binary chunk.
  export function dump(func: callable, strip?: boolean): string

  ---
  -- Packs values into a binary string.
  export function pack(fmt: string, ...values: unknown[]): string

  ---
  -- Unpacks values from a binary string.
  export function unpack(fmt: string, s: string, pos?: number): ...unknown[]

  ---
  -- Returns the size of a format string.
  export function packsize(fmt: string): number
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
  export function pack<T>(...args: T[]): { n: number, [number]: T }

  ---
  -- Unpacks a table into multiple values.
  export function unpack<T>(list: T[], i?: number, j?: number): ...T[]

  ---
  -- Moves elements between tables.
  export function move<T>(a1: T[], f: number, e: number, t: number, a2?: T[]): T[]
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
  export function atan(y: number, x: number): number

  ---
  -- Returns the smallest integer >= x.
  export function ceil(x: number): number

  ---
  -- Returns the cosine of x (in radians).
  export function cos(x: number): number

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
  -- Returns a huge value (infinity).
  export const huge: number

  ---
  -- Returns the natural logarithm of x.
  export function log(x: number, base?: number): number

  ---
  -- Returns the maximum value among arguments.
  export function max(...args: number[]): number

  ---
  -- Returns x^y.
  export function pow(x: number, y: number): number

  ---
  -- Returns the maximum integer value.
  export const maxinteger: number

  ---
  -- Returns the minimum value among arguments.
  export function min(...args: number[]): number

  ---
  -- Returns the minimum integer value.
  export const mininteger: number

  ---
  -- Returns the integral and fractional parts of x.
  export function modf(x: number): (number, number)

  ---
  -- The value of pi.
  export const pi: number

  ---
  -- Converts from degrees to radians.
  export function rad(x: number): number

  ---
  -- Returns a pseudo-random number.
  -- Can now optionally use different RNG algorithms.
  export function random(): number
  export function random(m: number): number
  export function random(m: number, n: number): number

  ---
  -- Sets the seed for the random number generator.
  -- Can now return the random state for later restoration.
  export function randomseed(x?: number, y?: number): (number, number)

  ---
  -- Returns the sine of x (in radians).
  export function sin(x: number): number

  ---
  -- Returns the square root of x.
  export function sqrt(x: number): number

  ---
  -- Returns the tangent of x (in radians).
  export function tan(x: number): number

  ---
  -- Converts a number to an integer.
  export function tointeger(x: number): Nullable<number>

  ---
  -- Returns the type of a number.
  export function type(x: number): Nullable<"integer" | "float">

  ---
  -- Unsigned integer less than comparison.
  export function ult(m: number, n: number): boolean
}

-- ============================================================================
-- UTF-8 Library
-- ============================================================================

declare namespace utf8 {
  ---
  -- The pattern that matches exactly one UTF-8 byte sequence.
  export const charpattern: string

  ---
  -- Receives zero or more integers, converts each to UTF-8 byte sequence.
  export function char(...codepoints: number[]): string

  ---
  -- Returns the codepoints of all characters in s.
  export function codes(s: string, lax?: boolean): () -> (number, number)

  ---
  -- Returns the position (in bytes) where encoding of the n-th character starts.
  export function offset(s: string, n: number, i?: number): Nullable<number>

  ---
  -- Returns the codepoints of the characters in s.
  export function codepoint(s: string, i?: number, j?: number, lax?: boolean): ...number[]

  ---
  -- Returns the number of UTF-8 characters in the string.
  export function len(s: string, i?: number, j?: number): Nullable<(number, number)>
}

-- ============================================================================
-- I/O Library
-- ============================================================================

declare interface File {
  close(): Nullable<(boolean, string, number)>
  flush(): boolean
  lines(...formats: (string | number)[]): () -> ...unknown[]
  read(...formats: (string | number)[]): ...unknown[]
  seek(whence?: "set" | "cur" | "end", offset?: number): Nullable<(number, string)>
  setvbuf(mode: "no" | "full" | "line", size?: number): void
  write(...args: (string | number)[]): Nullable<(File, string)>
}

declare namespace io {
  export function close(file?: File): Nullable<(boolean, string, number)>
  export function flush(): boolean
  export function open(filename: string, mode?: string): Nullable<(File, string, number)>
  export function input(file?: File | string): File
  export function output(file?: File | string): File
  export function lines(filename?: string, ...formats: (string | number)[]): () -> ...unknown[]
  export function read(...formats: (string | number)[]): ...unknown[]
  export function tmpfile(): Nullable<File>
  export function type(obj: unknown): Nullable<"file" | "closed file">
  export function write(...args: (string | number)[]): Nullable<(File, string)>
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
  export function remove(filename: string): Nullable<(boolean, string, number)>
  export function rename(oldname: string, newname: string): Nullable<(boolean, string, number)>
  export function setlocale(locale: string, category?: string): Nullable<string>
  export function time(table?: DateTable): number
  export function tmpname(): string
  export function clock(): number
}

-- ============================================================================
-- Coroutine Library
-- ============================================================================

declare namespace coroutine {
  export function create(func: callable): coroutine
  export function resume(co: coroutine, ...args: unknown[]): (true, ...unknown[]) | (false, string)
  export function running(): (Nullable<coroutine>, boolean)
  export function status(co: coroutine): "running" | "suspended" | "normal" | "dead"
  export function wrap(func: callable): (...args: unknown[]) -> ...unknown[]
  export function yield(...args: unknown[]): ...unknown[]
  export function isyieldable(): boolean

  ---
  -- Closes a coroutine.
  -- New in Lua 5.4.
  export function close(co: coroutine): Nullable<(boolean, unknown)>
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
  ftransfer?: number
  ntransfer?: number
}

declare namespace debug {
  export function debug(): void
  export function gethook(thread?: thread): (callable, string, number)
  export function getinfo(thread: thread, func: callable | number, what?: string): Nullable<DebugInfo>
  export function getinfo(func: callable | number, what?: string): Nullable<DebugInfo>
  export function getlocal(thread: thread, level: number, local: number): Nullable<(string, unknown)>
  export function getlocal(level: number, local: number): Nullable<(string, unknown)>
  export function getmetatable(object: unknown): Nullable<table>
  export function getregistry(): table
  export function getupvalue(func: callable, up: number): Nullable<(string, unknown)>
  export function getuservalue(u: userdata, n?: number): unknown
  export function sethook(thread: thread, hook: callable, mask: string, count?: number): void
  export function sethook(hook: callable, mask: string, count?: number): void
  export function setlocal(thread: thread, level: number, local: number, value: unknown): Nullable<string>
  export function setlocal(level: number, local: number, value: unknown): Nullable<string>
  export function setmetatable(object: unknown, metatable: Nullable<table>): unknown
  export function setupvalue(func: callable, up: number, value: unknown): Nullable<string>
  export function setuservalue(u: userdata, value: unknown, n?: number): userdata
  export function traceback(thread: thread, message?: string, level?: number): string
  export function traceback(message?: string, level?: number): string
  export function upvalueid(func: callable, n: number): unknown
  export function upvaluejoin(f1: callable, n1: number, f2: callable, n2: number): void

  ---
  -- Sets a C closure to be called when code reaches certain events.
  -- New in Lua 5.4.
  export function setcstacklimit(limit: number): number
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
  export const searchers: callable[]

  export function loadlib(libname: string, funcname: string): Nullable<callable>
  export function searchpath(name: string, path: string, sep?: string, rep?: string): Nullable<(string, string)>
}

-- ============================================================================
-- Lua 5.4 Specific Globals
-- ============================================================================

---
-- Emits a warning message.
-- New in Lua 5.4.
declare function warn(...messages: string[]): void
