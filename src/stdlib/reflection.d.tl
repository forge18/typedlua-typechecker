-- TypedLua Standard Library: Reflection Module
-- Runtime reflection utilities for TypedLua classes

declare namespace Reflect {
  export function getFields(obj: unknown): unknown
  export function getMethods(obj: unknown): unknown
  export function isInstance(obj: unknown, classRef: unknown): boolean
  export function getType(obj: unknown): unknown
  export function getOwnFields(obj: unknown): unknown
  export function getOwnMethods(obj: unknown): unknown
}
