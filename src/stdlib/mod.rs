// Standard library type definitions embedded at compile time

use super::config::LuaVersion;

/// Builtin global functions (available in all Lua versions)
pub const BUILTINS: &str = include_str!("builtins.d.tl");

/// Lua 5.1 standard library
pub const LUA51: &str = include_str!("lua51.d.tl");

/// Lua 5.2 standard library
pub const LUA52: &str = include_str!("lua52.d.tl");

/// Lua 5.3 standard library
pub const LUA53: &str = include_str!("lua53.d.tl");

/// Lua 5.4 standard library
pub const LUA54: &str = include_str!("lua54.d.tl");

/// Reflection runtime module (available in all Lua versions)
pub const REFLECTION: &str = include_str!("reflection.d.tl");

/// Get the appropriate stdlib content based on Lua version
pub fn get_stdlib(version: LuaVersion) -> &'static str {
    match version {
        LuaVersion::Lua51 => LUA51,
        LuaVersion::Lua52 => LUA52,
        LuaVersion::Lua53 => LUA53,
        LuaVersion::Lua54 => LUA54,
    }
}

/// Get all stdlib sources (builtins + version-specific + reflection)
pub fn get_all_stdlib(version: LuaVersion) -> Vec<(&'static str, &'static str)> {
    vec![
        ("builtins.d.tl", BUILTINS),
        (
            match version {
                LuaVersion::Lua51 => "lua51.d.tl",
                LuaVersion::Lua52 => "lua52.d.tl",
                LuaVersion::Lua53 => "lua53.d.tl",
                LuaVersion::Lua54 => "lua54.d.tl",
            },
            get_stdlib(version),
        ),
        ("reflection.d.tl", REFLECTION),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builtins_embedded() {
        assert!(!BUILTINS.is_empty());
        assert!(BUILTINS.contains("declare function print"));
        assert!(BUILTINS.contains("declare function type"));
    }

    #[test]
    fn test_lua51_embedded() {
        assert!(!LUA51.is_empty());
        assert!(LUA51.contains("declare namespace string"));
        assert!(LUA51.contains("declare namespace table"));
    }

    #[test]
    fn test_lua52_embedded() {
        assert!(!LUA52.is_empty());
        assert!(LUA52.contains("declare namespace bit32"));
        assert!(!LUA52.contains("table.maxn")); // Removed in 5.2
    }

    #[test]
    fn test_lua53_embedded() {
        assert!(!LUA53.is_empty());
        assert!(LUA53.contains("declare namespace utf8"));
        assert!(!LUA53.contains("declare namespace bit32")); // Removed in 5.3
    }

    #[test]
    fn test_lua54_embedded() {
        assert!(!LUA54.is_empty());
        assert!(LUA54.contains("declare function warn"));
        assert!(LUA54.contains("declare namespace coroutine"));
        assert!(LUA54.contains("export function close")); // coroutine.close
    }

    #[test]
    fn test_get_stdlib() {
        assert_eq!(get_stdlib(LuaVersion::Lua51), LUA51);
        assert_eq!(get_stdlib(LuaVersion::Lua52), LUA52);
        assert_eq!(get_stdlib(LuaVersion::Lua53), LUA53);
        assert_eq!(get_stdlib(LuaVersion::Lua54), LUA54);
    }

    #[test]
    fn test_get_all_stdlib() {
        let stdlib = get_all_stdlib(LuaVersion::Lua54);
        assert_eq!(stdlib.len(), 3);
        assert_eq!(stdlib[0].0, "builtins.d.tl");
        assert_eq!(stdlib[1].0, "lua54.d.tl");
        assert_eq!(stdlib[2].0, "reflection.d.tl");
    }
}
