pub mod dependency_graph;
pub mod error;
pub mod registry;

pub use dependency_graph::DependencyGraph;
pub use error::{ModuleError, ModuleId, ModuleKind};
pub use registry::{CompiledModule, ExportedSymbol, ModuleExports, ModuleRegistry, ModuleStatus};

use super::config::CompilerOptions;
use super::fs::FileSystem;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Normalize a path by removing . and .. components
fn normalize_path(path: &Path) -> PathBuf {
    let mut components = Vec::new();

    for component in path.components() {
        match component {
            std::path::Component::Prefix(_) | std::path::Component::RootDir => {
                components.push(component);
            }
            std::path::Component::CurDir => {
                // Skip . components
            }
            std::path::Component::ParentDir => {
                // Pop the last component for ..
                if let Some(last) = components.last() {
                    if !matches!(last, std::path::Component::ParentDir) {
                        components.pop();
                    } else {
                        components.push(component);
                    }
                }
            }
            std::path::Component::Normal(_) => {
                components.push(component);
            }
        }
    }

    components.iter().collect()
}

/// Configuration for module resolution
#[derive(Debug, Clone)]
pub struct ModuleConfig {
    /// Search paths for package-style imports
    pub module_paths: Vec<PathBuf>,
    /// Policy for handling plain .lua files
    pub lua_file_policy: LuaFilePolicy,
}

impl ModuleConfig {
    pub fn from_compiler_options(options: &CompilerOptions, base_dir: &Path) -> Self {
        Self {
            module_paths: vec![base_dir.to_path_buf(), base_dir.join("lua_modules")],
            lua_file_policy: if options.allow_non_typed_lua {
                LuaFilePolicy::RequireDeclaration
            } else {
                LuaFilePolicy::Block
            },
        }
    }
}

/// Policy for handling plain .lua file imports
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LuaFilePolicy {
    /// Require .d.tl declaration file
    RequireDeclaration,
    /// Block .lua imports entirely
    Block,
}

/// Module resolver - handles module path resolution
pub struct ModuleResolver {
    fs: Arc<dyn FileSystem>,
    config: ModuleConfig,
    base_dir: PathBuf,
}

impl std::fmt::Debug for ModuleResolver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleResolver")
            .field("config", &self.config)
            .field("base_dir", &self.base_dir)
            .finish_non_exhaustive()
    }
}

impl ModuleResolver {
    pub fn new(fs: Arc<dyn FileSystem>, config: ModuleConfig, base_dir: PathBuf) -> Self {
        Self {
            fs,
            config,
            base_dir,
        }
    }

    /// Resolve an import source to a module ID
    ///
    /// Supports two resolution strategies:
    /// 1. Relative paths: './file', '../dir/file'
    /// 2. Package paths: 'foo.bar' (Lua-style)
    pub fn resolve(&self, source: &str, from_file: &Path) -> Result<ModuleId, ModuleError> {
        // Determine resolution strategy based on source format
        if source.starts_with("./") || source.starts_with("../") {
            self.resolve_relative(source, from_file)
        } else {
            self.resolve_package(source)
        }
    }

    /// Resolve a relative import (Node-style)
    fn resolve_relative(&self, source: &str, from: &Path) -> Result<ModuleId, ModuleError> {
        let from_dir = from.parent().ok_or_else(|| ModuleError::InvalidPath {
            source: source.to_string(),
            reason: format!("Cannot get parent directory of '{}'", from.display()),
        })?;

        let target = from_dir.join(source);
        let mut searched_paths = Vec::new();

        // Try direct file with extensions
        for ext in &["tl", "d.tl"] {
            let path = target.with_extension(ext);
            searched_paths.push(path.clone());
            if self.fs.exists(&path) {
                return self.canonicalize(&path);
            }
        }

        // Try .lua file if policy allows
        if matches!(
            self.config.lua_file_policy,
            LuaFilePolicy::RequireDeclaration
        ) {
            // Check for .d.tl declaration file first
            let decl_path = target.with_extension("d.tl");
            if self.fs.exists(&decl_path) {
                return self.canonicalize(&decl_path);
            }

            // Try .lua file (will require .d.tl at type-check time)
            let lua_path = target.with_extension("lua");
            searched_paths.push(lua_path.clone());
            if self.fs.exists(&lua_path) {
                return self.canonicalize(&lua_path);
            }
        }

        // Try as directory with index.tl
        let index_path = target.join("index.tl");
        searched_paths.push(index_path.clone());
        if self.fs.exists(&index_path) {
            return self.canonicalize(&index_path);
        }

        Err(ModuleError::NotFound {
            source: source.to_string(),
            searched_paths,
        })
    }

    /// Resolve a package import (Lua-style)
    fn resolve_package(&self, source: &str) -> Result<ModuleId, ModuleError> {
        // Convert "foo.bar" → "foo/bar"
        let path = source.replace('.', "/");
        let mut searched_paths = Vec::new();

        // Search in configured module_paths
        for search_path in &self.config.module_paths {
            let candidate = search_path.join(&path);

            // Try with extensions
            if let Ok(resolved) = self.try_extensions(&candidate, &mut searched_paths) {
                return Ok(resolved);
            }

            // Try as directory with index.tl
            let index_path = candidate.join("index.tl");
            searched_paths.push(index_path.clone());
            if self.fs.exists(&index_path) {
                return self.canonicalize(&index_path);
            }
        }

        Err(ModuleError::NotFound {
            source: source.to_string(),
            searched_paths,
        })
    }

    /// Try multiple file extensions for a path
    fn try_extensions(
        &self,
        base: &Path,
        searched_paths: &mut Vec<PathBuf>,
    ) -> Result<ModuleId, ModuleError> {
        // Try .tl first
        let tl_path = base.with_extension("tl");
        searched_paths.push(tl_path.clone());
        if self.fs.exists(&tl_path) {
            return self.canonicalize(&tl_path);
        }

        // Try .d.tl
        let dtl_path = PathBuf::from(format!("{}.d.tl", base.display()));
        searched_paths.push(dtl_path.clone());
        if self.fs.exists(&dtl_path) {
            return self.canonicalize(&dtl_path);
        }

        // Try .lua if policy allows
        if matches!(
            self.config.lua_file_policy,
            LuaFilePolicy::RequireDeclaration
        ) {
            let lua_path = base.with_extension("lua");
            searched_paths.push(lua_path.clone());
            if self.fs.exists(&lua_path) {
                return self.canonicalize(&lua_path);
            }
        }

        Err(ModuleError::NotFound {
            source: base.display().to_string(),
            searched_paths: Vec::new(),
        })
    }

    /// Canonicalize a path to create a ModuleId
    fn canonicalize(&self, path: &Path) -> Result<ModuleId, ModuleError> {
        // For real file system, use canonicalize
        // For mock file system, just use the path as-is
        match path.canonicalize() {
            Ok(canonical) => Ok(ModuleId::new(canonical)),
            Err(_) => {
                // Fallback for mock file system - use absolute path with normalization
                let absolute = if path.is_absolute() {
                    path.to_path_buf()
                } else {
                    self.base_dir.join(path)
                };
                // Normalize the path by removing . and .. components
                let normalized = normalize_path(&absolute);
                Ok(ModuleId::new(normalized))
            }
        }
    }

    /// Get the module kind from a path
    pub fn get_module_kind(&self, path: &Path) -> Option<ModuleKind> {
        let path_str = path.to_str()?;
        if path_str.ends_with(".d.tl") {
            Some(ModuleKind::Declaration)
        } else {
            path.extension()
                .and_then(|ext| ext.to_str())
                .and_then(ModuleKind::from_extension)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fs::MockFileSystem;

    fn make_test_fs() -> Arc<MockFileSystem> {
        let mut fs = MockFileSystem::new();
        fs.add_file("/project/src/main.tl", "-- main");
        fs.add_file("/project/src/utils.tl", "-- utils");
        fs.add_file("/project/src/types.d.tl", "-- types");
        fs.add_file("/project/src/lib/index.tl", "-- lib");
        fs.add_file("/project/lua_modules/foo/bar.tl", "-- foo.bar");
        Arc::new(fs)
    }

    fn make_resolver(fs: Arc<dyn FileSystem>) -> ModuleResolver {
        let config = ModuleConfig {
            module_paths: vec![
                PathBuf::from("/project"),
                PathBuf::from("/project/lua_modules"),
            ],
            lua_file_policy: LuaFilePolicy::RequireDeclaration,
        };
        ModuleResolver::new(fs, config, PathBuf::from("/project"))
    }

    #[test]
    fn test_resolve_relative_simple() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let result = resolver.resolve("./utils", Path::new("/project/src/main.tl"));
        assert!(result.is_ok());
        let id = result.unwrap();
        assert!(id.as_str().contains("utils.tl"));
    }

    #[test]
    fn test_resolve_relative_declaration() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let result = resolver.resolve("./types", Path::new("/project/src/main.tl"));
        assert!(result.is_ok());
        let id = result.unwrap();
        assert!(id.as_str().contains("types.d.tl"));
    }

    #[test]
    fn test_resolve_relative_index() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let result = resolver.resolve("./lib", Path::new("/project/src/main.tl"));
        assert!(result.is_ok());
        let id = result.unwrap();
        assert!(id.as_str().contains("lib"));
        assert!(id.as_str().contains("index.tl"));
    }

    #[test]
    fn test_resolve_package_style() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let result = resolver.resolve("foo.bar", Path::new("/project/src/main.tl"));
        assert!(result.is_ok());
        let id = result.unwrap();
        assert!(id.as_str().contains("foo"));
        assert!(id.as_str().contains("bar.tl"));
    }

    #[test]
    fn test_resolve_not_found() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let result = resolver.resolve("./nonexistent", Path::new("/project/src/main.tl"));
        assert!(result.is_err());

        if let Err(ModuleError::NotFound {
            source,
            searched_paths,
        }) = result
        {
            assert_eq!(source, "./nonexistent");
            assert!(!searched_paths.is_empty());
        } else {
            panic!("Expected NotFound error");
        }
    }

    #[test]
    fn test_module_kind_detection() {
        let fs = make_test_fs();
        let resolver = make_resolver(fs);

        let tl_kind = resolver.get_module_kind(Path::new("test.tl"));
        assert_eq!(tl_kind, Some(ModuleKind::Typed));

        let dtl_kind = resolver.get_module_kind(Path::new("test.d.tl"));
        assert_eq!(dtl_kind, Some(ModuleKind::Declaration));

        let lua_kind = resolver.get_module_kind(Path::new("test.lua"));
        assert_eq!(lua_kind, Some(ModuleKind::PlainLua));
    }

    #[test]
    fn test_lua_file_policy_block() {
        let mut fs = MockFileSystem::new();
        fs.add_file("/project/src/main.tl", "-- main");
        fs.add_file("/project/src/legacy.lua", "-- legacy");
        let fs = Arc::new(fs);

        let config = ModuleConfig {
            module_paths: vec![PathBuf::from("/project")],
            lua_file_policy: LuaFilePolicy::Block,
        };
        let resolver = ModuleResolver::new(fs, config, PathBuf::from("/project"));

        // Should not find .lua file when policy is Block
        let result = resolver.resolve("./legacy", Path::new("/project/src/main.tl"));
        assert!(result.is_err());
    }
}
