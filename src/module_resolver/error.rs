use std::fmt;
use std::path::PathBuf;

/// Errors that can occur during module resolution
#[derive(Debug, Clone)]
pub enum ModuleError {
    /// Module not found despite searching multiple paths
    NotFound {
        source: String,
        searched_paths: Vec<PathBuf>,
    },

    /// Circular dependency detected
    CircularDependency { cycle: Vec<ModuleId> },

    /// Invalid module path
    InvalidPath { source: String, reason: String },

    /// I/O error during module resolution
    IoError { path: PathBuf, message: String },

    /// Module not yet compiled (dependency ordering issue)
    NotCompiled { id: ModuleId },

    /// Export not found in module
    ExportNotFound {
        module_id: ModuleId,
        export_name: String,
    },

    /// Type-check in progress (circular lazy resolution)
    TypeCheckInProgress {
        module: ModuleId,
        depth: usize,
        max_depth: usize,
    },

    /// Export type mismatch between import and export
    ExportTypeMismatch {
        module_id: ModuleId,
        export_name: String,
        expected_type: String,
        actual_type: String,
    },

    /// Runtime import of type-only export
    RuntimeImportOfTypeOnly {
        module_id: ModuleId,
        export_name: String,
    },

    /// Circular re-export chain detected
    CircularReExport {
        chain: Vec<ModuleId>,
        symbol_name: String,
    },

    /// Re-export chain too deep (performance protection)
    ReExportChainTooDeep {
        symbol_name: String,
        depth: usize,
        max_depth: usize,
    },

    /// Type-only export re-exported as value export
    TypeOnlyReExportAsValue {
        module_id: ModuleId,
        symbol_name: String,
    },

    /// Path alias matched but no file found at any resolved path
    AliasNotResolved {
        source: String,
        alias_candidates: Vec<PathBuf>,
        searched_paths: Vec<PathBuf>,
    },
}

impl fmt::Display for ModuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModuleError::NotFound {
                source,
                searched_paths,
            } => {
                writeln!(f, "Cannot find module '{}'", source)?;
                writeln!(f, "Searched paths:")?;
                for path in searched_paths {
                    writeln!(f, "  - {}", path.display())?;
                }
                Ok(())
            }
            ModuleError::CircularDependency { cycle } => {
                writeln!(f, "Circular runtime dependency detected:")?;
                writeln!(f)?;
                for (i, id) in cycle.iter().enumerate() {
                    if i == cycle.len() - 1 {
                        writeln!(f, "  {} -> {} (completes cycle)", id, cycle[0])?;
                    } else {
                        writeln!(f, "  {} ->", id)?;
                    }
                }
                writeln!(f)?;
                writeln!(f, "Suggestion:")?;
                writeln!(
                    f,
                    "  If these modules only reference each other's types (not runtime values),"
                )?;
                writeln!(f, "  use 'import type {{ ... }}' instead of 'import {{ ... }}' to break the cycle.")?;
                writeln!(f)?;
                writeln!(f, "Example:")?;
                writeln!(f, "  // Before: import {{ Foo }} from './other'")?;
                write!(f, "  // After:  import type {{ Foo }} from './other'")
            }
            ModuleError::InvalidPath { source, reason } => {
                write!(f, "Invalid module path '{}': {}", source, reason)
            }
            ModuleError::IoError { path, message } => {
                write!(f, "I/O error reading '{}': {}", path.display(), message)
            }
            ModuleError::NotCompiled { id } => {
                write!(f, "Module '{}' has not been compiled yet", id)
            }
            ModuleError::ExportNotFound {
                module_id,
                export_name,
            } => {
                write!(
                    f,
                    "Module '{}' does not export '{}'",
                    module_id, export_name
                )
            }
            ModuleError::TypeCheckInProgress {
                module,
                depth,
                max_depth,
            } => {
                writeln!(
                    f,
                    "Circular dependency detected during lazy type resolution"
                )?;
                writeln!(f, "  Module: {}", module)?;
                writeln!(f, "  Current recursion depth: {}/{}", depth, max_depth)?;
                write!(f, "  Likely cause: Circular imports with type dependencies")
            }
            ModuleError::ExportTypeMismatch {
                module_id,
                export_name,
                expected_type,
                actual_type,
            } => {
                writeln!(
                    f,
                    "Type mismatch for export '{}' in module '{}'",
                    export_name, module_id
                )?;
                writeln!(f, "  Expected: {}", expected_type)?;
                write!(f, "  Found:    {}", actual_type)
            }
            ModuleError::RuntimeImportOfTypeOnly {
                module_id,
                export_name,
            } => {
                writeln!(
                    f,
                    "Cannot import type-only export '{}' from '{}' as a runtime value",
                    export_name, module_id
                )?;
                write!(f, "  Use 'import type {{ {} }}' instead", export_name)
            }
            ModuleError::CircularReExport { chain, symbol_name } => {
                writeln!(
                    f,
                    "Circular re-export chain detected for symbol '{}':",
                    symbol_name
                )?;
                writeln!(f)?;
                for (i, id) in chain.iter().enumerate() {
                    if i == chain.len() - 1 {
                        writeln!(f, "  {} -> {} (completes cycle)", id, chain[0])?;
                    } else {
                        writeln!(f, "  {} ->", id)?;
                    }
                }
                writeln!(f)?;
                write!(
                    f,
                    "Break this cycle by removing the re-export from one of these modules"
                )
            }
            ModuleError::ReExportChainTooDeep {
                symbol_name,
                depth,
                max_depth,
            } => {
                writeln!(f, "Re-export chain too deep for symbol '{}'", symbol_name)?;
                writeln!(f, "  Current depth: {}/{}", depth, max_depth)?;
                write!(
                    f,
                    "  Simplify the re-export chain or inline the definitions"
                )
            }
            ModuleError::TypeOnlyReExportAsValue {
                module_id,
                symbol_name,
            } => {
                writeln!(
                    f,
                    "Cannot re-export type-only symbol '{}' from '{}' as a runtime export",
                    symbol_name, module_id
                )?;
                write!(
                    f,
                    "  Use 'export type {{ {} }}' if this is a type-only re-export",
                    symbol_name
                )
            }
            ModuleError::AliasNotResolved {
                source,
                alias_candidates,
                searched_paths,
            } => {
                writeln!(f, "Cannot resolve path alias '{}'", source)?;
                if !alias_candidates.is_empty() {
                    writeln!(f, "  Alias expanded to:")?;
                    for candidate in alias_candidates {
                        writeln!(f, "    - {}", candidate.display())?;
                    }
                }
                if !searched_paths.is_empty() {
                    writeln!(f, "  Searched paths:")?;
                    for path in searched_paths {
                        writeln!(f, "    - {}", path.display())?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for ModuleError {}

/// Unique identifier for a module (canonicalized absolute path)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleId(PathBuf);

impl ModuleId {
    pub fn new(path: PathBuf) -> Self {
        Self(path)
    }

    pub fn path(&self) -> &PathBuf {
        &self.0
    }

    pub fn as_str(&self) -> &str {
        self.0.to_str().unwrap_or("<invalid utf-8>")
    }
}

impl fmt::Display for ModuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}

impl From<PathBuf> for ModuleId {
    fn from(path: PathBuf) -> Self {
        Self(path)
    }
}

/// Type of module based on file extension
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleKind {
    /// .tl file (TypedLua source)
    Typed,
    /// .d.tl file (Type declaration only)
    Declaration,
    /// .lua file (Plain Lua, policy-dependent)
    PlainLua,
}

impl ModuleKind {
    pub fn from_extension(ext: &str) -> Option<Self> {
        match ext {
            "tl" => Some(Self::Typed),
            "lua" => Some(Self::PlainLua),
            _ => {
                // Check for .d.tl
                if ext.ends_with(".d.tl") {
                    Some(Self::Declaration)
                } else {
                    None
                }
            }
        }
    }

    pub fn extension(&self) -> &'static str {
        match self {
            Self::Typed => "tl",
            Self::Declaration => "d.tl",
            Self::PlainLua => "lua",
        }
    }
}
