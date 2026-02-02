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
                writeln!(f, "Circular dependency detected:")?;
                for (i, id) in cycle.iter().enumerate() {
                    if i == cycle.len() - 1 {
                        writeln!(f, "  {} -> {} (cycle)", id, cycle[0])?;
                    } else {
                        writeln!(f, "  {} ->", id)?;
                    }
                }
                Ok(())
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
