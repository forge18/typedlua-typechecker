use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum LuaVersion {
    #[serde(rename = "5.1")]
    Lua51,
    #[serde(rename = "5.2")]
    Lua52,
    #[serde(rename = "5.3")]
    Lua53,
    #[serde(rename = "5.4")]
    Lua54,
    #[serde(rename = "auto")]
    #[default]
    Auto,
}

impl LuaVersion {
    /// Detect Lua version from system (runs `lua -v`)
    pub fn detect() -> Self {
        use std::process::Command;

        // Try to run `lua -v`
        if let Ok(output) = Command::new("lua").arg("-v").output() {
            if output.status.success() {
                let version_output = String::from_utf8_lossy(&output.stdout);

                // Parse version from output like "Lua 5.4.6  Copyright (C) 1994-2023 Lua.org, PUC-Rio"
                if version_output.contains("5.1") {
                    return LuaVersion::Lua51;
                } else if version_output.contains("5.2") {
                    return LuaVersion::Lua52;
                } else if version_output.contains("5.3") {
                    return LuaVersion::Lua53;
                } else if version_output.contains("5.4") {
                    return LuaVersion::Lua54;
                }
            }
        }

        // Fallback to 5.4 if detection fails
        LuaVersion::Lua54
    }

    /// Resolve Auto to a concrete Lua version
    pub fn effective(self) -> Self {
        match self {
            LuaVersion::Auto => Self::detect(),
            other => other,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum StrictLevel {
    #[serde(rename = "off")]
    Off,
    #[serde(rename = "warning")]
    Warning,
    #[serde(rename = "error")]
    #[default]
    Error,
}

/// Module code generation mode
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum ModuleMode {
    /// Generate separate files with require() calls (default)
    #[default]
    Require,
    /// Bundle all modules into a single file
    Bundle,
}

/// Optimization level for code generation
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OptimizationLevel {
    /// No optimizations - fastest compilation (O0)
    None,
    /// Basic optimizations - safe transformations (O1: constant folding, DCE, etc.)
    Minimal,
    /// Standard optimizations (O2: includes function inlining, loop opts, string concat)
    Moderate,
    /// Aggressive optimizations (O3: whole-program analysis, devirtualization, generic specialization)
    Aggressive,
    /// Auto-detect based on build profile (default)
    /// Minimal for debug builds, Moderate for release builds
    #[default]
    Auto,
}

/// Output format for generated Lua code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OutputFormat {
    /// Human-readable format with proper indentation and newlines (default)
    #[default]
    Readable,
    /// Compact format with minimal whitespace (single space between tokens)
    Compact,
    /// Minified format with no unnecessary whitespace
    Minified,
}

impl OptimizationLevel {
    /// Resolve Auto to an actual optimization level based on build profile
    #[cfg(debug_assertions)]
    pub fn effective(self) -> Self {
        match self {
            OptimizationLevel::Auto => OptimizationLevel::Minimal,
            other => other,
        }
    }

    #[cfg(not(debug_assertions))]
    pub fn effective(self) -> Self {
        match self {
            OptimizationLevel::Auto => OptimizationLevel::Moderate,
            other => other,
        }
    }
}

/// Compiler options that control type checking and code generation
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompilerOptions {
    /// Enable strict null checking (default: true)
    #[serde(default = "default_true")]
    pub strict_null_checks: bool,

    /// Naming convention enforcement (default: error)
    #[serde(default)]
    pub strict_naming: StrictLevel,

    /// Disallow implicit unknown types (default: false)
    #[serde(default)]
    pub no_implicit_unknown: bool,

    /// Disallow explicit unknown types (default: false)
    #[serde(default)]
    pub no_explicit_unknown: bool,

    /// Target Lua version (default: 5.4)
    #[serde(default)]
    pub target: LuaVersion,

    /// Enable decorator syntax (default: true)
    #[serde(default = "default_true")]
    pub enable_decorators: bool,

    /// Allow importing non-typed Lua files (default: true)
    #[serde(default = "default_true")]
    pub allow_non_typed_lua: bool,

    /// Copy plain .lua files to output directory during compilation (default: false)
    #[serde(default)]
    pub copy_lua_to_output: bool,

    /// Output directory for compiled files
    #[serde(default)]
    pub out_dir: Option<String>,

    /// Output file (bundle all into one file)
    #[serde(default)]
    pub out_file: Option<String>,

    /// Generate source maps (default: false)
    #[serde(default)]
    pub source_map: bool,

    /// Don't emit output files (type check only, default: false)
    #[serde(default)]
    pub no_emit: bool,

    /// Pretty-print diagnostics (default: true)
    #[serde(default = "default_true")]
    pub pretty: bool,

    /// Module code generation mode (default: require)
    #[serde(default)]
    pub module_mode: ModuleMode,

    /// Module search paths for package imports
    #[serde(default = "default_module_paths")]
    pub module_paths: Vec<String>,

    /// Enforce that namespace declarations match file paths (default: false)
    #[serde(default)]
    pub enforce_namespace_path: bool,

    /// Output format for generated Lua code (default: readable)
    #[serde(default)]
    pub output_format: OutputFormat,

    /// Optimization level for code generation (default: minimal)
    #[serde(default)]
    pub optimization_level: OptimizationLevel,
}

fn default_true() -> bool {
    true
}

fn default_module_paths() -> Vec<String> {
    vec![
        "./?.luax".to_string(),
        "./lua_modules/?.luax".to_string(),
        "./lua_modules/?/init.luax".to_string(),
    ]
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            strict_null_checks: true,
            strict_naming: StrictLevel::Error,
            no_implicit_unknown: false,
            no_explicit_unknown: false,
            target: LuaVersion::Lua54,
            enable_decorators: true,
            allow_non_typed_lua: true,
            copy_lua_to_output: false,
            out_dir: None,
            out_file: None,
            source_map: false,
            no_emit: false,
            pretty: true,
            module_mode: ModuleMode::Require,
            module_paths: default_module_paths(),
            enforce_namespace_path: false,
            output_format: OutputFormat::Readable,
            optimization_level: OptimizationLevel::Auto,
        }
    }
}

/// Main compiler configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompilerConfig {
    /// Compiler options
    #[serde(default)]
    pub compiler_options: CompilerOptions,

    /// Files to include (glob patterns)
    #[serde(default)]
    pub include: Vec<String>,

    /// Files to exclude (glob patterns)
    #[serde(default = "default_exclude")]
    pub exclude: Vec<String>,
}

fn default_exclude() -> Vec<String> {
    vec!["**/node_modules/**".to_string(), "**/dist/**".to_string()]
}

impl Default for CompilerConfig {
    fn default() -> Self {
        Self {
            compiler_options: CompilerOptions::default(),
            include: vec!["**/*.luax".to_string()],
            exclude: default_exclude(),
        }
    }
}

impl CompilerConfig {
    /// Load configuration from a YAML file (luanext.config.yaml)
    pub fn from_file(path: &Path) -> Result<Self, crate::cli::errors::CompilationError> {
        let content = std::fs::read_to_string(path)?;
        let config: CompilerConfig = serde_yaml::from_str(&content)
            .map_err(|e| crate::cli::errors::CompilationError::ConfigError(e.to_string()))?;
        Ok(config)
    }

    /// Create a default configuration and write it to luanext.config.yaml
    pub fn init_file(path: &Path) -> Result<(), crate::cli::errors::CompilationError> {
        let config = CompilerConfig::default();
        let yaml = serde_yaml::to_string(&config)
            .map_err(|e| crate::cli::errors::CompilationError::ConfigError(e.to_string()))?;
        std::fs::write(path, yaml)?;
        Ok(())
    }

    /// Merge this configuration with CLI overrides
    /// Only non-None/non-default CLI values override file config
    pub fn merge(&mut self, overrides: &CliOverrides) {
        // Merge compiler options
        if let Some(strict_null_checks) = overrides.strict_null_checks {
            self.compiler_options.strict_null_checks = strict_null_checks;
        }
        if let Some(strict_naming) = overrides.strict_naming {
            self.compiler_options.strict_naming = strict_naming;
        }
        if let Some(no_implicit_unknown) = overrides.no_implicit_unknown {
            self.compiler_options.no_implicit_unknown = no_implicit_unknown;
        }
        if let Some(no_explicit_unknown) = overrides.no_explicit_unknown {
            self.compiler_options.no_explicit_unknown = no_explicit_unknown;
        }
        if let Some(target) = overrides.target {
            self.compiler_options.target = target;
        }
        if let Some(enable_decorators) = overrides.enable_decorators {
            self.compiler_options.enable_decorators = enable_decorators;
        }
        if let Some(allow_non_typed_lua) = overrides.allow_non_typed_lua {
            self.compiler_options.allow_non_typed_lua = allow_non_typed_lua;
        }
        if let Some(copy_lua_to_output) = overrides.copy_lua_to_output {
            self.compiler_options.copy_lua_to_output = copy_lua_to_output;
        }
        if let Some(ref out_dir) = overrides.out_dir {
            self.compiler_options.out_dir = Some(out_dir.clone());
        }
        if let Some(ref out_file) = overrides.out_file {
            self.compiler_options.out_file = Some(out_file.clone());
        }
        if let Some(source_map) = overrides.source_map {
            self.compiler_options.source_map = source_map;
        }
        if let Some(no_emit) = overrides.no_emit {
            self.compiler_options.no_emit = no_emit;
        }
        if let Some(pretty) = overrides.pretty {
            self.compiler_options.pretty = pretty;
        }
        if let Some(module_mode) = overrides.module_mode {
            self.compiler_options.module_mode = module_mode;
        }
        if let Some(ref module_paths) = overrides.module_paths {
            self.compiler_options.module_paths = module_paths.clone();
        }
        if let Some(enforce_namespace_path) = overrides.enforce_namespace_path {
            self.compiler_options.enforce_namespace_path = enforce_namespace_path;
        }
        if let Some(output_format) = overrides.output_format {
            self.compiler_options.output_format = output_format;
        }
        if let Some(optimization_level) = overrides.optimization_level {
            self.compiler_options.optimization_level = optimization_level;
        }
    }
}

/// CLI overrides for configuration
/// All fields are optional - only specified flags override file config
#[derive(Debug, Default, Clone)]
pub struct CliOverrides {
    pub strict_null_checks: Option<bool>,
    pub strict_naming: Option<StrictLevel>,
    pub no_implicit_unknown: Option<bool>,
    pub no_explicit_unknown: Option<bool>,
    pub target: Option<LuaVersion>,
    pub enable_decorators: Option<bool>,
    pub allow_non_typed_lua: Option<bool>,
    pub copy_lua_to_output: Option<bool>,
    pub out_dir: Option<String>,
    pub out_file: Option<String>,
    pub source_map: Option<bool>,
    pub no_emit: Option<bool>,
    pub pretty: Option<bool>,
    pub module_mode: Option<ModuleMode>,
    pub module_paths: Option<Vec<String>>,
    pub enforce_namespace_path: Option<bool>,
    pub output_format: Option<OutputFormat>,
    pub optimization_level: Option<OptimizationLevel>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = CompilerConfig::default();
        assert!(config.compiler_options.strict_null_checks);
        assert_eq!(config.compiler_options.target, LuaVersion::Lua54);
    }

    #[test]
    fn test_serialize_config() {
        let config = CompilerConfig::default();
        let yaml = serde_yaml::to_string(&config).unwrap();
        assert!(yaml.contains("compilerOptions"));
    }

    #[test]
    fn test_deserialize_config() {
        let yaml = r#"
compilerOptions:
  target: "5.3"
  enableDecorators: false
"#;
        let config: CompilerConfig = serde_yaml::from_str(yaml).unwrap();
        assert_eq!(config.compiler_options.target, LuaVersion::Lua53);
        assert!(!config.compiler_options.enable_decorators);
    }

    #[test]
    fn test_config_merge_overrides_file() {
        let mut config = CompilerConfig::default();
        // Default has Lua54 and strict_null_checks = true
        assert_eq!(config.compiler_options.target, LuaVersion::Lua54);
        assert!(config.compiler_options.strict_null_checks);

        // CLI overrides both
        let overrides = CliOverrides {
            target: Some(LuaVersion::Lua51),
            strict_null_checks: Some(false),
            ..Default::default()
        };

        config.merge(&overrides);

        assert_eq!(config.compiler_options.target, LuaVersion::Lua51);
        assert!(!config.compiler_options.strict_null_checks);
    }

    #[test]
    fn test_config_merge_partial_overrides() {
        let mut config = CompilerConfig::default();
        assert!(config.compiler_options.strict_null_checks);
        assert!(config.compiler_options.enable_decorators);

        // Only override one field
        let overrides = CliOverrides {
            enable_decorators: Some(false),
            ..Default::default()
        };

        config.merge(&overrides);

        // This field was overridden
        assert!(!config.compiler_options.enable_decorators);
        // This field remains from file/default
        assert!(config.compiler_options.strict_null_checks);
    }

    #[test]
    fn test_config_merge_empty_overrides() {
        let mut config = CompilerConfig::default();
        let original_target = config.compiler_options.target;
        let original_decorators = config.compiler_options.enable_decorators;

        // Empty overrides shouldn't change anything
        let overrides = CliOverrides::default();
        config.merge(&overrides);

        assert_eq!(config.compiler_options.target, original_target);
        assert_eq!(
            config.compiler_options.enable_decorators,
            original_decorators
        );
    }

    #[test]
    fn test_config_merge_output_options() {
        let mut config = CompilerConfig::default();
        assert!(config.compiler_options.out_dir.is_none());
        assert!(config.compiler_options.out_file.is_none());

        let overrides = CliOverrides {
            out_dir: Some("dist".to_string()),
            source_map: Some(true),
            ..Default::default()
        };

        config.merge(&overrides);

        assert_eq!(config.compiler_options.out_dir, Some("dist".to_string()));
        assert!(config.compiler_options.source_map);
        assert!(config.compiler_options.out_file.is_none()); // Not overridden
    }
}
