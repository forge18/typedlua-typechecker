use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// A compiled path alias pattern (one entry from the `paths` config)
#[derive(Debug, Clone)]
struct PathAliasPattern {
    /// The prefix before the wildcard (e.g., `@/` for `@/*`, or full string for exact match)
    prefix: String,
    /// Whether this pattern has a wildcard (`*`)
    has_wildcard: bool,
    /// The replacement paths with their own prefix/wildcard info
    replacements: Vec<PathAliasReplacement>,
}

/// A single replacement target for a path alias pattern
#[derive(Debug, Clone)]
struct PathAliasReplacement {
    /// The prefix before the wildcard (e.g., `src/` for `src/*`)
    prefix: String,
    /// The suffix after the wildcard (usually empty)
    suffix: String,
    /// Whether this replacement has a wildcard
    has_wildcard: bool,
}

/// Resolves path aliases from configuration.
///
/// Matches TypeScript's `paths` semantics:
/// - Single `*` wildcard per pattern
/// - Longest prefix matching for specificity
/// - Multiple fallback paths (array values tried in order)
/// - Catch-all `*` pattern supported
#[derive(Debug, Clone)]
pub struct PathAliasResolver {
    /// Compiled alias patterns, sorted by specificity (longest prefix first)
    patterns: Vec<PathAliasPattern>,
    /// Base directory for alias resolution
    base_dir: PathBuf,
}

impl PathAliasResolver {
    /// Create a new PathAliasResolver from config.
    ///
    /// - `paths`: the `paths` config mapping (pattern → replacement paths)
    /// - `base_url`: optional base URL for resolution (relative to `project_root`)
    /// - `project_root`: the project root directory
    pub fn new(
        paths: &HashMap<String, Vec<String>>,
        base_url: Option<&str>,
        project_root: &Path,
    ) -> Self {
        let base_dir = match base_url {
            Some(url) => {
                let p = PathBuf::from(url);
                if p.is_absolute() {
                    p
                } else {
                    project_root.join(p)
                }
            }
            None => project_root.to_path_buf(),
        };

        let mut patterns: Vec<PathAliasPattern> = paths
            .iter()
            .map(|(pattern, replacements)| {
                let (prefix, has_wildcard) = if let Some(idx) = pattern.find('*') {
                    (pattern[..idx].to_string(), true)
                } else {
                    (pattern.clone(), false)
                };

                let replacements = replacements
                    .iter()
                    .map(|r| {
                        if let Some(idx) = r.find('*') {
                            PathAliasReplacement {
                                prefix: r[..idx].to_string(),
                                suffix: r[idx + 1..].to_string(),
                                has_wildcard: true,
                            }
                        } else {
                            PathAliasReplacement {
                                prefix: r.clone(),
                                suffix: String::new(),
                                has_wildcard: false,
                            }
                        }
                    })
                    .collect();

                PathAliasPattern {
                    prefix,
                    has_wildcard,
                    replacements,
                }
            })
            .collect();

        // Sort by longest prefix first (most specific match wins)
        patterns.sort_by(|a, b| b.prefix.len().cmp(&a.prefix.len()));

        Self { patterns, base_dir }
    }

    /// Create an empty resolver with no aliases configured.
    pub fn empty() -> Self {
        Self {
            patterns: Vec::new(),
            base_dir: PathBuf::new(),
        }
    }

    /// Returns true if any aliases are configured.
    pub fn has_aliases(&self) -> bool {
        !self.patterns.is_empty()
    }

    /// Try to resolve a module source string using path aliases.
    ///
    /// Returns `None` if no alias matches.
    /// Returns `Some(candidates)` with filesystem paths to try (in fallback order).
    pub fn resolve_alias(&self, source: &str) -> Option<Vec<PathBuf>> {
        for pattern in &self.patterns {
            if pattern.has_wildcard {
                // Wildcard pattern: check if source starts with the prefix
                if source.starts_with(&pattern.prefix) {
                    let captured = &source[pattern.prefix.len()..];
                    let candidates: Vec<PathBuf> = pattern
                        .replacements
                        .iter()
                        .map(|r| {
                            if r.has_wildcard {
                                let resolved =
                                    format!("{}{}{}", r.prefix, captured, r.suffix);
                                self.base_dir.join(resolved)
                            } else {
                                self.base_dir.join(&r.prefix)
                            }
                        })
                        .collect();
                    return Some(candidates);
                }
            } else {
                // Exact match: source must equal the pattern exactly
                if source == pattern.prefix {
                    let candidates: Vec<PathBuf> = pattern
                        .replacements
                        .iter()
                        .map(|r| self.base_dir.join(&r.prefix))
                        .collect();
                    return Some(candidates);
                }
            }
        }
        None
    }

    /// Check if a source string matches any configured alias pattern.
    pub fn matches_alias(&self, source: &str) -> bool {
        for pattern in &self.patterns {
            if pattern.has_wildcard {
                if source.starts_with(&pattern.prefix) {
                    return true;
                }
            } else if source == pattern.prefix {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_paths(entries: &[(&str, &[&str])]) -> HashMap<String, Vec<String>> {
        entries
            .iter()
            .map(|(k, v)| (k.to_string(), v.iter().map(|s| s.to_string()).collect()))
            .collect()
    }

    #[test]
    fn test_wildcard_basic() {
        let paths = make_paths(&[("@/*", &["src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("@/components/Button").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/src/components/Button")]);
    }

    #[test]
    fn test_wildcard_nested_path() {
        let paths = make_paths(&[("@/*", &["src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("@/deeply/nested/module").unwrap();
        assert_eq!(
            result,
            vec![PathBuf::from("/project/src/deeply/nested/module")]
        );
    }

    #[test]
    fn test_wildcard_single_segment() {
        let paths = make_paths(&[("@/*", &["src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("@/utils").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/src/utils")]);
    }

    #[test]
    fn test_exact_match() {
        let paths = make_paths(&[("@utils", &["src/shared/utils"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("@utils").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/src/shared/utils")]);
    }

    #[test]
    fn test_exact_match_no_partial() {
        let paths = make_paths(&[("@utils", &["src/shared/utils"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        // Should NOT match — exact patterns don't match partial strings
        assert!(resolver.resolve_alias("@utils/foo").is_none());
    }

    #[test]
    fn test_specificity_longest_prefix_wins() {
        let paths = make_paths(&[
            ("@/*", &["src/*"]),
            ("@components/*", &["src/components/*"]),
        ]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        // @components/* should win over @/* for this import
        let result = resolver.resolve_alias("@components/Button").unwrap();
        assert_eq!(
            result,
            vec![PathBuf::from("/project/src/components/Button")]
        );
    }

    #[test]
    fn test_specificity_fallback_to_shorter() {
        let paths = make_paths(&[
            ("@/*", &["src/*"]),
            ("@components/*", &["src/components/*"]),
        ]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        // @/utils doesn't match @components/*, falls through to @/*
        let result = resolver.resolve_alias("@/utils").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/src/utils")]);
    }

    #[test]
    fn test_exact_match_wins_over_wildcard() {
        let paths = make_paths(&[
            ("@utils/*", &["src/utils/*"]),
            ("@utils", &["src/shared/all-utils"]),
        ]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        // Exact match for "@utils" (prefix len same, but exact wins because it's checked)
        // Both have prefix "@utils" (len 6), exact is sorted alongside wildcard
        let result = resolver.resolve_alias("@utils").unwrap();
        assert_eq!(
            result,
            vec![PathBuf::from("/project/src/shared/all-utils")]
        );
    }

    #[test]
    fn test_multiple_fallback_paths() {
        let paths = make_paths(&[("*", &["./vendor/*", "./types/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("lodash").unwrap();
        assert_eq!(
            result,
            vec![
                PathBuf::from("/project/./vendor/lodash"),
                PathBuf::from("/project/./types/lodash"),
            ]
        );
    }

    #[test]
    fn test_catch_all_wildcard() {
        let paths = make_paths(&[("*", &["./src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("anything").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/./src/anything")]);

        let result2 = resolver.resolve_alias("nested/path").unwrap();
        assert_eq!(result2, vec![PathBuf::from("/project/./src/nested/path")]);
    }

    #[test]
    fn test_no_match_returns_none() {
        let paths = make_paths(&[("@/*", &["src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        assert!(resolver.resolve_alias("./relative").is_none());
        assert!(resolver.resolve_alias("some.package").is_none());
    }

    #[test]
    fn test_empty_resolver() {
        let resolver = PathAliasResolver::empty();
        assert!(!resolver.has_aliases());
        assert!(resolver.resolve_alias("@/anything").is_none());
    }

    #[test]
    fn test_has_aliases() {
        let paths = make_paths(&[("@/*", &["src/*"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));
        assert!(resolver.has_aliases());
    }

    #[test]
    fn test_matches_alias() {
        let paths = make_paths(&[
            ("@/*", &["src/*"]),
            ("@utils", &["src/shared/utils"]),
        ]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        assert!(resolver.matches_alias("@/foo"));
        assert!(resolver.matches_alias("@utils"));
        assert!(!resolver.matches_alias("./relative"));
        assert!(!resolver.matches_alias("some.package"));
    }

    #[test]
    fn test_base_url_relative() {
        let paths = make_paths(&[("@/*", &["*"])]);
        let resolver = PathAliasResolver::new(&paths, Some("src"), Path::new("/project"));

        let result = resolver.resolve_alias("@/components/Button").unwrap();
        assert_eq!(
            result,
            vec![PathBuf::from("/project/src/components/Button")]
        );
    }

    #[test]
    fn test_base_url_absolute() {
        let paths = make_paths(&[("@/*", &["*"])]);
        let resolver =
            PathAliasResolver::new(&paths, Some("/absolute/path"), Path::new("/project"));

        let result = resolver.resolve_alias("@/foo").unwrap();
        assert_eq!(result, vec![PathBuf::from("/absolute/path/foo")]);
    }

    #[test]
    fn test_replacement_without_wildcard() {
        // Pattern has wildcard but replacement doesn't — always maps to same path
        let paths = make_paths(&[("@config/*", &["src/config/index"])]);
        let resolver = PathAliasResolver::new(&paths, None, Path::new("/project"));

        let result = resolver.resolve_alias("@config/anything").unwrap();
        assert_eq!(result, vec![PathBuf::from("/project/src/config/index")]);
    }
}
