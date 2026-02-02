use std::sync::Mutex;
use typedlua_parser::span::Span;

// Bridge implementation for parser crate compatibility
// This allows core's diagnostic handlers to be used with the parser crate's Lexer and Parser

/// Diagnostic severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Info,
}

/// Diagnostic code for categorization and documentation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagnosticCode {
    /// Numeric code (e.g., 1001, 2004)
    pub code: u16,
    /// Category prefix (e.g., "E" for error, "W" for warning)
    pub prefix: char,
}

impl DiagnosticCode {
    pub const fn new(prefix: char, code: u16) -> Self {
        Self { code, prefix }
    }

    /// Format as string (e.g., "E1001", "W2004")
    pub fn as_str(&self) -> String {
        format!("{}{:04}", self.prefix, self.code)
    }
}

/// Related information for a diagnostic (additional context from other locations)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticRelatedInformation {
    pub span: Span,
    pub message: String,
}

/// Suggested fix for a diagnostic
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticSuggestion {
    pub span: Span,
    pub replacement: String,
    pub message: String,
}

/// A diagnostic message with location, severity, and optional metadata
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub span: Span,
    pub message: String,
    pub code: Option<DiagnosticCode>,
    pub related_information: Vec<DiagnosticRelatedInformation>,
    pub suggestions: Vec<DiagnosticSuggestion>,
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self {
            level: DiagnosticLevel::Error,
            span,
            message: message.into(),
            code: None,
            related_information: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self {
            level: DiagnosticLevel::Warning,
            span,
            message: message.into(),
            code: None,
            related_information: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    pub fn info(span: Span, message: impl Into<String>) -> Self {
        Self {
            level: DiagnosticLevel::Info,
            span,
            message: message.into(),
            code: None,
            related_information: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    /// Create an error with a diagnostic code
    pub fn error_with_code(span: Span, code: DiagnosticCode, message: impl Into<String>) -> Self {
        Self {
            level: DiagnosticLevel::Error,
            span,
            message: message.into(),
            code: Some(code),
            related_information: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    /// Add related information to this diagnostic
    pub fn with_related(mut self, span: Span, message: impl Into<String>) -> Self {
        self.related_information.push(DiagnosticRelatedInformation {
            span,
            message: message.into(),
        });
        self
    }

    /// Add a suggestion to this diagnostic
    pub fn with_suggestion(
        mut self,
        span: Span,
        replacement: String,
        message: impl Into<String>,
    ) -> Self {
        self.suggestions.push(DiagnosticSuggestion {
            span,
            replacement,
            message: message.into(),
        });
        self
    }

    /// Set the diagnostic code
    pub fn with_code(mut self, code: DiagnosticCode) -> Self {
        self.code = Some(code);
        self
    }
}

/// Trait for handling diagnostics
/// This allows for dependency injection and testing with mock handlers
pub trait DiagnosticHandler: Send + Sync {
    fn report(&self, diagnostic: Diagnostic);

    fn error(&self, span: Span, message: &str) {
        self.report(Diagnostic::error(span, message.to_string()));
    }

    fn warning(&self, span: Span, message: &str) {
        self.report(Diagnostic::warning(span, message.to_string()));
    }

    fn info(&self, span: Span, message: &str) {
        self.report(Diagnostic::info(span, message.to_string()));
    }

    fn has_errors(&self) -> bool;
    fn error_count(&self) -> usize;
    fn warning_count(&self) -> usize;
    fn get_diagnostics(&self) -> Vec<Diagnostic>;
}

/// Console-based diagnostic handler that prints to stderr
pub struct ConsoleDiagnosticHandler {
    diagnostics: Mutex<Vec<Diagnostic>>,
    pretty: bool,
}

impl ConsoleDiagnosticHandler {
    pub fn new(pretty: bool) -> Self {
        Self {
            diagnostics: Mutex::new(Vec::new()),
            pretty,
        }
    }
}

impl DiagnosticHandler for ConsoleDiagnosticHandler {
    fn report(&self, diagnostic: Diagnostic) {
        let level_str = match diagnostic.level {
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
            DiagnosticLevel::Info => "info",
        };

        if self.pretty {
            let code_str = if let Some(code) = &diagnostic.code {
                format!("[{}] ", code.as_str())
            } else {
                String::new()
            };
            eprintln!(
                "\x1b[1m{}\x1b[0m {}at {}: {}",
                level_str, code_str, diagnostic.span, diagnostic.message
            );

            // Print related information
            for related in &diagnostic.related_information {
                eprintln!(
                    "  \x1b[36mNote\x1b[0m at {}: {}",
                    related.span, related.message
                );
            }

            // Print suggestions
            for suggestion in &diagnostic.suggestions {
                eprintln!("  \x1b[32mSuggestion\x1b[0m: {}", suggestion.message);
            }
        } else {
            let code_str = if let Some(code) = &diagnostic.code {
                format!("[{}] ", code.as_str())
            } else {
                String::new()
            };
            eprintln!(
                "{} {}at {}: {}",
                level_str, code_str, diagnostic.span, diagnostic.message
            );

            // Print related information
            for related in &diagnostic.related_information {
                eprintln!("  Note at {}: {}", related.span, related.message);
            }

            // Print suggestions
            for suggestion in &diagnostic.suggestions {
                eprintln!("  Suggestion: {}", suggestion.message);
            }
        }

        self.diagnostics.lock().unwrap().push(diagnostic);
    }

    fn has_errors(&self) -> bool {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    }

    fn error_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Error)
            .count()
    }

    fn warning_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Warning)
            .count()
    }

    fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.lock().unwrap().clone()
    }
}

/// Error codes for TypedLua diagnostics
///
/// Error codes are organized by component:
/// - E1000-E1999: Lexer errors
/// - E2000-E2999: Parser errors
/// - E3000-E3999: Type checker errors
/// - E4000-E4999: Code generator errors
/// - E5000-E5999: Configuration errors
/// - W1000-W9999: Warnings
pub mod error_codes {
    use super::DiagnosticCode;

    // ========================================
    // Lexer Errors (E1000-E1999)
    // ========================================

    /// Unterminated string literal
    pub const UNTERMINATED_STRING: DiagnosticCode = DiagnosticCode::new('E', 1001);

    /// Unterminated multi-line comment
    pub const UNTERMINATED_COMMENT: DiagnosticCode = DiagnosticCode::new('E', 1002);

    /// Invalid number literal format
    pub const INVALID_NUMBER: DiagnosticCode = DiagnosticCode::new('E', 1003);

    /// Unexpected character
    pub const UNEXPECTED_CHAR: DiagnosticCode = DiagnosticCode::new('E', 1004);

    /// Invalid escape sequence in string
    pub const INVALID_ESCAPE: DiagnosticCode = DiagnosticCode::new('E', 1005);

    /// Unterminated template literal
    pub const UNTERMINATED_TEMPLATE: DiagnosticCode = DiagnosticCode::new('E', 1006);

    /// Invalid hexadecimal number
    pub const INVALID_HEX_NUMBER: DiagnosticCode = DiagnosticCode::new('E', 1007);

    /// Invalid binary number
    pub const INVALID_BINARY_NUMBER: DiagnosticCode = DiagnosticCode::new('E', 1008);

    // ========================================
    // Parser Errors (E2000-E2999)
    // ========================================

    /// Expected a specific token but found something else
    pub const EXPECTED_TOKEN: DiagnosticCode = DiagnosticCode::new('E', 2001);

    /// Unexpected token encountered
    pub const UNEXPECTED_TOKEN: DiagnosticCode = DiagnosticCode::new('E', 2002);

    /// Expected an identifier
    pub const EXPECTED_IDENTIFIER: DiagnosticCode = DiagnosticCode::new('E', 2003);

    /// Expected an expression
    pub const EXPECTED_EXPRESSION: DiagnosticCode = DiagnosticCode::new('E', 2004);

    /// Expected a type annotation
    pub const EXPECTED_TYPE: DiagnosticCode = DiagnosticCode::new('E', 2005);

    /// Expected a pattern
    pub const EXPECTED_PATTERN: DiagnosticCode = DiagnosticCode::new('E', 2006);

    /// Missing semicolon or statement terminator
    pub const MISSING_SEMICOLON: DiagnosticCode = DiagnosticCode::new('E', 2007);

    /// Missing 'end' keyword
    pub const MISSING_END: DiagnosticCode = DiagnosticCode::new('E', 2008);

    /// Missing 'then' keyword after if condition
    pub const MISSING_THEN: DiagnosticCode = DiagnosticCode::new('E', 2009);

    /// Missing 'do' keyword
    pub const MISSING_DO: DiagnosticCode = DiagnosticCode::new('E', 2010);

    /// Invalid function parameter
    pub const INVALID_PARAMETER: DiagnosticCode = DiagnosticCode::new('E', 2011);

    /// Invalid destructuring pattern
    pub const INVALID_DESTRUCTURING: DiagnosticCode = DiagnosticCode::new('E', 2012);

    /// Break statement outside of loop
    pub const BREAK_OUTSIDE_LOOP: DiagnosticCode = DiagnosticCode::new('E', 2013);

    /// Continue statement outside of loop
    pub const CONTINUE_OUTSIDE_LOOP: DiagnosticCode = DiagnosticCode::new('E', 2014);

    /// Invalid assignment target
    pub const INVALID_ASSIGNMENT: DiagnosticCode = DiagnosticCode::new('E', 2015);

    /// Expected '>>' but found end of tokens (generic type parsing)
    pub const EXPECTED_DOUBLE_GT: DiagnosticCode = DiagnosticCode::new('E', 2016);

    /// Classes disabled in configuration
    pub const CLASSES_DISABLED: DiagnosticCode = DiagnosticCode::new('E', 2020);

    /// Decorators disabled in configuration
    pub const DECORATORS_DISABLED: DiagnosticCode = DiagnosticCode::new('E', 2021);

    /// Functional programming features disabled
    pub const FP_DISABLED: DiagnosticCode = DiagnosticCode::new('E', 2022);

    // ========================================
    // Type Checker Errors (E3000-E3999)
    // ========================================

    /// Type mismatch between expected and actual types
    pub const TYPE_MISMATCH: DiagnosticCode = DiagnosticCode::new('E', 3001);

    /// Undefined variable or identifier
    pub const UNDEFINED_VARIABLE: DiagnosticCode = DiagnosticCode::new('E', 3002);

    /// Duplicate declaration
    pub const DUPLICATE_DECLARATION: DiagnosticCode = DiagnosticCode::new('E', 3003);

    /// Cannot assign to constant
    pub const ASSIGN_TO_CONST: DiagnosticCode = DiagnosticCode::new('E', 3004);

    /// Type not found
    pub const TYPE_NOT_FOUND: DiagnosticCode = DiagnosticCode::new('E', 3005);

    /// Property not found on type
    pub const PROPERTY_NOT_FOUND: DiagnosticCode = DiagnosticCode::new('E', 3006);

    /// Wrong number of arguments in function call
    pub const WRONG_ARG_COUNT: DiagnosticCode = DiagnosticCode::new('E', 3007);

    /// Cannot call non-function type
    pub const NOT_CALLABLE: DiagnosticCode = DiagnosticCode::new('E', 3008);

    /// Cannot index non-indexable type
    pub const NOT_INDEXABLE: DiagnosticCode = DiagnosticCode::new('E', 3009);

    /// Missing return statement
    pub const MISSING_RETURN: DiagnosticCode = DiagnosticCode::new('E', 3010);

    /// Circular type reference
    pub const CIRCULAR_TYPE: DiagnosticCode = DiagnosticCode::new('E', 3011);

    /// Interface not found
    pub const INTERFACE_NOT_FOUND: DiagnosticCode = DiagnosticCode::new('E', 3012);

    /// Class does not implement interface
    pub const INTERFACE_NOT_IMPLEMENTED: DiagnosticCode = DiagnosticCode::new('E', 3013);

    /// Abstract method has implementation
    pub const ABSTRACT_METHOD_BODY: DiagnosticCode = DiagnosticCode::new('E', 3014);

    /// Non-abstract class has abstract methods
    pub const ABSTRACT_METHODS_IN_CONCRETE_CLASS: DiagnosticCode = DiagnosticCode::new('E', 3015);

    /// Multiple constructors in class
    pub const MULTIPLE_CONSTRUCTORS: DiagnosticCode = DiagnosticCode::new('E', 3016);

    /// Generic type parameter constraint not satisfied
    pub const CONSTRAINT_NOT_SATISFIED: DiagnosticCode = DiagnosticCode::new('E', 3017);

    /// Wrong number of type arguments
    pub const WRONG_TYPE_ARG_COUNT: DiagnosticCode = DiagnosticCode::new('E', 3018);

    /// Cannot infer type
    pub const CANNOT_INFER_TYPE: DiagnosticCode = DiagnosticCode::new('E', 3019);

    /// Pattern match not exhaustive
    pub const NON_EXHAUSTIVE_MATCH: DiagnosticCode = DiagnosticCode::new('E', 3020);

    /// Invalid type in pattern match
    pub const INVALID_MATCH_TYPE: DiagnosticCode = DiagnosticCode::new('E', 3021);

    /// Getter and setter type mismatch
    pub const GETTER_SETTER_MISMATCH: DiagnosticCode = DiagnosticCode::new('E', 3022);

    /// Property marked readonly
    pub const READONLY_PROPERTY: DiagnosticCode = DiagnosticCode::new('E', 3023);

    /// Access to private member
    pub const PRIVATE_ACCESS: DiagnosticCode = DiagnosticCode::new('E', 3024);

    /// Access to protected member
    pub const PROTECTED_ACCESS: DiagnosticCode = DiagnosticCode::new('E', 3025);

    /// Or-pattern alternatives bind different variables
    pub const INCONSISTENT_OR_PATTERN_BINDINGS: DiagnosticCode = DiagnosticCode::new('E', 3026);

    /// Or-pattern alternatives bind variables with incompatible types
    pub const INCOMPATIBLE_OR_PATTERN_TYPES: DiagnosticCode = DiagnosticCode::new('E', 3027);

    /// Or-pattern has no alternatives
    pub const EMPTY_OR_PATTERN: DiagnosticCode = DiagnosticCode::new('E', 3028);

    // ========================================
    // Code Generator Errors (E4000-E4999)
    // ========================================

    /// Unsupported feature for target Lua version
    pub const UNSUPPORTED_FEATURE: DiagnosticCode = DiagnosticCode::new('E', 4001);

    /// Source map generation failed
    pub const SOURCE_MAP_ERROR: DiagnosticCode = DiagnosticCode::new('E', 4002);

    // ========================================
    // Configuration Errors (E5000-E5999)
    // ========================================

    /// Invalid configuration file
    pub const INVALID_CONFIG: DiagnosticCode = DiagnosticCode::new('E', 5001);

    /// Missing configuration file
    pub const MISSING_CONFIG: DiagnosticCode = DiagnosticCode::new('E', 5002);

    /// Invalid Lua target version
    pub const INVALID_TARGET: DiagnosticCode = DiagnosticCode::new('E', 5003);

    // ========================================
    // Warnings (W1000-W9999)
    // ========================================

    /// Unused variable
    pub const UNUSED_VARIABLE: DiagnosticCode = DiagnosticCode::new('W', 1001);

    /// Unused import
    pub const UNUSED_IMPORT: DiagnosticCode = DiagnosticCode::new('W', 1002);

    /// Deprecated feature
    pub const DEPRECATED: DiagnosticCode = DiagnosticCode::new('W', 1003);

    /// Unreachable code
    pub const UNREACHABLE_CODE: DiagnosticCode = DiagnosticCode::new('W', 1004);

    /// Implicit any type
    pub const IMPLICIT_ANY: DiagnosticCode = DiagnosticCode::new('W', 1005);

    /// Possible nil value
    pub const POSSIBLE_NIL: DiagnosticCode = DiagnosticCode::new('W', 1006);

    /// Shadowed variable
    pub const SHADOWED_VARIABLE: DiagnosticCode = DiagnosticCode::new('W', 1007);

    /// Empty block
    pub const EMPTY_BLOCK: DiagnosticCode = DiagnosticCode::new('W', 1008);

    /// Type could be narrower
    pub const TYPE_TOO_WIDE: DiagnosticCode = DiagnosticCode::new('W', 1009);

    /// Pattern is unreachable
    pub const UNREACHABLE_PATTERN: DiagnosticCode = DiagnosticCode::new('W', 1010);
}

/// Collecting diagnostic handler for testing
/// Collects all diagnostics without printing
pub struct CollectingDiagnosticHandler {
    diagnostics: Mutex<Vec<Diagnostic>>,
}

impl CollectingDiagnosticHandler {
    pub fn new() -> Self {
        Self {
            diagnostics: Mutex::new(Vec::new()),
        }
    }
}

impl Default for CollectingDiagnosticHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl DiagnosticHandler for CollectingDiagnosticHandler {
    fn report(&self, diagnostic: Diagnostic) {
        self.diagnostics.lock().unwrap().push(diagnostic);
    }

    fn has_errors(&self) -> bool {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .any(|d| d.level == DiagnosticLevel::Error)
    }

    fn error_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Error)
            .count()
    }

    fn warning_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Warning)
            .count()
    }

    fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.lock().unwrap().clone()
    }
}

// Bridge implementations for parser crate compatibility
// These allow the core's diagnostic handlers to work with typedlua_parser's Lexer and Parser

/// Convert a parser diagnostic to a core diagnostic
fn convert_parser_diagnostic(diag: typedlua_parser::Diagnostic) -> Diagnostic {
    let level = match diag.level {
        typedlua_parser::diagnostics::DiagnosticLevel::Error => DiagnosticLevel::Error,
        typedlua_parser::diagnostics::DiagnosticLevel::Warning => DiagnosticLevel::Warning,
        typedlua_parser::diagnostics::DiagnosticLevel::Info => DiagnosticLevel::Info,
    };

    let code = diag.code.map(|c| DiagnosticCode::new(c.prefix, c.code));

    let related_information = diag
        .related_information
        .into_iter()
        .map(|r| DiagnosticRelatedInformation {
            span: r.span,
            message: r.message,
        })
        .collect();

    let suggestions = diag
        .suggestions
        .into_iter()
        .map(|s| DiagnosticSuggestion {
            span: s.span,
            replacement: s.replacement,
            message: s.message,
        })
        .collect();

    Diagnostic {
        level,
        span: diag.span,
        message: diag.message,
        code,
        related_information,
        suggestions,
    }
}

impl typedlua_parser::DiagnosticHandler for ConsoleDiagnosticHandler {
    fn report(&self, diagnostic: typedlua_parser::Diagnostic) {
        DiagnosticHandler::report(self, convert_parser_diagnostic(diagnostic));
    }

    fn has_errors(&self) -> bool {
        DiagnosticHandler::has_errors(self)
    }

    fn error_count(&self) -> usize {
        DiagnosticHandler::error_count(self)
    }

    fn warning_count(&self) -> usize {
        DiagnosticHandler::warning_count(self)
    }

    fn get_diagnostics(&self) -> Vec<typedlua_parser::Diagnostic> {
        // Convert core diagnostics back to parser diagnostics
        DiagnosticHandler::get_diagnostics(self)
            .into_iter()
            .map(|d| {
                let level = match d.level {
                    DiagnosticLevel::Error => typedlua_parser::diagnostics::DiagnosticLevel::Error,
                    DiagnosticLevel::Warning => {
                        typedlua_parser::diagnostics::DiagnosticLevel::Warning
                    }
                    DiagnosticLevel::Info => typedlua_parser::diagnostics::DiagnosticLevel::Info,
                };
                let code = d
                    .code
                    .map(|c| typedlua_parser::diagnostics::DiagnosticCode::new(c.prefix, c.code));
                typedlua_parser::Diagnostic {
                    level,
                    span: d.span,
                    message: d.message,
                    code,
                    related_information: d
                        .related_information
                        .into_iter()
                        .map(
                            |r| typedlua_parser::diagnostics::DiagnosticRelatedInformation {
                                span: r.span,
                                message: r.message,
                            },
                        )
                        .collect(),
                    suggestions: d
                        .suggestions
                        .into_iter()
                        .map(|s| typedlua_parser::diagnostics::DiagnosticSuggestion {
                            span: s.span,
                            replacement: s.replacement,
                            message: s.message,
                        })
                        .collect(),
                }
            })
            .collect()
    }
}

impl typedlua_parser::DiagnosticHandler for CollectingDiagnosticHandler {
    fn report(&self, diagnostic: typedlua_parser::Diagnostic) {
        DiagnosticHandler::report(self, convert_parser_diagnostic(diagnostic));
    }

    fn has_errors(&self) -> bool {
        DiagnosticHandler::has_errors(self)
    }

    fn error_count(&self) -> usize {
        DiagnosticHandler::error_count(self)
    }

    fn warning_count(&self) -> usize {
        DiagnosticHandler::warning_count(self)
    }

    fn get_diagnostics(&self) -> Vec<typedlua_parser::Diagnostic> {
        DiagnosticHandler::get_diagnostics(self)
            .into_iter()
            .map(|d| {
                let level = match d.level {
                    DiagnosticLevel::Error => typedlua_parser::diagnostics::DiagnosticLevel::Error,
                    DiagnosticLevel::Warning => {
                        typedlua_parser::diagnostics::DiagnosticLevel::Warning
                    }
                    DiagnosticLevel::Info => typedlua_parser::diagnostics::DiagnosticLevel::Info,
                };
                let code = d
                    .code
                    .map(|c| typedlua_parser::diagnostics::DiagnosticCode::new(c.prefix, c.code));
                typedlua_parser::Diagnostic {
                    level,
                    span: d.span,
                    message: d.message,
                    code,
                    related_information: d
                        .related_information
                        .into_iter()
                        .map(
                            |r| typedlua_parser::diagnostics::DiagnosticRelatedInformation {
                                span: r.span,
                                message: r.message,
                            },
                        )
                        .collect(),
                    suggestions: d
                        .suggestions
                        .into_iter()
                        .map(|s| typedlua_parser::diagnostics::DiagnosticSuggestion {
                            span: s.span,
                            replacement: s.replacement,
                            message: s.message,
                        })
                        .collect(),
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_creation() {
        let span = Span::new(0, 5, 1, 1);
        let diag = Diagnostic::error(span, "Test error");

        assert_eq!(diag.level, DiagnosticLevel::Error);
        assert_eq!(diag.message, "Test error");
        assert!(diag.code.is_none());
        assert!(diag.related_information.is_empty());
        assert!(diag.suggestions.is_empty());
    }

    #[test]
    fn test_diagnostic_with_code() {
        let span = Span::new(0, 5, 1, 1);
        let code = DiagnosticCode::new('E', 1001);
        let diag = Diagnostic::error_with_code(span, code, "Syntax error");

        assert_eq!(diag.code, Some(code));
        assert_eq!(code.as_str(), "E1001");
    }

    #[test]
    fn test_diagnostic_with_related_info() {
        let span = Span::new(0, 5, 1, 1);
        let related_span = Span::new(10, 15, 2, 1);

        let diag = Diagnostic::error(span, "Duplicate declaration")
            .with_related(related_span, "Previously declared here");

        assert_eq!(diag.related_information.len(), 1);
        assert_eq!(diag.related_information[0].span, related_span);
        assert_eq!(
            diag.related_information[0].message,
            "Previously declared here"
        );
    }

    #[test]
    fn test_diagnostic_with_suggestion() {
        let span = Span::new(0, 5, 1, 1);

        let diag = Diagnostic::error(span, "Use 'const' instead").with_suggestion(
            span,
            "const".to_string(),
            "Replace with 'const'",
        );

        assert_eq!(diag.suggestions.len(), 1);
        assert_eq!(diag.suggestions[0].replacement, "const");
        assert_eq!(diag.suggestions[0].message, "Replace with 'const'");
    }

    #[test]
    fn test_diagnostic_builder_chain() {
        let span = Span::new(0, 5, 1, 1);
        let related_span = Span::new(10, 15, 2, 1);
        let code = DiagnosticCode::new('E', 2004);

        let diag = Diagnostic::error(span, "Type mismatch")
            .with_code(code)
            .with_related(related_span, "Expected type defined here")
            .with_suggestion(span, "number".to_string(), "Use 'number' type");

        assert_eq!(diag.code, Some(code));
        assert_eq!(diag.related_information.len(), 1);
        assert_eq!(diag.suggestions.len(), 1);
    }

    #[test]
    fn test_collecting_handler() {
        let handler = CollectingDiagnosticHandler::new();
        let span = Span::new(0, 5, 1, 1);

        handler.error(span, "Error 1");
        handler.warning(span, "Warning 1");
        handler.error(span, "Error 2");

        assert_eq!(handler.error_count(), 2);
        assert_eq!(handler.warning_count(), 1);
        assert!(handler.has_errors());
        assert_eq!(handler.get_diagnostics().len(), 3);
    }

    #[test]
    fn test_no_errors() {
        let handler = CollectingDiagnosticHandler::new();
        let span = Span::new(0, 5, 1, 1);

        handler.warning(span, "Warning 1");
        handler.info(span, "Info 1");

        assert!(!handler.has_errors());
        assert_eq!(handler.error_count(), 0);
    }

    #[test]
    fn test_diagnostic_code_formatting() {
        let code1 = DiagnosticCode::new('E', 1);
        assert_eq!(code1.as_str(), "E0001");

        let code2 = DiagnosticCode::new('W', 1234);
        assert_eq!(code2.as_str(), "W1234");

        let code3 = DiagnosticCode::new('I', 999);
        assert_eq!(code3.as_str(), "I0999");
    }

    #[test]
    fn test_error_code_constants() {
        use super::error_codes::*;

        // Test lexer error codes
        assert_eq!(UNTERMINATED_STRING.as_str(), "E1001");
        assert_eq!(UNTERMINATED_COMMENT.as_str(), "E1002");
        assert_eq!(INVALID_NUMBER.as_str(), "E1003");
        assert_eq!(UNEXPECTED_CHAR.as_str(), "E1004");

        // Test parser error codes
        assert_eq!(EXPECTED_TOKEN.as_str(), "E2001");
        assert_eq!(UNEXPECTED_TOKEN.as_str(), "E2002");
        assert_eq!(MISSING_END.as_str(), "E2008");
        assert_eq!(CLASSES_DISABLED.as_str(), "E2020");

        // Test type checker error codes
        assert_eq!(TYPE_MISMATCH.as_str(), "E3001");
        assert_eq!(UNDEFINED_VARIABLE.as_str(), "E3002");
        assert_eq!(DUPLICATE_DECLARATION.as_str(), "E3003");

        // Test code generator error codes
        assert_eq!(UNSUPPORTED_FEATURE.as_str(), "E4001");

        // Test configuration error codes
        assert_eq!(INVALID_CONFIG.as_str(), "E5001");

        // Test warning codes
        assert_eq!(UNUSED_VARIABLE.as_str(), "W1001");
        assert_eq!(DEPRECATED.as_str(), "W1003");
    }

    #[test]
    fn test_error_codes_are_unique() {
        use super::error_codes::*;
        use std::collections::HashSet;

        let mut codes = HashSet::new();

        // Collect all error codes
        let all_codes = vec![
            // Lexer
            UNTERMINATED_STRING,
            UNTERMINATED_COMMENT,
            INVALID_NUMBER,
            UNEXPECTED_CHAR,
            INVALID_ESCAPE,
            UNTERMINATED_TEMPLATE,
            INVALID_HEX_NUMBER,
            INVALID_BINARY_NUMBER,
            // Parser
            EXPECTED_TOKEN,
            UNEXPECTED_TOKEN,
            EXPECTED_IDENTIFIER,
            EXPECTED_EXPRESSION,
            EXPECTED_TYPE,
            EXPECTED_PATTERN,
            MISSING_SEMICOLON,
            MISSING_END,
            MISSING_THEN,
            MISSING_DO,
            INVALID_PARAMETER,
            INVALID_DESTRUCTURING,
            BREAK_OUTSIDE_LOOP,
            CONTINUE_OUTSIDE_LOOP,
            INVALID_ASSIGNMENT,
            EXPECTED_DOUBLE_GT,
            CLASSES_DISABLED,
            DECORATORS_DISABLED,
            FP_DISABLED,
            // Type checker
            TYPE_MISMATCH,
            UNDEFINED_VARIABLE,
            DUPLICATE_DECLARATION,
            ASSIGN_TO_CONST,
            TYPE_NOT_FOUND,
            PROPERTY_NOT_FOUND,
            WRONG_ARG_COUNT,
            NOT_CALLABLE,
            NOT_INDEXABLE,
            MISSING_RETURN,
            CIRCULAR_TYPE,
            INTERFACE_NOT_FOUND,
            INTERFACE_NOT_IMPLEMENTED,
            ABSTRACT_METHOD_BODY,
            ABSTRACT_METHODS_IN_CONCRETE_CLASS,
            MULTIPLE_CONSTRUCTORS,
            CONSTRAINT_NOT_SATISFIED,
            WRONG_TYPE_ARG_COUNT,
            CANNOT_INFER_TYPE,
            NON_EXHAUSTIVE_MATCH,
            INVALID_MATCH_TYPE,
            GETTER_SETTER_MISMATCH,
            READONLY_PROPERTY,
            PRIVATE_ACCESS,
            PROTECTED_ACCESS,
            INCONSISTENT_OR_PATTERN_BINDINGS,
            INCOMPATIBLE_OR_PATTERN_TYPES,
            EMPTY_OR_PATTERN,
            // Code generator
            UNSUPPORTED_FEATURE,
            SOURCE_MAP_ERROR,
            // Configuration
            INVALID_CONFIG,
            MISSING_CONFIG,
            INVALID_TARGET,
            // Warnings
            UNUSED_VARIABLE,
            UNUSED_IMPORT,
            DEPRECATED,
            UNREACHABLE_CODE,
            IMPLICIT_ANY,
            POSSIBLE_NIL,
            SHADOWED_VARIABLE,
            EMPTY_BLOCK,
            TYPE_TOO_WIDE,
            UNREACHABLE_PATTERN,
        ];

        // Check all codes are unique
        for code in all_codes {
            let key = (code.prefix, code.code);
            assert!(codes.insert(key), "Duplicate error code: {}", code.as_str());
        }
    }

    #[test]
    fn test_error_with_code_and_suggestion() {
        use super::error_codes::*;

        let span = Span::new(0, 5, 1, 1);
        let diag = Diagnostic::error_with_code(
            span,
            TYPE_MISMATCH,
            "Type 'string' is not assignable to type 'number'",
        )
        .with_suggestion(
            span,
            "tonumber(value)".to_string(),
            "Convert to number using tonumber()",
        );

        assert_eq!(diag.code, Some(TYPE_MISMATCH));
        assert_eq!(diag.code.unwrap().as_str(), "E3001");
        assert_eq!(diag.suggestions.len(), 1);
        assert_eq!(diag.suggestions[0].replacement, "tonumber(value)");
    }

    #[test]
    fn test_error_with_code_and_related() {
        use super::error_codes::*;

        let error_span = Span::new(10, 15, 2, 1);
        let decl_span = Span::new(0, 5, 1, 1);

        let diag = Diagnostic::error_with_code(
            error_span,
            DUPLICATE_DECLARATION,
            "Duplicate declaration of 'x'",
        )
        .with_related(decl_span, "Previously declared here");

        assert_eq!(diag.code, Some(DUPLICATE_DECLARATION));
        assert_eq!(diag.code.unwrap().as_str(), "E3003");
        assert_eq!(diag.related_information.len(), 1);
        assert_eq!(
            diag.related_information[0].message,
            "Previously declared here"
        );
    }
}
