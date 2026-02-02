use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("Lexical analysis failed with {0} errors")]
    LexicalErrors(usize),

    #[error("Parsing failed with {0} errors")]
    ParseErrors(usize),

    #[error("Type checking failed with {0} errors")]
    TypeErrors(usize),

    #[error("Code generation failed: {0}")]
    CodeGenError(String),

    #[error("Configuration error: {0}")]
    ConfigError(String),
}

#[derive(Debug, Error)]
pub enum ResolutionError {
    #[error("Module not found: {0}")]
    ModuleNotFound(String),

    #[error("Circular dependency detected: {0}")]
    CircularDependency(String),

    #[error("Non-typed Lua file without type definitions: {0}")]
    MissingTypeDefinitions(String),

    #[error("Ambiguous module resolution: {0}")]
    AmbiguousResolution(String),
}

#[derive(Debug, Error)]
pub enum LexerError {
    #[error("Unexpected character: {0}")]
    UnexpectedCharacter(char),

    #[error("Unterminated string literal")]
    UnterminatedString,

    #[error("Unterminated comment")]
    UnterminatedComment,

    #[error("Invalid number literal: {0}")]
    InvalidNumber(String),

    #[error("Invalid escape sequence: {0}")]
    InvalidEscape(String),
}

#[derive(Debug, Error)]
pub enum ParserError {
    #[error("Unexpected token: expected {expected}, found {found}")]
    UnexpectedToken { expected: String, found: String },

    #[error("Unexpected end of file")]
    UnexpectedEof,

    #[error("Feature disabled: {0}")]
    DisabledFeature(String),

    #[error("Invalid syntax: {0}")]
    InvalidSyntax(String),
}

#[derive(Debug, Error)]
pub enum TypeCheckError {
    #[error("Type mismatch: expected {expected}, found {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("Undefined variable: {0}")]
    UndefinedVariable(String),

    #[error("Undefined type: {0}")]
    UndefinedType(String),

    #[error("Cannot reassign const variable: {0}")]
    ConstReassignment(String),

    #[error("Duplicate declaration: {0}")]
    DuplicateDeclaration(String),

    #[error("Invalid operation: {0}")]
    InvalidOperation(String),
}
