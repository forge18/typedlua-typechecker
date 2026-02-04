//! Mock implementations for testing using DI container
//!
//! This module provides mock services that can be used with the DI container
//! to create isolated, controllable test scenarios.

use crate::cli::diagnostics::{Diagnostic, DiagnosticHandler};
use crate::cli::fs::FileSystem;
use std::io::Error;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// Mock diagnostic handler that collects diagnostics for testing
#[derive(Debug, Default)]
pub struct MockDiagnosticHandler {
    diagnostics: Mutex<Vec<Diagnostic>>,
}

impl MockDiagnosticHandler {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.lock().unwrap().clone()
    }

    pub fn clear(&self) {
        self.diagnostics.lock().unwrap().clear();
    }
}

impl DiagnosticHandler for MockDiagnosticHandler {
    fn report(&self, diagnostic: Diagnostic) {
        self.diagnostics.lock().unwrap().push(diagnostic);
    }

    fn has_errors(&self) -> bool {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .any(|d| matches!(d.level, crate::cli::diagnostics::DiagnosticLevel::Error))
    }

    fn error_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| matches!(d.level, crate::cli::diagnostics::DiagnosticLevel::Error))
            .count()
    }

    fn warning_count(&self) -> usize {
        self.diagnostics
            .lock()
            .unwrap()
            .iter()
            .filter(|d| matches!(d.level, crate::cli::diagnostics::DiagnosticLevel::Warning))
            .count()
    }

    fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.lock().unwrap().clone()
    }
}

/// Mock file system for testing
#[derive(Debug, Default)]
pub struct MockFileSystem {
    files: Mutex<std::collections::HashMap<String, String>>,
}

impl MockFileSystem {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_file(&self, path: &str, content: &str) {
        self.files
            .lock()
            .unwrap()
            .insert(path.to_string(), content.to_string());
    }

    pub fn clear(&self) {
        self.files.lock().unwrap().clear();
    }
}

impl FileSystem for MockFileSystem {
    fn read_file(&self, path: &Path) -> Result<String, Error> {
        let files = self.files.lock().unwrap();
        let path_str = path.to_string_lossy().into_owned();

        files
            .get(&path_str)
            .cloned()
            .ok_or_else(|| Error::new(std::io::ErrorKind::NotFound, "File not found"))
    }

    fn write_file(&self, path: &Path, content: &str) -> Result<(), Error> {
        let mut files = self.files.lock().unwrap();
        let path_str = path.to_string_lossy().into_owned();
        files.insert(path_str, content.to_string());
        Ok(())
    }

    fn exists(&self, path: &Path) -> bool {
        let files = self.files.lock().unwrap();
        let path_str = path.to_string_lossy().into_owned();
        files.contains_key(&path_str)
    }

    fn resolve_path(&self, base: &Path, relative: &str) -> PathBuf {
        base.join(relative)
    }
}
