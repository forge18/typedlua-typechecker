use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};

/// File system abstraction for dependency injection
pub trait FileSystem: Send + Sync {
    fn read_file(&self, path: &Path) -> Result<String, std::io::Error>;
    fn write_file(&self, path: &Path, content: &str) -> Result<(), std::io::Error>;
    fn exists(&self, path: &Path) -> bool;
    fn resolve_path(&self, base: &Path, relative: &str) -> PathBuf;
}

/// Real file system implementation
pub struct RealFileSystem;

impl RealFileSystem {
    pub fn new() -> Self {
        Self
    }
}

impl Default for RealFileSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl FileSystem for RealFileSystem {
    fn read_file(&self, path: &Path) -> Result<String, std::io::Error> {
        std::fs::read_to_string(path)
    }

    fn write_file(&self, path: &Path, content: &str) -> Result<(), std::io::Error> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, content)
    }

    fn exists(&self, path: &Path) -> bool {
        path.exists()
    }

    fn resolve_path(&self, base: &Path, relative: &str) -> PathBuf {
        base.join(relative)
    }
}

/// Mock file system for testing
pub struct MockFileSystem {
    files: FxHashMap<PathBuf, String>,
}

impl MockFileSystem {
    pub fn new() -> Self {
        Self {
            files: FxHashMap::default(),
        }
    }

    pub fn add_file(&mut self, path: impl Into<PathBuf>, content: impl Into<String>) {
        self.files.insert(path.into(), content.into());
    }
}

impl Default for MockFileSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl FileSystem for MockFileSystem {
    fn read_file(&self, path: &Path) -> Result<String, std::io::Error> {
        self.files.get(path).cloned().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("File not found: {}", path.display()),
            )
        })
    }

    fn write_file(&self, _path: &Path, _content: &str) -> Result<(), std::io::Error> {
        // Mock implementation - could track writes if needed
        Ok(())
    }

    fn exists(&self, path: &Path) -> bool {
        self.files.contains_key(path)
    }

    fn resolve_path(&self, base: &Path, relative: &str) -> PathBuf {
        base.join(relative)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mock_fs_read() {
        let mut fs = MockFileSystem::new();
        fs.add_file("/test.txt", "Hello, world!");

        let content = fs.read_file(Path::new("/test.txt")).unwrap();
        assert_eq!(content, "Hello, world!");
    }

    #[test]
    fn test_mock_fs_not_found() {
        let fs = MockFileSystem::new();
        let result = fs.read_file(Path::new("/nonexistent.txt"));
        assert!(result.is_err());
    }

    #[test]
    fn test_mock_fs_exists() {
        let mut fs = MockFileSystem::new();
        fs.add_file("/test.txt", "content");

        assert!(fs.exists(Path::new("/test.txt")));
        assert!(!fs.exists(Path::new("/other.txt")));
    }

    #[test]
    fn test_resolve_path() {
        let fs = RealFileSystem::new();
        let resolved = fs.resolve_path(Path::new("/base"), "relative/path.txt");
        assert_eq!(resolved, PathBuf::from("/base/relative/path.txt"));
    }
}
