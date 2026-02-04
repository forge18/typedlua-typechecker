//! Test utilities and mocks for comprehensive testing
//!
//! This module provides testing infrastructure that leverages the DI container
//! to create isolated, maintainable test scenarios.

#[cfg(test)]
pub mod integration_tests;
pub mod mocks;
#[cfg(test)]
pub mod module_tests;
