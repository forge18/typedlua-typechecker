//! Type checker phase modules
//!
//! This module contains the decomposed phases of type checking, extracted from
//! the monolithic type_checker.rs to improve maintainability and reduce cognitive load.
//!
//! Each phase handles a specific aspect of type checking:
//! - `module_phase`: Import/export resolution and module dependency tracking
//! - `declaration_phase`: Symbol declaration and registration (PASS 1)
//! - `declaration_checking_phase`: Type alias, enum, interface checking (PASS 2)
//! - `validation_phase`: Type compatibility and validation checks
//! - `inference_phase`: Statement and expression type inference

pub mod declaration_checking_phase;
pub mod declaration_phase;
pub mod inference_phase;
pub mod module_phase;
pub mod validation_phase;
