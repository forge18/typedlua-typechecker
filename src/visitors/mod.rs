mod access_control;
mod inference;
mod narrowing;

// GenericVisitor types are available from typechecker::generics module directly
pub use narrowing::{narrow_type_from_condition, NarrowingContext, NarrowingVisitor, TypeNarrower};
pub use access_control::{
    AccessControl, AccessControlVisitor, ClassContext, ClassMemberInfo, ClassMemberKind,
};
pub use inference::{TypeInferenceVisitor, TypeInferrer};

pub trait TypeCheckVisitor {
    #[allow(dead_code)]
    fn name(&self) -> &'static str;
}
