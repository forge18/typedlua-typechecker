use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_environment::TypeEnvironment;
use crate::utils::symbol_table::SymbolTable;
use crate::visitors::{AccessControl, TypeNarrower};
use std::sync::Arc;
use typedlua_parser::string_interner::CommonIdentifiers;
use typedlua_parser::string_interner::StringInterner;

pub trait TypeCheckContext {
    fn symbol_table(&mut self) -> &mut SymbolTable;
    fn type_env(&mut self) -> &mut TypeEnvironment;
    fn narrowing(&mut self) -> &mut TypeNarrower;
    fn access_control(&mut self) -> &mut AccessControl;
    fn interner(&self) -> &StringInterner;
    fn common(&self) -> &CommonIdentifiers;
    fn diagnostic_handler(&self) -> &Arc<dyn DiagnosticHandler>;
}

pub struct TypeCheckContextImpl {
    pub symbol_table: SymbolTable,
    pub type_env: TypeEnvironment,
    pub narrowing: TypeNarrower,
    pub access_control: AccessControl,
    pub interner: Arc<StringInterner>,
    pub common: Arc<CommonIdentifiers>,
    pub diagnostic_handler: Arc<dyn DiagnosticHandler>,
}

impl TypeCheckContextImpl {
    pub fn new(
        interner: Arc<StringInterner>,
        common: Arc<CommonIdentifiers>,
        diagnostic_handler: Arc<dyn DiagnosticHandler>,
    ) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            type_env: TypeEnvironment::new(),
            narrowing: TypeNarrower::new(),
            access_control: AccessControl::new(),
            interner,
            common,
            diagnostic_handler,
        }
    }
}

impl TypeCheckContext for TypeCheckContextImpl {
    fn symbol_table(&mut self) -> &mut SymbolTable {
        &mut self.symbol_table
    }

    fn type_env(&mut self) -> &mut TypeEnvironment {
        &mut self.type_env
    }

    fn narrowing(&mut self) -> &mut TypeNarrower {
        &mut self.narrowing
    }

    fn access_control(&mut self) -> &mut AccessControl {
        &mut self.access_control
    }

    fn interner(&self) -> &StringInterner {
        &self.interner
    }

    fn common(&self) -> &CommonIdentifiers {
        &self.common
    }

    fn diagnostic_handler(&self) -> &Arc<dyn DiagnosticHandler> {
        &self.diagnostic_handler
    }
}

#[cfg(test)]
pub mod test_helpers {
    use super::*;

    // Note: Use proper DI container for creating test contexts
    // This method is commented out due to missing TestDiagnosticHandler
    // pub fn create_test_context() -> TypeCheckContextImpl {
    //     let interner = Arc::new(StringInterner::new());
    //     let common = Arc::new(CommonIdentifiers::new(&interner));
    //     let diagnostic_handler: Arc<dyn DiagnosticHandler> = Arc::new(TestDiagnosticHandler::new());
    //     TypeCheckContextImpl::new(interner, common, diagnostic_handler)
    // }
}
