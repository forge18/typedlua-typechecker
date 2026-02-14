use crate::cli::diagnostics::DiagnosticHandler;
use crate::core::type_environment::TypeEnvironment;
use crate::utils::symbol_table::SymbolTable;
use crate::visitors::{AccessControl, TypeNarrower};
use luanext_parser::string_interner::CommonIdentifiers;
use luanext_parser::string_interner::StringInterner;
use std::sync::Arc;

pub trait TypeCheckContext<'arena> {
    fn symbol_table(&mut self) -> &mut SymbolTable<'arena>;
    fn type_env(&mut self) -> &mut TypeEnvironment<'arena>;
    fn narrowing(&mut self) -> &mut TypeNarrower<'arena>;
    fn access_control(&mut self) -> &mut AccessControl<'arena>;
    fn interner(&self) -> &StringInterner;
    fn common(&self) -> &CommonIdentifiers;
    fn diagnostic_handler(&self) -> &Arc<dyn DiagnosticHandler>;
}

pub struct TypeCheckContextImpl<'arena> {
    pub symbol_table: SymbolTable<'arena>,
    pub type_env: TypeEnvironment<'arena>,
    pub narrowing: TypeNarrower<'arena>,
    pub access_control: AccessControl<'arena>,
    pub interner: Arc<StringInterner>,
    pub common: Arc<CommonIdentifiers>,
    pub diagnostic_handler: Arc<dyn DiagnosticHandler>,
}

impl<'arena> TypeCheckContextImpl<'arena> {
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

impl<'arena> TypeCheckContext<'arena> for TypeCheckContextImpl<'arena> {
    fn symbol_table(&mut self) -> &mut SymbolTable<'arena> {
        &mut self.symbol_table
    }

    fn type_env(&mut self) -> &mut TypeEnvironment<'arena> {
        &mut self.type_env
    }

    fn narrowing(&mut self) -> &mut TypeNarrower<'arena> {
        &mut self.narrowing
    }

    fn access_control(&mut self) -> &mut AccessControl<'arena> {
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

    // Note: Use proper DI container for creating test contexts
    // This method is commented out due to missing TestDiagnosticHandler
    // pub fn create_test_context() -> TypeCheckContextImpl {
    //     let interner = Arc::new(StringInterner::new());
    //     let common = Arc::new(CommonIdentifiers::new(&interner));
    //     let diagnostic_handler: Arc<dyn DiagnosticHandler> = Arc::new(TestDiagnosticHandler::new());
    //     TypeCheckContextImpl::new(interner, common, diagnostic_handler)
    // }
}
