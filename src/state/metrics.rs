use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Duration;

#[derive(Debug, Default)]
pub struct Metrics {
    pub symbol_lookups: AtomicUsize,
    pub symbol_hits: AtomicUsize,
    pub symbol_misses: AtomicUsize,
    pub type_lookups: AtomicUsize,
    pub type_hits: AtomicUsize,
    pub type_misses: AtomicUsize,
    pub expressions_checked: AtomicUsize,
    pub statements_checked: AtomicUsize,
    pub functions_checked: AtomicUsize,
    pub types_inferred: AtomicUsize,
    pub generic_instantiations: AtomicUsize,
    pub module_resolutions: AtomicUsize,
    pub scope_operations: AtomicUsize,
    pub allocations: AtomicUsize,
    pub expression_times: Mutex<HashMap<&'static str, Vec<Duration>>>,
}

impl Metrics {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reset(&self) {
        self.symbol_lookups.store(0, Ordering::SeqCst);
        self.symbol_hits.store(0, Ordering::SeqCst);
        self.symbol_misses.store(0, Ordering::SeqCst);
        self.type_lookups.store(0, Ordering::SeqCst);
        self.type_hits.store(0, Ordering::SeqCst);
        self.type_misses.store(0, Ordering::SeqCst);
        self.expressions_checked.store(0, Ordering::SeqCst);
        self.statements_checked.store(0, Ordering::SeqCst);
        self.functions_checked.store(0, Ordering::SeqCst);
        self.types_inferred.store(0, Ordering::SeqCst);
        self.generic_instantiations.store(0, Ordering::SeqCst);
        self.module_resolutions.store(0, Ordering::SeqCst);
        self.scope_operations.store(0, Ordering::SeqCst);
        self.allocations.store(0, Ordering::SeqCst);
    }

    pub fn record_symbol_lookup(&self, hit: bool) {
        self.symbol_lookups.fetch_add(1, Ordering::SeqCst);
        if hit {
            self.symbol_hits.fetch_add(1, Ordering::SeqCst);
        } else {
            self.symbol_misses.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn record_type_lookup(&self, hit: bool) {
        self.type_lookups.fetch_add(1, Ordering::SeqCst);
        if hit {
            self.type_hits.fetch_add(1, Ordering::SeqCst);
        } else {
            self.type_misses.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn symbol_hit_rate(&self) -> f64 {
        let total = self.symbol_lookups.load(Ordering::SeqCst);
        if total == 0 {
            return 1.0;
        }
        let hits = self.symbol_hits.load(Ordering::SeqCst);
        hits as f64 / total as f64
    }

    pub fn type_hit_rate(&self) -> f64 {
        let total = self.type_lookups.load(Ordering::SeqCst);
        if total == 0 {
            return 1.0;
        }
        let hits = self.type_hits.load(Ordering::SeqCst);
        hits as f64 / total as f64
    }

    pub fn record_expression_check(&self) {
        self.expressions_checked.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_statement_check(&self) {
        self.statements_checked.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_function_check(&self) {
        self.functions_checked.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_type_inference(&self) {
        self.types_inferred.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_generic_instantiation(&self) {
        self.generic_instantiations.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_scope_operation(&self) {
        self.scope_operations.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_allocation(&self) {
        self.allocations.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_module_resolution(&self) {
        self.module_resolutions.fetch_add(1, Ordering::SeqCst);
    }

    pub fn record_expression_time(&self, expr_type: &'static str, duration: Duration) {
        let mut times = self.expression_times.lock().unwrap();
        times.entry(expr_type).or_default().push(duration);
    }

    pub fn get_summary(&self) -> MetricSummary {
        let symbol_total = self.symbol_lookups.load(Ordering::SeqCst);
        let symbol_hits = self.symbol_hits.load(Ordering::SeqCst);

        let type_total = self.type_lookups.load(Ordering::SeqCst);
        let type_hits = self.type_hits.load(Ordering::SeqCst);

        MetricSummary {
            symbol_lookups: symbol_total,
            symbol_hit_rate: if symbol_total > 0 {
                symbol_hits as f64 / symbol_total as f64
            } else {
                1.0
            },
            type_lookups: type_total,
            type_hit_rate: if type_total > 0 {
                type_hits as f64 / type_total as f64
            } else {
                1.0
            },
            expressions_checked: self.expressions_checked.load(Ordering::SeqCst),
            statements_checked: self.statements_checked.load(Ordering::SeqCst),
            functions_checked: self.functions_checked.load(Ordering::SeqCst),
            types_inferred: self.types_inferred.load(Ordering::SeqCst),
            generic_instantiations: self.generic_instantiations.load(Ordering::SeqCst),
            module_resolutions: self.module_resolutions.load(Ordering::SeqCst),
            scope_operations: self.scope_operations.load(Ordering::SeqCst),
            allocations: self.allocations.load(Ordering::SeqCst),
        }
    }
}

#[derive(Debug)]
pub struct MetricSummary {
    pub symbol_lookups: usize,
    pub symbol_hit_rate: f64,
    pub type_lookups: usize,
    pub type_hit_rate: f64,
    pub expressions_checked: usize,
    pub statements_checked: usize,
    pub functions_checked: usize,
    pub types_inferred: usize,
    pub generic_instantiations: usize,
    pub module_resolutions: usize,
    pub scope_operations: usize,
    pub allocations: usize,
}

impl MetricSummary {
    pub fn format(&self) -> String {
        format!(
            r#"=== Performance Metrics ===
Symbol Lookups: {} (hit rate: {:.1}%)
Type Lookups: {} (hit rate: {:.1}%)
Expressions Checked: {}
Statements Checked: {}
Functions Checked: {}
Types Inferred: {}
Generic Instantiations: {}
Module Resolutions: {}
Scope Operations: {}
Total Allocations: {}"#,
            self.symbol_lookups,
            self.symbol_hit_rate * 100.0,
            self.type_lookups,
            self.type_hit_rate * 100.0,
            self.expressions_checked,
            self.statements_checked,
            self.functions_checked,
            self.types_inferred,
            self.generic_instantiations,
            self.module_resolutions,
            self.scope_operations,
            self.allocations
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ExpressionKind {
    Literal,
    Identifier,
    BinaryOp,
    UnaryOp,
    FunctionCall,
    MethodCall,
    TableAccess,
    Function,
    Table,
    If,
    TypeCast,
    TypeAssertion,
    Other,
}

impl From<&str> for ExpressionKind {
    fn from(s: &str) -> Self {
        match s {
            "Literal" => ExpressionKind::Literal,
            "Identifier" => ExpressionKind::Identifier,
            "BinaryOp" => ExpressionKind::BinaryOp,
            "UnaryOp" => ExpressionKind::UnaryOp,
            "FunctionCall" => ExpressionKind::FunctionCall,
            "MethodCall" => ExpressionKind::MethodCall,
            "TableAccess" => ExpressionKind::TableAccess,
            "Function" => ExpressionKind::Function,
            "Table" => ExpressionKind::Table,
            "If" => ExpressionKind::If,
            "TypeCast" => ExpressionKind::TypeCast,
            "TypeAssertion" => ExpressionKind::TypeAssertion,
            _ => ExpressionKind::Other,
        }
    }
}
