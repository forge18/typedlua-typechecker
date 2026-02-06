//! Incremental Type Checking Infrastructure
//!
//! This module implements declaration-level incremental type checking. The key insight
//! is that body-only changes don't invalidate callers - only signature changes do.

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::hash::{Hash, Hasher};
use std::path::PathBuf;
use typedlua_parser::ast::pattern::Pattern;
use typedlua_parser::ast::statement::*;
use typedlua_parser::ast::types::*;
use typedlua_parser::prelude::EnumValue;
use typedlua_parser::string_interner::StringInterner;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DeclarationId {
    pub module_path: PathBuf,
    pub declaration_name: String,
}

impl DeclarationId {
    pub fn new(module_path: PathBuf, declaration_name: String) -> Self {
        Self {
            module_path,
            declaration_name,
        }
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CompilationCache {
    pub declaration_hashes: FxHashMap<DeclarationId, u64>,
    pub dependency_graph: DependencyGraph,
    pub version: u32,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DependencyGraph {
    dependents: FxHashMap<DeclarationId, Vec<DeclarationId>>,
    dependencies: FxHashMap<DeclarationId, Vec<DeclarationId>>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            dependents: FxHashMap::default(),
            dependencies: FxHashMap::default(),
        }
    }

    pub fn add_dependency(&mut self, caller: DeclarationId, callee: DeclarationId) {
        self.dependencies
            .entry(caller.clone())
            .or_default()
            .push(callee.clone());

        self.dependents.entry(callee).or_default().push(caller);
    }

    pub fn get_dependents(&self, decl: &DeclarationId) -> Vec<DeclarationId> {
        self.dependents.get(decl).cloned().unwrap_or_default()
    }

    pub fn get_dependencies(&self, decl: &DeclarationId) -> Vec<DeclarationId> {
        self.dependencies.get(decl).cloned().unwrap_or_default()
    }

    pub fn clear(&mut self) {
        self.dependents.clear();
        self.dependencies.clear();
    }

    pub fn merge(&mut self, other: DependencyGraph) {
        for (caller, callees) in other.dependencies {
            for callee in callees {
                self.add_dependency(caller.clone(), callee);
            }
        }
    }
}

pub trait DeclarationHash {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64;
}

struct FxHasher {
    state: u64,
}

impl FxHasher {
    fn new() -> Self {
        Self {
            state: 0xcbf29ce484222325,
        }
    }
}

impl Hasher for FxHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut hash = self.state;
        for &byte in bytes {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        self.state = hash;
    }
}

fn hash_parameter_name(pattern: &Pattern, interner: &StringInterner, hasher: &mut FxHasher) {
    match pattern {
        Pattern::Identifier(ident) => {
            interner.resolve(ident.node).hash(hasher);
        }
        _ => {
            "_".hash(hasher);
        }
    }
}

impl DeclarationHash for FunctionDeclaration {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64 {
        let mut hasher = FxHasher::new();
        interner.resolve(self.name.node).hash(&mut hasher);

        if let Some(type_params) = &self.type_parameters {
            type_params.len().hash(&mut hasher);
            for tp in type_params {
                interner.resolve(tp.name.node).hash(&mut hasher);
                if let Some(constraint) = &tp.constraint {
                    hash_type(constraint, interner, &mut hasher);
                }
            }
        }

        self.parameters.len().hash(&mut hasher);
        for param in &self.parameters {
            hash_parameter_name(&param.pattern, interner, &mut hasher);
            if let Some(type_ann) = &param.type_annotation {
                hash_type(type_ann, interner, &mut hasher);
            }
            param.is_rest.hash(&mut hasher);
        }

        if let Some(return_type) = &self.return_type {
            hash_type(return_type, interner, &mut hasher);
        }

        if let Some(throws) = &self.throws {
            throws.len().hash(&mut hasher);
            for throw_type in throws {
                hash_type(throw_type, interner, &mut hasher);
            }
        }

        hasher.finish()
    }
}

impl DeclarationHash for ClassDeclaration {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64 {
        let mut hasher = FxHasher::new();
        interner.resolve(self.name.node).hash(&mut hasher);

        if let Some(type_params) = &self.type_parameters {
            type_params.len().hash(&mut hasher);
            for tp in type_params {
                interner.resolve(tp.name.node).hash(&mut hasher);
            }
        }

        if let Some(extends) = &self.extends {
            hash_type(extends, interner, &mut hasher);
        }

        self.implements.len().hash(&mut hasher);
        for impl_type in &self.implements {
            hash_type(impl_type, interner, &mut hasher);
        }

        self.is_abstract.hash(&mut hasher);
        self.is_final.hash(&mut hasher);

        hasher.finish()
    }
}

impl DeclarationHash for InterfaceDeclaration {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64 {
        let mut hasher = FxHasher::new();
        interner.resolve(self.name.node).hash(&mut hasher);

        if let Some(type_params) = &self.type_parameters {
            type_params.len().hash(&mut hasher);
            for tp in type_params {
                interner.resolve(tp.name.node).hash(&mut hasher);
            }
        }

        self.extends.len().hash(&mut hasher);
        for extends_type in &self.extends {
            hash_type(extends_type, interner, &mut hasher);
        }

        self.members.len().hash(&mut hasher);

        hasher.finish()
    }
}

impl DeclarationHash for TypeAliasDeclaration {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64 {
        let mut hasher = FxHasher::new();
        interner.resolve(self.name.node).hash(&mut hasher);

        if let Some(type_params) = &self.type_parameters {
            type_params.len().hash(&mut hasher);
            for tp in type_params {
                interner.resolve(tp.name.node).hash(&mut hasher);
            }
        }

        hash_type(&self.type_annotation, interner, &mut hasher);

        hasher.finish()
    }
}

impl DeclarationHash for EnumDeclaration {
    fn compute_signature_hash(&self, interner: &StringInterner) -> u64 {
        let mut hasher = FxHasher::new();
        interner.resolve(self.name.node).hash(&mut hasher);

        self.members.len().hash(&mut hasher);
        for member in &self.members {
            interner.resolve(member.name.node).hash(&mut hasher);
            if let Some(value) = &member.value {
                match value {
                    EnumValue::Number(n) => n.to_bits().hash(&mut hasher),
                    EnumValue::String(s) => s.hash(&mut hasher),
                }
            }
        }

        hasher.finish()
    }
}

fn hash_type(typ: &Type, interner: &StringInterner, hasher: &mut FxHasher) {
    match &typ.kind {
        TypeKind::Primitive(primitive) => {
            0u8.hash(hasher);
            match primitive {
                PrimitiveType::Nil => 0u8.hash(hasher),
                PrimitiveType::Boolean => 1u8.hash(hasher),
                PrimitiveType::Number => 2u8.hash(hasher),
                PrimitiveType::Integer => 3u8.hash(hasher),
                PrimitiveType::String => 4u8.hash(hasher),
                _ => 5u8.hash(hasher),
            }
        }
        TypeKind::Reference(ref_ref) => {
            1u8.hash(hasher);
            interner.resolve(ref_ref.name.node).hash(hasher);
        }
        TypeKind::Function(func) => {
            2u8.hash(hasher);
            hash_function_type(func, interner, hasher);
        }
        TypeKind::Array(elem) => {
            3u8.hash(hasher);
            hash_type(elem, interner, hasher);
        }
        TypeKind::Tuple(elements) => {
            4u8.hash(hasher);
            elements.len().hash(hasher);
        }
        TypeKind::Union(members) => {
            5u8.hash(hasher);
            members.len().hash(hasher);
        }
        _ => {
            99u8.hash(hasher);
        }
    }
}

fn hash_function_type(func: &FunctionType, interner: &StringInterner, hasher: &mut FxHasher) {
    if let Some(type_params) = &func.type_parameters {
        type_params.len().hash(hasher);
    }

    func.parameters.len().hash(hasher);

    hash_type(&func.return_type, interner, hasher);
}

#[derive(Debug, Clone)]
pub struct InvalidationResult {
    pub invalidated_declarations: Vec<DeclarationId>,
    pub cache_dirty: bool,
}

impl InvalidationResult {
    pub fn nothing_invalidated() -> Self {
        Self {
            invalidated_declarations: Vec::new(),
            cache_dirty: false,
        }
    }

    pub fn all_invalidated() -> Self {
        Self {
            invalidated_declarations: Vec::new(),
            cache_dirty: true,
        }
    }
}

pub fn compute_invalidated_decls(
    old_cache: &CompilationCache,
    new_hashes: &FxHashMap<DeclarationId, u64>,
    deleted_decls: &[DeclarationId],
) -> InvalidationResult {
    let mut invalidated = Vec::new();
    let mut cache_dirty = false;

    for (decl_id, new_hash) in new_hashes {
        if let Some(old_hash) = old_cache.declaration_hashes.get(decl_id) {
            if new_hash != old_hash {
                invalidated.push(decl_id.clone());
                let dependents = old_cache.dependency_graph.get_dependents(decl_id);
                invalidated.extend(dependents);
                cache_dirty = true;
            }
        } else {
            cache_dirty = true;
        }
    }

    for decl_id in deleted_decls {
        if old_cache.declaration_hashes.contains_key(decl_id) {
            let dependents = old_cache.dependency_graph.get_dependents(decl_id);
            invalidated.extend(dependents);
            cache_dirty = true;
        }
    }

    InvalidationResult {
        invalidated_declarations: invalidated,
        cache_dirty,
    }
}

pub struct IncrementalChecker {
    cache: CompilationCache,
}

impl IncrementalChecker {
    pub fn new() -> Self {
        Self {
            cache: CompilationCache::default(),
        }
    }

    pub fn set_cache(&mut self, cache: CompilationCache) {
        self.cache = cache;
    }

    pub fn take_cache(&mut self) -> CompilationCache {
        std::mem::take(&mut self.cache)
    }

    pub fn compute_declaration_hashes(
        &self,
        program: &typedlua_parser::ast::Program,
        module_path: PathBuf,
        interner: &StringInterner,
    ) -> FxHashMap<DeclarationId, u64> {
        let mut hashes = FxHashMap::default();

        for statement in &program.statements {
            match statement {
                Statement::Function(func) => {
                    let name = interner.resolve(func.name.node).to_string();
                    let decl_id = DeclarationId::new(module_path.clone(), name);
                    let hash = func.compute_signature_hash(interner);
                    hashes.insert(decl_id, hash);
                }
                Statement::Class(class) => {
                    let name = interner.resolve(class.name.node).to_string();
                    let decl_id = DeclarationId::new(module_path.clone(), name);
                    let hash = class.compute_signature_hash(interner);
                    hashes.insert(decl_id, hash);
                }
                Statement::Interface(iface) => {
                    let name = interner.resolve(iface.name.node).to_string();
                    let decl_id = DeclarationId::new(module_path.clone(), name);
                    let hash = iface.compute_signature_hash(interner);
                    hashes.insert(decl_id, hash);
                }
                Statement::TypeAlias(alias) => {
                    let name = interner.resolve(alias.name.node).to_string();
                    let decl_id = DeclarationId::new(module_path.clone(), name);
                    let hash = alias.compute_signature_hash(interner);
                    hashes.insert(decl_id, hash);
                }
                Statement::Enum(enum_decl) => {
                    let name = interner.resolve(enum_decl.name.node).to_string();
                    let decl_id = DeclarationId::new(module_path.clone(), name);
                    let hash = enum_decl.compute_signature_hash(interner);
                    hashes.insert(decl_id, hash);
                }
                _ => {}
            }
        }

        hashes
    }

    pub fn update_cache(
        &mut self,
        new_hashes: FxHashMap<DeclarationId, u64>,
        dependencies: DependencyGraph,
    ) {
        self.cache.declaration_hashes = new_hashes;
        self.cache.dependency_graph = dependencies;
        self.cache.version += 1;
    }
}

impl Default for IncrementalChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dependency_graph() {
        let mut graph = DependencyGraph::new();

        let a = DeclarationId::new(PathBuf::from("a.lua"), "a".to_string());
        let b = DeclarationId::new(PathBuf::from("b.lua"), "b".to_string());
        let c = DeclarationId::new(PathBuf::from("c.lua"), "c".to_string());

        graph.add_dependency(a.clone(), b.clone());
        graph.add_dependency(b.clone(), c.clone());

        let b_dependents = graph.get_dependents(&b);
        assert_eq!(b_dependents.len(), 1);
        assert_eq!(b_dependents[0], a);

        let c_dependents = graph.get_dependents(&c);
        assert_eq!(c_dependents.len(), 1);
        assert_eq!(c_dependents[0], b);

        let a_deps = graph.get_dependencies(&a);
        assert_eq!(a_deps.len(), 1);
        assert_eq!(a_deps[0], b);
    }

    #[test]
    fn test_invalidation_result() {
        let result = InvalidationResult::nothing_invalidated();
        assert!(result.invalidated_declarations.is_empty());
        assert!(!result.cache_dirty);
    }

    #[test]
    fn test_compilation_cache_serialization() {
        let cache = CompilationCache::default();
        assert_eq!(cache.version, 0);
        assert!(cache.declaration_hashes.is_empty());
    }
}
