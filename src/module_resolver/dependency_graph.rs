use super::error::{ModuleError, ModuleId};
use rustc_hash::{FxHashMap, FxHashSet};

/// Dependency graph for module compilation ordering
#[derive(Debug)]
pub struct DependencyGraph {
    /// Adjacency list: module_id -> dependencies
    edges: FxHashMap<ModuleId, Vec<ModuleId>>,
    /// All known modules
    nodes: FxHashSet<ModuleId>,
}

impl DependencyGraph {
    pub fn new() -> Self {
        Self {
            edges: FxHashMap::default(),
            nodes: FxHashSet::default(),
        }
    }

    /// Add a module and its dependencies to the graph
    pub fn add_module(&mut self, id: ModuleId, dependencies: Vec<ModuleId>) {
        self.nodes.insert(id.clone());
        for dep in &dependencies {
            self.nodes.insert(dep.clone());
        }
        self.edges.insert(id, dependencies);
    }

    /// Perform topological sort to determine compilation order
    ///
    /// Returns modules in dependency order (dependencies first)
    /// or an error if a circular dependency is detected
    pub fn topological_sort(&self) -> Result<Vec<ModuleId>, ModuleError> {
        let mut sorted = Vec::new();
        let mut visited = FxHashSet::default();
        let mut visiting = FxHashSet::default();

        for node in &self.nodes {
            if !visited.contains(node) {
                self.visit(
                    node,
                    &mut visited,
                    &mut visiting,
                    &mut sorted,
                    &mut Vec::new(),
                )?;
            }
        }

        Ok(sorted)
    }

    /// DFS visit for topological sort with cycle detection
    fn visit(
        &self,
        node: &ModuleId,
        visited: &mut FxHashSet<ModuleId>,
        visiting: &mut FxHashSet<ModuleId>,
        sorted: &mut Vec<ModuleId>,
        path: &mut Vec<ModuleId>,
    ) -> Result<(), ModuleError> {
        if visiting.contains(node) {
            // Circular dependency detected - extract cycle from path
            let cycle_start = path.iter().position(|n| n == node).unwrap();
            let mut cycle: Vec<ModuleId> = path[cycle_start..].to_vec();
            cycle.push(node.clone());
            return Err(ModuleError::CircularDependency { cycle });
        }

        if visited.contains(node) {
            return Ok(());
        }

        visiting.insert(node.clone());
        path.push(node.clone());

        // Visit dependencies
        if let Some(deps) = self.edges.get(node) {
            for dep in deps {
                self.visit(dep, visited, visiting, sorted, path)?;
            }
        }

        path.pop();
        visiting.remove(node);
        visited.insert(node.clone());
        sorted.push(node.clone());

        Ok(())
    }

    /// Get direct dependencies of a module
    pub fn get_dependencies(&self, id: &ModuleId) -> Option<&Vec<ModuleId>> {
        self.edges.get(id)
    }

    /// Check if the graph contains a module
    pub fn contains(&self, id: &ModuleId) -> bool {
        self.nodes.contains(id)
    }

    /// Get all modules in the graph
    pub fn modules(&self) -> impl Iterator<Item = &ModuleId> {
        self.nodes.iter()
    }
}

impl Default for DependencyGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_id(name: &str) -> ModuleId {
        ModuleId::new(PathBuf::from(name))
    }

    #[test]
    fn test_simple_topological_sort() {
        let mut graph = DependencyGraph::new();

        // a depends on b, b depends on c
        graph.add_module(make_id("c"), vec![]);
        graph.add_module(make_id("b"), vec![make_id("c")]);
        graph.add_module(make_id("a"), vec![make_id("b")]);

        let sorted = graph.topological_sort().unwrap();

        // c should come before b, b before a
        let c_pos = sorted.iter().position(|id| id.as_str() == "c").unwrap();
        let b_pos = sorted.iter().position(|id| id.as_str() == "b").unwrap();
        let a_pos = sorted.iter().position(|id| id.as_str() == "a").unwrap();

        assert!(c_pos < b_pos);
        assert!(b_pos < a_pos);
    }

    #[test]
    fn test_diamond_dependency() {
        let mut graph = DependencyGraph::new();

        // a depends on b and c, both b and c depend on d
        graph.add_module(make_id("d"), vec![]);
        graph.add_module(make_id("b"), vec![make_id("d")]);
        graph.add_module(make_id("c"), vec![make_id("d")]);
        graph.add_module(make_id("a"), vec![make_id("b"), make_id("c")]);

        let sorted = graph.topological_sort().unwrap();

        // d should come before b and c, both should come before a
        let d_pos = sorted.iter().position(|id| id.as_str() == "d").unwrap();
        let b_pos = sorted.iter().position(|id| id.as_str() == "b").unwrap();
        let c_pos = sorted.iter().position(|id| id.as_str() == "c").unwrap();
        let a_pos = sorted.iter().position(|id| id.as_str() == "a").unwrap();

        assert!(d_pos < b_pos);
        assert!(d_pos < c_pos);
        assert!(b_pos < a_pos);
        assert!(c_pos < a_pos);
    }

    #[test]
    fn test_circular_dependency_detected() {
        let mut graph = DependencyGraph::new();

        // a depends on b, b depends on c, c depends on a (cycle)
        graph.add_module(make_id("a"), vec![make_id("b")]);
        graph.add_module(make_id("b"), vec![make_id("c")]);
        graph.add_module(make_id("c"), vec![make_id("a")]);

        let result = graph.topological_sort();

        assert!(result.is_err());
        if let Err(ModuleError::CircularDependency { cycle }) = result {
            assert!(cycle.len() >= 3);
            // Verify cycle contains a, b, c
            assert!(cycle.iter().any(|id| id.as_str() == "a"));
            assert!(cycle.iter().any(|id| id.as_str() == "b"));
            assert!(cycle.iter().any(|id| id.as_str() == "c"));
        } else {
            panic!("Expected CircularDependency error");
        }
    }

    #[test]
    fn test_self_dependency() {
        let mut graph = DependencyGraph::new();

        // a depends on itself
        graph.add_module(make_id("a"), vec![make_id("a")]);

        let result = graph.topological_sort();

        assert!(result.is_err());
        if let Err(ModuleError::CircularDependency { cycle }) = result {
            assert_eq!(cycle.len(), 2); // [a, a]
            assert_eq!(cycle[0].as_str(), "a");
        } else {
            panic!("Expected CircularDependency error");
        }
    }

    #[test]
    fn test_no_dependencies() {
        let mut graph = DependencyGraph::new();

        graph.add_module(make_id("a"), vec![]);
        graph.add_module(make_id("b"), vec![]);
        graph.add_module(make_id("c"), vec![]);

        let sorted = graph.topological_sort().unwrap();

        assert_eq!(sorted.len(), 3);
        // Order doesn't matter since there are no dependencies
    }
}
