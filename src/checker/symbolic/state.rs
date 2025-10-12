use crate::checker::symbolic::expr::{BoolExpr, SymExpr};
use im::{HashMap, Vector};

/// Path-local symbolic state with a persistent store and path conditions.
/// All updates are functional (return a new state) to exploit structural sharing.
#[derive(Clone, Debug)]
pub struct SymbolicState {
    /// Persistent mapping from abstract addresses to symbolic expressions.
    /// Key is (var_id, offset), see the design notes in the previous snippet.
    store: HashMap<(usize, usize), SymExpr>,

    /// Persistent sequence of path conditions (conjoined at the path level).
    path_cond: Vector<BoolExpr>,
}

impl SymbolicState {
    /// Creates an empty symbolic state.
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            path_cond: Vector::new(),
        }
    }

    /// Returns the persistent vector of path conditions (read-only view).
    pub fn path_condition(&self) -> &Vector<BoolExpr> {
        &self.path_cond
    }

    /// Returns a new state with `cond` appended to the path condition.
    pub fn with_pc(&self, cond: BoolExpr) -> Self {
        // Persistent vector updates in-place on the cloned state.
        let mut next = self.clone();
        next.path_cond.push_back(cond);
        next
    }

    /// Reads the binding at address (var_id, offset), if present.
    pub fn read(&self, var_id: usize, offset: usize) -> Option<&SymExpr> {
        self.store.get(&(var_id, offset))
    }

    /// Returns a new state with (var_id, offset) bound to `value` (overwriting if present).
    pub fn with_write(&self, var_id: usize, offset: usize, value: SymExpr) -> Self {
        let mut next: SymbolicState = self.clone();
        next.store = next.store.update((var_id, offset), value);
        next
    }

    /// Returns a new state without the binding at (var_id, offset) and whether it existed.
    pub fn without(&self, var_id: usize, offset: usize) -> (Self, bool) {
        let existed = self.store.contains_key(&(var_id, offset));
        // `without` returns a new map with the key removed.
        let mut next = self.clone();
        next.store = self.store.without(&(var_id, offset));
        (next, existed)
    }

    /// Returns an iterator over all address→expression bindings.
    pub fn iter_bindings(&self) -> impl Iterator<Item = (&(usize, usize), &SymExpr)> {
        self.store.iter()
    }

    /// Convenience predicate for address membership.
    pub fn contains(&self, var_id: usize, offset: usize) -> bool {
        self.store.contains_key(&(var_id, offset))
    }

    /* --------  mutable façade (wraps functional updates) --------
       These provide ergonomic &mut self methods while preserving persistence
       under the hood. They simply rebind `self` to the newly created structure.
    */

    /// Mutating façade: append a path condition by rebinding the persistent vector.
    pub fn assert_pc(&mut self, cond: BoolExpr) {
        // In-place update leveraging structural sharing.
        self.path_cond.push_back(cond);
    }

    /// Mutating façade: write by rebinding the persistent map.
    pub fn write(&mut self, var_id: usize, offset: usize, value: SymExpr) {
        self.store = self.store.update((var_id, offset), value);
    }

    /// Mutating façade: remove by rebinding the persistent map and return old value (if any).
    pub fn kill(&mut self, var_id: usize, offset: usize) -> Option<SymExpr> {
        let key = (var_id, offset);
        let old = self.store.get(&key).cloned();
        self.store = self.store.without(&key);
        old
    }
}
