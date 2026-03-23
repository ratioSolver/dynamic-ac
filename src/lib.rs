use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Display, Formatter},
};

type Callback = Box<dyn Fn(&Engine, usize)>;

#[derive(Debug, PartialEq)]
enum PropagationError {
    DomainWipeout(usize), // The ID of the variable that became empty
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintKind {
    Equality,
    Inequality,
    Set(i32),
    Forbid(i32),
}

struct ValueState {
    value: i32,
    suppressed_by: Option<usize>,
}

pub struct Engine {
    values: Vec<Vec<ValueState>>,
    constraints: HashMap<usize, (usize, usize, ConstraintKind)>,
    listeners: HashMap<usize, Vec<Callback>>,
}
impl Engine {
    /// Creates a new empty constraint engine.
    ///
    /// The returned engine has no variables, no constraints, and no listeners.
    pub fn new() -> Self {
        Self { values: Vec::new(), constraints: HashMap::new(), listeners: HashMap::new() }
    }

    /// Adds a variable with the provided initial domain.
    ///
    /// Returns the variable ID that can be used with methods like
    /// [`Engine::val`], [`Engine::new_eq`], and [`Engine::new_neq`].
    ///
    /// All inserted values start as active (not suppressed).
    pub fn add_var(&mut self, values: Vec<i32>) -> usize {
        let id = self.values.len();
        self.values.push(values.into_iter().map(|v| ValueState { value: v, suppressed_by: None }).collect());
        id
    }

    /// Returns the currently active domain values of a variable.
    ///
    /// Suppressed values are excluded from the returned vector.
    ///
    /// Panics if `var` is not a valid variable ID.
    pub fn val(&self, var: usize) -> Vec<i32> {
        self.values[var].iter().filter(|s| s.suppressed_by.is_none()).map(|s| s.value).collect()
    }

    /// Adds an equality constraint between two variables and propagates it.
    ///
    /// On success, returns the newly assigned constraint ID.
    ///
    /// On failure, returns `(constraint_id, explanation)` where `explanation`
    /// contains IDs of constraints involved in the domain wipeout.
    /// The newly created constraint remains in the engine and can be removed
    /// with [`Engine::retract_constraint`].
    pub fn new_eq(&mut self, var1: usize, var2: usize) -> Result<usize, (usize, Vec<usize>)> {
        let id = self.constraints.len();
        self.constraints.insert(id, (var1, var2, ConstraintKind::Equality));
        self.propagate(id).map_err(|e| match e {
            PropagationError::DomainWipeout(var_id) => (id, self.get_conflict_explanation(var_id)),
        })?;
        Ok(id)
    }

    /// Adds an inequality constraint between two variables and propagates it.
    ///
    /// On success, returns the newly assigned constraint ID.
    ///
    /// On failure, returns `(constraint_id, explanation)` where `explanation`
    /// contains IDs of constraints involved in the domain wipeout.
    /// The newly created constraint remains in the engine and can be removed
    /// with [`Engine::retract_constraint`].
    pub fn new_neq(&mut self, var1: usize, var2: usize) -> Result<usize, (usize, Vec<usize>)> {
        let id = self.constraints.len();
        self.constraints.insert(id, (var1, var2, ConstraintKind::Inequality));
        self.propagate(id).map_err(|e| match e {
            PropagationError::DomainWipeout(var_id) => (id, self.get_conflict_explanation(var_id)),
        })?;
        Ok(id)
    }

    /// Adds a unary `set` constraint (`var == value`) and propagates it.
    ///
    /// On success, returns the newly assigned constraint ID.
    ///
    /// On failure, returns `(constraint_id, explanation)` where `explanation`
    /// contains IDs of constraints involved in the domain wipeout.
    /// The newly created constraint remains in the engine and can be removed
    /// with [`Engine::retract_constraint`].
    pub fn set(&mut self, var: usize, value: i32) -> Result<usize, (usize, Vec<usize>)> {
        let id = self.constraints.len();
        self.constraints.insert(id, (var, var, ConstraintKind::Set(value)));
        self.propagate(id).map_err(|e| match e {
            PropagationError::DomainWipeout(var_id) => (id, self.get_conflict_explanation(var_id)),
        })?;
        Ok(id)
    }

    /// Adds a unary `forbid` constraint (`var != value`) and propagates it.
    ///
    /// On success, returns the newly assigned constraint ID.
    ///
    /// On failure, returns `(constraint_id, explanation)` where `explanation`
    /// contains IDs of constraints involved in the domain wipeout.
    /// The newly created constraint remains in the engine and can be removed
    /// with [`Engine::retract_constraint`].
    pub fn forbid(&mut self, var: usize, value: i32) -> Result<usize, (usize, Vec<usize>)> {
        let id = self.constraints.len();
        self.constraints.insert(id, (var, var, ConstraintKind::Forbid(value)));
        self.propagate(id).map_err(|e| match e {
            PropagationError::DomainWipeout(var_id) => (id, self.get_conflict_explanation(var_id)),
        })?;
        Ok(id)
    }

    /// Retracts a constraint by ID and incrementally restores consistency.
    ///
    /// If the ID is present, the constraint is removed, values suppressed by
    /// that exact constraint are released, and only the affected neighborhood is
    /// re-propagated. If the ID does not exist, this method is a no-op.
    ///
    /// Panics if re-propagation unexpectedly causes a domain wipeout.
    pub fn retract_constraint(&mut self, id: usize) {
        if let Some((var1, var2, _)) = self.constraints.remove(&id) {
            // 1. Free only values that were killed *by this exact constraint*
            for &var in &[var1, var2] {
                if let Some(domain) = self.values.get_mut(var) {
                    for state in domain {
                        if state.suppressed_by == Some(id) {
                            state.suppressed_by = None;
                        }
                    }
                }
            }

            // 2. Re-propagate only the affected subgraph (true incremental)
            self.propagate_touching(&[var1, var2]).unwrap_or_else(|e| match e {
                PropagationError::DomainWipeout(var_id) => {
                    panic!("Unexpected domain wipeout during re-propagation after retracting constraint {}: variable {}", id, var_id)
                }
            });
        }
    }

    fn propagate(&mut self, start_id: usize) -> Result<(), PropagationError> {
        self.propagate_from_queue(vec![start_id])
    }

    fn propagate_touching(&mut self, vars: &[usize]) -> Result<(), PropagationError> {
        let mut initial = Vec::new();
        for &v in vars {
            for (&id, (v1, v2, _)) in &self.constraints {
                if *v1 == v || *v2 == v {
                    initial.push(id);
                }
            }
        }
        self.propagate_from_queue(initial)
    }

    fn propagate_from_queue(&mut self, initial: Vec<usize>) -> Result<(), PropagationError> {
        let mut prop_q: VecDeque<usize> = initial.into();
        let mut in_queue: HashSet<usize> = prop_q.iter().cloned().collect();

        while let Some(c) = prop_q.pop_front() {
            in_queue.remove(&c);

            let (var1, var2, kind) = *self.constraints.get(&c).unwrap();

            let changed_vars = match kind {
                ConstraintKind::Equality | ConstraintKind::Inequality => {
                    let mut any_changed = false;
                    loop {
                        let changed1 = self.revise_binary(var1, var2, kind, c)?;
                        let changed2 = self.revise_binary(var2, var1, kind, c)?;
                        if !(changed1 || changed2) {
                            break;
                        }
                        any_changed = true;
                    }

                    if any_changed { vec![var1, var2] } else { Vec::new() }
                }
                ConstraintKind::Set(_) | ConstraintKind::Forbid(_) => {
                    let changed = self.revise_unary(var1, kind, c)?;
                    if changed { vec![var1] } else { Vec::new() }
                }
            };

            if !changed_vars.is_empty() {
                // Enqueue all constraints that touch changed variables.
                for &v in &changed_vars {
                    for (&id, (v1, v2, _)) in &self.constraints {
                        if id != c && !in_queue.contains(&id) && (*v1 == v || *v2 == v) {
                            prop_q.push_back(id);
                            in_queue.insert(id);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn revise_binary(&mut self, var1: usize, var2: usize, kind: ConstraintKind, id: usize) -> Result<bool, PropagationError> {
        let mut changed = false;

        let domain_b: Vec<(i32, Option<usize>)> = self.values[var2].iter().map(|s| (s.value, s.suppressed_by)).collect();

        let domain_a = self.values.get_mut(var1).unwrap();
        for state_a in domain_a.iter_mut() {
            let has_support = match kind {
                // Values suppressed by this same constraint can be revived together,
                // so they count as provisional support during this revision.
                ConstraintKind::Equality => domain_b.iter().any(|(v_b, suppressed_by)| *v_b == state_a.value && (suppressed_by.is_none() || *suppressed_by == Some(id))),
                ConstraintKind::Inequality => domain_b.iter().any(|(v_b, suppressed_by)| *v_b != state_a.value && (suppressed_by.is_none() || *suppressed_by == Some(id))),
                ConstraintKind::Set(_) | ConstraintKind::Forbid(_) => unreachable!("Unary constraints are handled by revise_unary"),
            };

            if has_support {
                // This constraint no longer kills the value → possible revival
                if state_a.suppressed_by == Some(id) {
                    state_a.suppressed_by = None;
                    changed = true;
                }
            } else if state_a.suppressed_by.is_none() {
                // This constraint now kills the value
                state_a.suppressed_by = Some(id);
                changed = true;
            }
        }

        if !domain_a.iter().any(|s| s.suppressed_by.is_none()) {
            return Err(PropagationError::DomainWipeout(var1));
        }

        Ok(changed)
    }

    fn revise_unary(&mut self, var: usize, kind: ConstraintKind, id: usize) -> Result<bool, PropagationError> {
        let mut changed = false;

        let domain = self.values.get_mut(var).unwrap();
        for state in domain.iter_mut() {
            let has_support = match kind {
                ConstraintKind::Set(value) => state.value == value,
                ConstraintKind::Forbid(value) => state.value != value,
                ConstraintKind::Equality | ConstraintKind::Inequality => unreachable!("Binary constraints are handled by revise_binary"),
            };

            if has_support {
                // This constraint no longer kills the value -> possible revival.
                if state.suppressed_by == Some(id) {
                    state.suppressed_by = None;
                    changed = true;
                }
            } else if state.suppressed_by.is_none() {
                // This constraint now kills the value.
                state.suppressed_by = Some(id);
                changed = true;
            }
        }

        if !domain.iter().any(|s| s.suppressed_by.is_none()) {
            return Err(PropagationError::DomainWipeout(var));
        }

        Ok(changed)
    }

    fn get_conflict_explanation(&self, var_id: usize) -> Vec<usize> {
        self.values[var_id].iter().filter_map(|state| state.suppressed_by).collect::<HashSet<_>>().into_iter().collect()
    }

    pub fn set_listener<F>(&mut self, var: usize, callback: F)
    where
        F: Fn(&Engine, usize) + 'static,
    {
        self.listeners.entry(var).or_default().push(Box::new(callback));
    }
}

impl Display for Engine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (i, var_values) in self.values.iter().enumerate() {
            let var_values: Vec<String> = var_values.iter().filter(|v| v.suppressed_by.is_none()).map(|v| v.value.to_string()).collect();
            writeln!(f, "e{}: {{{}}}", i, var_values.join(", "))?;
        }
        for (_, (var1, var2, kind)) in &self.constraints {
            let kind_str = match kind {
                ConstraintKind::Equality => "==",
                ConstraintKind::Inequality => "!=",
                ConstraintKind::Set(_) => "set",
                ConstraintKind::Forbid(_) => "forbid",
            };
            match kind {
                ConstraintKind::Set(v) | ConstraintKind::Forbid(v) => {
                    writeln!(f, "e{} {} {}", var1, kind_str, v)?;
                }
                ConstraintKind::Equality | ConstraintKind::Inequality => {
                    writeln!(f, "e{} {} e{}", var1, kind_str, var2)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_equality() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);
        let b = ac.add_var(vec![2, 3, 4]);

        let _ = ac.new_eq(a, b);

        // Intersection should be {2, 3}
        assert_eq!(ac.val(a), vec![2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_transitive_equality() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2]);
        let b = ac.add_var(vec![2, 3]);
        let c = ac.add_var(vec![3, 4]);

        let _ = ac.new_eq(a, b); // a:{2}, b:{2}
        let _ = ac.new_eq(b, c); // b: empty, c: empty

        assert!(ac.val(a).is_empty() || ac.val(b).is_empty() || ac.val(c).is_empty());
    }

    #[test]
    fn test_inequality_singleton_pruning() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1]);
        let b = ac.add_var(vec![1, 2, 3]);

        let _ = ac.new_neq(a, b);

        // Since a is {1}, b cannot be 1.
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_basic_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2]);
        let b = ac.add_var(vec![3, 4]);

        let c_id = ac.new_eq(a, b);
        assert!(ac.val(a).is_empty() || ac.val(b).is_empty());
        assert!(c_id.as_ref().expect_err("Expected a conflict due to no overlap between a and b").1.contains(&0), "Conflict explanation should include the failed constraint ID");
        // The conflict should be explained by the failed constraint itself

        ac.retract_constraint(c_id.err().unwrap().0);
        // After retraction, domains should return to original state
        assert_eq!(ac.val(a), vec![1, 2]);
        assert_eq!(ac.val(b), vec![3, 4]);
    }

    #[test]
    fn test_multiple_suppression_logic() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);
        let b = ac.add_var(vec![1]);
        let c = ac.add_var(vec![1]);

        // Constraint 0: a != b  => a: {2, 3}
        let id0 = ac.new_neq(a, b);
        // Constraint 1: a != c  => a: {2, 3}
        let id1 = ac.new_neq(a, c);

        assert_eq!(ac.val(a), vec![2, 3]);

        // Retract first inequality
        ac.retract_constraint(id0.unwrap());

        // CRITICAL: Value '1' in 'a' was suppressed by id0.
        // Even after retracting id0, '1' should stay suppressed because id1 (a != c) still forbids it.
        assert_eq!(ac.val(a), vec![2, 3], "Value 1 should still be suppressed by the other inequality");

        ac.retract_constraint(id1.unwrap());
        assert_eq!(ac.val(a), vec![1, 2, 3], "All values should be restored now");
    }

    #[test]
    fn test_diamond_chain_propagation() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);
        let b = ac.add_var(vec![2, 3, 4]);
        let c = ac.add_var(vec![2, 3, 4]);
        let d = ac.add_var(vec![3, 4, 5]);

        // Setup chain: a == b, b == d, a == c, c == d
        let _ = ac.new_eq(a, b); // a,b: {2,3}
        let _ = ac.new_eq(b, d); // a,b,d: {3}
        let _ = ac.new_eq(a, c); // c: {3}
        let _ = ac.new_eq(c, d);

        assert_eq!(ac.val(a), vec![3]);
        assert_eq!(ac.val(d), vec![3]);
    }

    #[test]
    fn test_inequality_chain_reaction() {
        let mut ac = Engine::new();
        // A chain where narrowing one forces another via inequalities
        let a = ac.add_var(vec![1]);
        let b = ac.add_var(vec![1, 2]);
        let c = ac.add_var(vec![2, 3]);

        let _ = ac.new_neq(a, b); // forces b to {2}
        let _ = ac.new_neq(b, c); // forces c to {3}

        assert_eq!(ac.val(b), vec![2]);
        assert_eq!(ac.val(c), vec![3]);
    }

    #[test]
    fn test_set_constraint_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);

        let set_id = ac.set(a, 2).expect("set should succeed");
        assert_eq!(ac.val(a), vec![2]);

        ac.retract_constraint(set_id);
        assert_eq!(ac.val(a), vec![1, 2, 3]);
    }

    #[test]
    fn test_forbid_constraint_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);

        let forbid_id = ac.forbid(a, 2).expect("forbid should succeed");
        assert_eq!(ac.val(a), vec![1, 3]);

        ac.retract_constraint(forbid_id);
        assert_eq!(ac.val(a), vec![1, 2, 3]);
    }

    #[test]
    fn test_set_with_binary_interaction_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2, 3]);
        let b = ac.add_var(vec![2, 3]);

        let eq_id = ac.new_eq(a, b).expect("equality should succeed");
        let set_id = ac.set(a, 2).expect("set should succeed");

        // set(a,2) should propagate through equality to b
        assert_eq!(ac.val(a), vec![2]);
        assert_eq!(ac.val(b), vec![2]);

        // Retracting only set should keep binary propagation active.
        ac.retract_constraint(set_id);
        assert_eq!(ac.val(a), vec![2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);

        ac.retract_constraint(eq_id);
        assert_eq!(ac.val(a), vec![1, 2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);
    }
}
