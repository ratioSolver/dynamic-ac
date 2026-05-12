use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

#[derive(Debug, Clone)]
pub enum Constraint {
    Equality(usize, usize),   // Represents an equality constraint between two variables (e.g., x_i == x_j).
    Inequality(usize, usize), // Represents an inequality constraint between two variables (e.g., x_i != x_j).
    Set(usize, i32),          // Represents a constraint that a variable must take a specific value (e.g., x_i == 5).
    Forbid(usize, i32),       // Represents a constraint that a variable cannot take a specific value (e.g., x_i != 5).
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(var1, var2) => write!(f, "e{} == e{}", var1, var2),
            Constraint::Inequality(var1, var2) => write!(f, "e{} != e{}", var1, var2),
            Constraint::Set(var, value) => write!(f, "e{} == {}", var, value),
            Constraint::Forbid(var, value) => write!(f, "e{} != {}", var, value),
        }
    }
}

#[derive(Debug, Clone)]
struct ValueState {
    value: i32,
    killers: HashSet<usize>,
}

#[derive(Debug, Clone)]
struct Variable {
    domain: Vec<ValueState>,
    index_by_value: HashMap<i32, usize>,
}

#[derive(Debug, Clone)]
struct ConstraintEntry {
    active: bool,
    kind: Constraint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropagationError {
    InvalidConstraintId(usize),
    DomainWipeout { var: usize, explanation: Vec<usize> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Arc {
    constraint_id: usize,
    from: usize,
    to: usize,
}

pub struct Engine {
    variables: Vec<Variable>,
    constraints: Vec<ConstraintEntry>,
    // Key: (constraint_id, from_var, to_var, from_value) -> supporting to_value.
    residues: HashMap<(usize, usize, usize, i32), i32>,
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    pub fn new() -> Self {
        Self { variables: Vec::new(), constraints: Vec::new(), residues: HashMap::new() }
    }

    pub fn add_variable(&mut self, domain: impl IntoIterator<Item = i32>) -> usize {
        let mut unique = Vec::new();
        let mut seen = HashSet::new();

        for value in domain {
            if seen.insert(value) {
                unique.push(value);
            }
        }

        let mut index_by_value = HashMap::with_capacity(unique.len());
        let mut states = Vec::with_capacity(unique.len());

        for (idx, value) in unique.into_iter().enumerate() {
            index_by_value.insert(value, idx);
            states.push(ValueState { value, killers: HashSet::new() });
        }

        let id = self.variables.len();
        self.variables.push(Variable { domain: states, index_by_value });
        id
    }

    pub fn val(&self, var_id: usize) -> Vec<i32> {
        self.variables[var_id].domain.iter().filter_map(|state| if state.killers.is_empty() { Some(state.value) } else { None }).collect()
    }

    pub fn add_constraint(&mut self, constraint: Constraint) -> usize {
        let id = self.constraints.len();
        self.constraints.push(ConstraintEntry { active: false, kind: constraint });
        id
    }

    pub fn assert(&mut self, constraint_id: usize) -> Result<(), PropagationError> {
        let touched = self.constraint_vars(constraint_id)?;
        if self.constraints[constraint_id].active {
            return Ok(());
        }

        self.constraints[constraint_id].active = true;
        self.propagate_from_vars(&touched)
    }

    pub fn retract(&mut self, constraint_id: usize) -> Result<(), PropagationError> {
        let touched = self.constraint_vars(constraint_id)?;
        if !self.constraints[constraint_id].active {
            return Ok(());
        }

        self.constraints[constraint_id].active = false;

        for &var in &touched {
            for state in &mut self.variables[var].domain {
                state.killers.remove(&constraint_id);
            }
        }

        self.residues.retain(|(cid, _, _, _), _| *cid != constraint_id);
        self.propagate_from_vars(&touched)
    }

    pub fn new_eq(&mut self, a: usize, b: usize) -> Result<usize, PropagationError> {
        let id = self.add_constraint(Constraint::Equality(a, b));
        self.assert(id)?;
        Ok(id)
    }

    pub fn new_neq(&mut self, a: usize, b: usize) -> Result<usize, PropagationError> {
        let id = self.add_constraint(Constraint::Inequality(a, b));
        self.assert(id)?;
        Ok(id)
    }

    pub fn set(&mut self, var: usize, value: i32) -> Result<usize, PropagationError> {
        let id = self.add_constraint(Constraint::Set(var, value));
        self.assert(id)?;
        Ok(id)
    }

    pub fn forbid(&mut self, var: usize, value: i32) -> Result<usize, PropagationError> {
        let id = self.add_constraint(Constraint::Forbid(var, value));
        self.assert(id)?;
        Ok(id)
    }

    pub fn assert_batch(&mut self, constraint_ids: &[usize]) -> Result<(), PropagationError> {
        let mut all_touched = HashSet::new();

        for &id in constraint_ids {
            let touched = self.constraint_vars(id)?;
            if !self.constraints[id].active {
                self.constraints[id].active = true;
                all_touched.extend(touched);
            }
        }

        self.propagate_from_vars(&all_touched.into_iter().collect::<Vec<_>>())
    }

    pub fn retract_batch(&mut self, constraint_ids: &[usize]) -> Result<(), PropagationError> {
        let mut all_touched = HashSet::new();

        for &id in constraint_ids {
            let touched = self.constraint_vars(id)?;
            if self.constraints[id].active {
                self.constraints[id].active = false;

                for &var in &touched {
                    for state in &mut self.variables[var].domain {
                        state.killers.remove(&id);
                    }
                }

                all_touched.extend(touched);
            }
        }

        self.residues.retain(|(cid, _, _, _), _| !constraint_ids.contains(cid));
        self.propagate_from_vars(&all_touched.into_iter().collect::<Vec<_>>())
    }

    fn constraint_vars(&self, constraint_id: usize) -> Result<Vec<usize>, PropagationError> {
        let Some(entry) = self.constraints.get(constraint_id) else {
            return Err(PropagationError::InvalidConstraintId(constraint_id));
        };

        let vars = match entry.kind {
            Constraint::Equality(a, b) | Constraint::Inequality(a, b) => {
                if a == b {
                    vec![a]
                } else {
                    vec![a, b]
                }
            }
            Constraint::Set(var, _) | Constraint::Forbid(var, _) => vec![var],
        };

        Ok(vars)
    }

    fn arcs_of(&self, constraint_id: usize) -> Vec<Arc> {
        match self.constraints[constraint_id].kind {
            Constraint::Equality(a, b) | Constraint::Inequality(a, b) => {
                if a == b {
                    vec![Arc { constraint_id, from: a, to: b }]
                } else {
                    vec![Arc { constraint_id, from: a, to: b }, Arc { constraint_id, from: b, to: a }]
                }
            }
            Constraint::Set(var, _) | Constraint::Forbid(var, _) => {
                vec![Arc { constraint_id, from: var, to: var }]
            }
        }
    }

    fn touching_constraints(&self, var: usize) -> Vec<usize> {
        self.constraints
            .iter()
            .enumerate()
            .filter_map(|(id, entry)| {
                if !entry.active {
                    return None;
                }

                let touches = match entry.kind {
                    Constraint::Equality(a, b) | Constraint::Inequality(a, b) => a == var || b == var,
                    Constraint::Set(v, _) | Constraint::Forbid(v, _) => v == var,
                };

                if touches { Some(id) } else { None }
            })
            .collect()
    }

    fn propagate_from_vars(&mut self, vars: &[usize]) -> Result<(), PropagationError> {
        let mut queue = VecDeque::new();
        let mut in_queue = HashSet::new();

        for &var in vars {
            for cid in self.touching_constraints(var) {
                for arc in self.arcs_of(cid) {
                    if in_queue.insert(arc) {
                        queue.push_back(arc);
                    }
                }
            }
        }

        while let Some(arc) = queue.pop_front() {
            in_queue.remove(&arc);

            if !self.constraints[arc.constraint_id].active {
                continue;
            }

            let changed = self.revise(arc)?;
            if changed {
                // Re-queue only incoming arcs: Y_i -> X_j where X_j = arc.from
                for cid in self.touching_constraints(arc.from) {
                    for next_arc in self.arcs_of(cid) {
                        if next_arc.to == arc.from && next_arc != arc {
                            if in_queue.insert(next_arc) {
                                queue.push_back(next_arc);
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn revise(&mut self, arc: Arc) -> Result<bool, PropagationError> {
        match self.constraints[arc.constraint_id].kind {
            Constraint::Set(_, expected) => self.revise_unary(arc.constraint_id, arc.from, |a| a == expected),
            Constraint::Forbid(_, forbidden) => self.revise_unary(arc.constraint_id, arc.from, |a| a != forbidden),
            Constraint::Equality(_, _) => self.revise_binary(arc.constraint_id, arc.from, arc.to, |a, b| a == b),
            Constraint::Inequality(_, _) => self.revise_binary(arc.constraint_id, arc.from, arc.to, |a, b| a != b),
        }
    }

    fn revise_unary<F>(&mut self, cid: usize, var: usize, predicate: F) -> Result<bool, PropagationError>
    where
        F: Fn(i32) -> bool,
    {
        let mut changed = false;

        for state in &mut self.variables[var].domain {
            let was_active = state.killers.is_empty();
            if predicate(state.value) {
                state.killers.remove(&cid);
            } else {
                state.killers.insert(cid);
            }

            let is_active = state.killers.is_empty();
            if was_active != is_active {
                changed = true;
            }
        }

        if !self.has_active_value(var) {
            return Err(self.wipeout(var));
        }

        Ok(changed)
    }

    fn revise_binary<F>(&mut self, cid: usize, from: usize, to: usize, relation: F) -> Result<bool, PropagationError>
    where
        F: Fn(i32, i32) -> bool,
    {
        let mut changed = false;

        let from_values: Vec<i32> = self.variables[from].domain.iter().map(|s| s.value).collect();

        for a in from_values {
            let has_support = self.has_support(cid, from, to, a, &relation);
            let idx = self.variables[from].index_by_value[&a];
            let state = &mut self.variables[from].domain[idx];
            let was_active = state.killers.is_empty();

            if has_support {
                state.killers.remove(&cid);
            } else {
                state.killers.insert(cid);
            }

            let is_active = state.killers.is_empty();
            if was_active != is_active {
                changed = true;
            }
        }

        if !self.has_active_value(from) {
            return Err(self.wipeout(from));
        }

        Ok(changed)
    }

    fn has_support<F>(&mut self, cid: usize, from: usize, to: usize, a: i32, relation: &F) -> bool
    where
        F: Fn(i32, i32) -> bool,
    {
        let residue_key = (cid, from, to, a);

        if let Some(&b) = self.residues.get(&residue_key)
            && self.is_active_value(to, b)
            && relation(a, b)
        {
            return true;
        }

        for state in &self.variables[to].domain {
            if !state.killers.is_empty() {
                continue;
            }
            if relation(a, state.value) {
                self.residues.insert(residue_key, state.value);
                return true;
            }
        }

        self.residues.remove(&residue_key);
        false
    }

    fn is_active_value(&self, var: usize, value: i32) -> bool {
        let Some(&idx) = self.variables[var].index_by_value.get(&value) else {
            return false;
        };
        self.variables[var].domain[idx].killers.is_empty()
    }

    fn has_active_value(&self, var: usize) -> bool {
        self.variables[var].domain.iter().any(|s| s.killers.is_empty())
    }

    fn wipeout(&self, var: usize) -> PropagationError {
        let mut explanation = HashSet::new();
        for state in &self.variables[var].domain {
            for &cid in &state.killers {
                explanation.insert(cid);
            }
        }

        PropagationError::DomainWipeout { var, explanation: explanation.into_iter().collect() }
    }
}

impl fmt::Display for Engine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Variables:")?;
        for (i, var) in self.variables.iter().enumerate() {
            let values: Vec<String> = var.domain.iter().map(|s| if s.killers.is_empty() { s.value.to_string() } else { format!("{} (killed by {:?})", s.value, s.killers) }).collect();
            writeln!(f, "  e{}: {}", i, values.join(", "))?;
        }

        writeln!(f, "Constraints:")?;
        for (i, entry) in self.constraints.iter().enumerate() {
            writeln!(f, "  c{}: {} [{}]", i, entry.kind, if entry.active { "active" } else { "inactive" })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dynamic_unary_retract_and_readd() {
        let mut ac = Engine::new();
        let x = ac.add_variable([1, 2, 3]);

        let c = ac.add_constraint(Constraint::Forbid(x, 2));
        ac.assert(c).expect("forbid must propagate");
        assert_eq!(ac.val(x), vec![1, 3]);

        ac.retract(c).expect("retraction must succeed");
        assert_eq!(ac.val(x), vec![1, 2, 3]);

        ac.assert(c).expect("re-assert must propagate");
        assert_eq!(ac.val(x), vec![1, 3]);
    }

    #[test]
    fn dynamic_binary_retract_and_readd() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([2, 3, 4]);

        let eq = ac.add_constraint(Constraint::Equality(a, b));
        ac.assert(eq).expect("equality must propagate");
        assert_eq!(ac.val(a), vec![2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);

        ac.retract(eq).expect("retraction must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3]);
        assert_eq!(ac.val(b), vec![2, 3, 4]);

        ac.assert(eq).expect("re-assert must propagate");
        assert_eq!(ac.val(a), vec![2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn mixed_constraints_and_selective_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([1, 2, 3]);

        let eq = ac.new_eq(a, b).expect("eq must succeed");
        let set = ac.set(a, 2).expect("set must succeed");
        assert_eq!(ac.val(a), vec![2]);
        assert_eq!(ac.val(b), vec![2]);

        ac.retract(set).expect("retract set must succeed");
        assert_eq!(ac.val(a), vec![2]);
        assert_eq!(ac.val(b), vec![2]);

        ac.retract(eq).expect("retract eq must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3]);
        assert_eq!(ac.val(b), vec![1, 2, 3]);
    }

    #[test]
    fn test_basic_equality() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([2, 3, 4]);

        ac.new_eq(a, b).expect("equality must succeed");

        // Intersection should be {2, 3}
        assert_eq!(ac.val(a), vec![2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_inequality_singleton_pruning() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1]);
        let b = ac.add_variable([1, 2, 3]);

        ac.new_neq(a, b).expect("inequality must succeed");

        // Since a is {1}, b cannot be 1.
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_multiple_suppression_logic() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([1]);
        let c = ac.add_variable([1]);

        // Constraint 0: a != b  => a: {2, 3}
        let id0 = ac.new_neq(a, b).expect("first neq must succeed");
        // Constraint 1: a != c  => a: {2, 3}
        let id1 = ac.new_neq(a, c).expect("second neq must succeed");

        assert_eq!(ac.val(a), vec![2, 3]);

        // Retract first inequality
        ac.retract(id0).expect("retract must succeed");

        // CRITICAL: Value '1' in 'a' was suppressed by id0.
        // Even after retracting id0, '1' should stay suppressed because id1 (a != c) still forbids it.
        assert_eq!(ac.val(a), vec![2, 3], "Value 1 should still be suppressed by the other inequality");

        ac.retract(id1).expect("retract must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3], "All values should be restored now");
    }

    #[test]
    fn test_diamond_chain_propagation() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([2, 3, 4]);
        let c = ac.add_variable([2, 3, 4]);
        let d = ac.add_variable([3, 4, 5]);

        // Setup chain: a == b, b == d, a == c, c == d
        ac.new_eq(a, b).expect("a==b");
        ac.new_eq(b, d).expect("b==d");
        ac.new_eq(a, c).expect("a==c");
        ac.new_eq(c, d).expect("c==d");

        assert_eq!(ac.val(a), vec![3]);
        assert_eq!(ac.val(d), vec![3]);
    }

    #[test]
    fn test_inequality_chain_reaction() {
        let mut ac = Engine::new();
        // A chain where narrowing one forces another via inequalities
        let a = ac.add_variable([1]);
        let b = ac.add_variable([1, 2]);
        let c = ac.add_variable([2, 3]);

        ac.new_neq(a, b).expect("a!=b"); // forces b to {2}
        ac.new_neq(b, c).expect("b!=c"); // forces c to {3}

        assert_eq!(ac.val(b), vec![2]);
        assert_eq!(ac.val(c), vec![3]);
    }

    #[test]
    fn test_set_constraint_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);

        let set_id = ac.set(a, 2).expect("set must succeed");
        assert_eq!(ac.val(a), vec![2]);

        ac.retract(set_id).expect("retract must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3]);
    }

    #[test]
    fn test_forbid_constraint_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);

        let forbid_id = ac.forbid(a, 2).expect("forbid must succeed");
        assert_eq!(ac.val(a), vec![1, 3]);

        ac.retract(forbid_id).expect("retract must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3]);
    }

    #[test]
    fn test_set_with_binary_interaction_and_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_variable([1, 2, 3]);
        let b = ac.add_variable([2, 3]);

        let eq_id = ac.new_eq(a, b).expect("equality must succeed");
        let set_id = ac.set(a, 2).expect("set must succeed");

        // set(a,2) should propagate through equality to b
        assert_eq!(ac.val(a), vec![2]);
        assert_eq!(ac.val(b), vec![2]);

        // Retracting only set should keep binary propagation active.
        // Since eq(a, b) is still active and b is {2}, a remains {2}.
        ac.retract(set_id).expect("retract set must succeed");
        assert_eq!(ac.val(a), vec![2]);
        assert_eq!(ac.val(b), vec![2]);

        ac.retract(eq_id).expect("retract eq must succeed");
        assert_eq!(ac.val(a), vec![1, 2, 3]);
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_assert_batch_equivalence() {
        // assert_batch should produce same results as sequential assert calls
        let mut ac1 = Engine::new();
        let a1 = ac1.add_variable([1, 2, 3]);
        let b1 = ac1.add_variable([2, 3, 4]);
        let c1 = ac1.add_variable([3, 4, 5]);

        let id0 = ac1.add_constraint(Constraint::Equality(a1, b1));
        let id1 = ac1.add_constraint(Constraint::Equality(b1, c1));
        let id2 = ac1.add_constraint(Constraint::Set(a1, 3));

        ac1.assert_batch(&[id0, id1, id2]).expect("batch assert must succeed");

        // Separate sequential calls
        let mut ac2 = Engine::new();
        let a2 = ac2.add_variable([1, 2, 3]);
        let b2 = ac2.add_variable([2, 3, 4]);
        let c2 = ac2.add_variable([3, 4, 5]);

        let id0 = ac2.add_constraint(Constraint::Equality(a2, b2));
        let id1 = ac2.add_constraint(Constraint::Equality(b2, c2));
        let id2 = ac2.add_constraint(Constraint::Set(a2, 3));

        ac2.assert(id0).expect("assert 0");
        ac2.assert(id1).expect("assert 1");
        ac2.assert(id2).expect("assert 2");

        // Results must match
        assert_eq!(ac1.val(a1), ac2.val(a2));
        assert_eq!(ac1.val(b1), ac2.val(b2));
        assert_eq!(ac1.val(c1), ac2.val(c2));
    }

    #[test]
    fn test_retract_batch_equivalence() {
        // Create two identical engines with constraints
        let mut ac1 = Engine::new();
        let a1 = ac1.add_variable([1, 2, 3]);
        let b1 = ac1.add_variable([1, 2, 3]);
        let c1 = ac1.add_variable([1, 2, 3]);

        let id0 = ac1.new_eq(a1, b1).expect("eq 0");
        let id1 = ac1.new_neq(b1, c1).expect("neq 1");
        let id2 = ac1.set(a1, 2).expect("set 2");

        let mut ac2 = Engine::new();
        let a2 = ac2.add_variable([1, 2, 3]);
        let b2 = ac2.add_variable([1, 2, 3]);
        let c2 = ac2.add_variable([1, 2, 3]);

        let id0_2 = ac2.new_eq(a2, b2).expect("eq 0");
        let id1_2 = ac2.new_neq(b2, c2).expect("neq 1");
        let id2_2 = ac2.set(a2, 2).expect("set 2");

        // Batch retract
        ac1.retract_batch(&[id0, id1, id2]).expect("batch retract");

        // Sequential retract
        ac2.retract(id0_2).expect("retract 0");
        ac2.retract(id1_2).expect("retract 1");
        ac2.retract(id2_2).expect("retract 2");

        // Results must match
        assert_eq!(ac1.val(a1), ac2.val(a2));
        assert_eq!(ac1.val(b1), ac2.val(b2));
        assert_eq!(ac1.val(c1), ac2.val(c2));
    }
}
