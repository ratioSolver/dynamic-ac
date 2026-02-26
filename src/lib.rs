use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::{Display, Formatter, Result},
};

type Callback = Box<dyn Fn(&Engine, usize)>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    Equality,
    Inequality,
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
    pub fn new() -> Self {
        Self { values: Vec::new(), constraints: HashMap::new(), listeners: HashMap::new() }
    }

    pub fn add_var(&mut self, values: Vec<i32>) -> usize {
        let id = self.values.len();
        self.values.push(values.into_iter().map(|v| ValueState { value: v, suppressed_by: None }).collect());
        id
    }

    pub fn val(&self, var: usize) -> Vec<i32> {
        self.values[var].iter().filter(|s| s.suppressed_by.is_none()).map(|s| s.value).collect()
    }

    pub fn new_eq(&mut self, var1: usize, var2: usize) -> usize {
        let id = self.constraints.len();
        self.constraints.insert(id, (var1, var2, ConstraintKind::Equality));
        self.propagate(id);
        id
    }

    pub fn new_neq(&mut self, var1: usize, var2: usize) -> usize {
        let id = self.constraints.len();
        self.constraints.insert(id, (var1, var2, ConstraintKind::Inequality));
        self.propagate(id);
        id
    }

    pub fn retract_constraint(&mut self, id: usize) {
        if let Some((a, b, _)) = self.constraints.remove(&id) {
            let mut to_check = VecDeque::new();

            // 1. Find all values killed by this specific constraint and free them
            for var in &[a, b] {
                if let Some(domain) = self.values.get_mut(*var) {
                    for state in domain {
                        if state.suppressed_by == Some(id) {
                            state.suppressed_by = None;
                            to_check.push_back(var.clone());
                        }
                    }
                }
            }

            // 2. Re-propagate because the "resurrected" values might now satisfy other constraints that were previously pruning values.
            self.propagate_all();
        }
    }

    fn propagate(&mut self, constraint: usize) {
        let mut prop_q = VecDeque::new();
        let mut in_queue = HashSet::new();
        prop_q.push_back(constraint);
        in_queue.insert(constraint);

        while let Some(c) = prop_q.pop_front() {
            in_queue.remove(&c);

            let (var1, var2, kind) = self.constraints.get(&c).unwrap().clone();
            let changed1 = self.revise(var1, var2, kind, c);
            let changed2 = self.revise(var2, var1, kind, c);

            if changed1 || changed2 {
                for (&id, (v1, v2, _)) in &self.constraints {
                    if id != c && !in_queue.contains(&id) {
                        if *v1 == var1 || *v2 == var1 || *v1 == var2 || *v2 == var2 {
                            prop_q.push_back(id);
                            in_queue.insert(id);
                        }
                    }
                }
            }
        }
    }

    fn propagate_all(&mut self) {
        let keys: Vec<usize> = self.constraints.keys().cloned().collect();
        for id in keys {
            self.propagate(id);
        }
    }

    fn revise(&mut self, var1: usize, var2: usize, kind: ConstraintKind, id: usize) -> bool {
        let mut changed = false;

        let active_b: Vec<i32> = self.values[var2].iter().filter(|s| s.suppressed_by.is_none()).map(|s| s.value).collect();

        let domain_a = self.values.get_mut(var1).unwrap();
        for state_a in domain_a {
            if state_a.suppressed_by.is_none() {
                let has_support = match kind {
                    ConstraintKind::Equality => active_b.contains(&state_a.value),
                    ConstraintKind::Inequality => active_b.iter().any(|&v_b| v_b != state_a.value),
                };

                if !has_support {
                    state_a.suppressed_by = Some(id);
                    changed = true;
                }
            }
        }
        changed
    }

    pub fn set_listener<F>(&mut self, var: usize, callback: F)
    where
        F: Fn(&Engine, usize) + 'static,
    {
        self.listeners.entry(var).or_default().push(Box::new(callback));
    }
}

impl Display for Engine {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for (i, var_values) in self.values.iter().enumerate() {
            let var_values: Vec<String> = var_values.iter().filter(|v| v.suppressed_by.is_none()).map(|v| v.value.to_string()).collect();
            writeln!(f, "e{}: {{{}}}", i, var_values.join(", "))?;
        }
        for (_, (var1, var2, kind)) in &self.constraints {
            let kind_str = match kind {
                ConstraintKind::Equality => "==",
                ConstraintKind::Inequality => "!=",
            };
            writeln!(f, "e{} {} e{}", var1, kind_str, var2)?;
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

        ac.new_eq(a, b);

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

        ac.new_eq(a, b); // a:{2}, b:{2}
        ac.new_eq(b, c); // b: empty, c: empty

        assert!(ac.val(a).is_empty());
        assert!(ac.val(b).is_empty());
        assert!(ac.val(c).is_empty());
    }

    #[test]
    fn test_inequality_singleton_pruning() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1]);
        let b = ac.add_var(vec![1, 2, 3]);

        ac.new_neq(a, b);

        // Since a is {1}, b cannot be 1.
        assert_eq!(ac.val(b), vec![2, 3]);
    }

    #[test]
    fn test_basic_retraction() {
        let mut ac = Engine::new();
        let a = ac.add_var(vec![1, 2]);
        let b = ac.add_var(vec![3, 4]);

        let c_id = ac.new_eq(a, b);
        assert!(ac.val(a).is_empty());

        ac.retract_constraint(c_id);
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
        ac.retract_constraint(id0);

        // CRITICAL: Value '1' in 'a' was suppressed by id0.
        // Even after retracting id0, '1' should stay suppressed because id1 (a != c) still forbids it.
        assert_eq!(ac.val(a), vec![2, 3], "Value 1 should still be suppressed by the other inequality");

        ac.retract_constraint(id1);
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
        ac.new_eq(a, b); // a,b: {2,3}
        ac.new_eq(b, d); // a,b,d: {3}
        ac.new_eq(a, c); // c: {3}
        ac.new_eq(c, d);

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

        ac.new_neq(a, b); // forces b to {2}
        ac.new_neq(b, c); // forces c to {3}

        assert_eq!(ac.val(b), vec![2]);
        assert_eq!(ac.val(c), vec![3]);
    }
}
