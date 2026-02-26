use std::{
    collections::{HashMap, VecDeque},
    fmt::{Display, Formatter, Result},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    Equality,
    Inequality,
}

struct ValueState {
    value: i32,
    suppressed_by: Option<usize>,
}

pub struct DynamicAC {
    values: Vec<Vec<ValueState>>,
    constraints: HashMap<usize, (usize, usize, ConstraintKind)>,
}

impl DynamicAC {
    pub fn new() -> Self {
        Self { values: Vec::new(), constraints: HashMap::new() }
    }

    pub fn add_var(&mut self, values: Vec<i32>) -> usize {
        let id = self.values.len();
        self.values.push(values.into_iter().map(|v| ValueState { value: v, suppressed_by: None }).collect());
        id
    }

    pub fn val(&self, var: usize) -> Vec<i32> {
        self.values[var].iter().filter(|s| s.suppressed_by.is_none()).map(|s| s.value).collect()
    }

    pub fn add_constraint(&mut self, var1: usize, var2: usize, kind: ConstraintKind) -> usize {
        let id = self.constraints.len();
        self.constraints.insert(id, (var1, var2, kind));
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
        prop_q.push_back(constraint);

        while let Some(c) = prop_q.pop_front() {
            let (var1, var2, kind) = self.constraints.get(&c).unwrap().clone();
            let changed1 = self.revise(var1, var2, kind, c);
            let changed2 = self.revise(var2, var1, kind, c);

            if changed1 || changed2 {
                for (&id, (v1, v2, _)) in &self.constraints {
                    if *v1 == var1 || *v2 == var1 || *v1 == var2 || *v2 == var2 {
                        prop_q.push_back(id);
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

    fn revise(&mut self, var1: usize, var2: usize, kind: ConstraintKind, cid: usize) -> bool {
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
                    state_a.suppressed_by = Some(cid);
                    changed = true;
                }
            }
        }
        changed
    }
}

impl Display for DynamicAC {
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
