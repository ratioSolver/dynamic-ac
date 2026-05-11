use std::{
    collections::{HashMap, VecDeque},
    fmt,
};

struct Value {
    value: i32,
    suppressed_by: Option<usize>,        // The constraint that suppresses this value, if any.
    supported_by: HashMap<usize, usize>, // Maps supporting variables to the value index in their domain.
}

struct Variable {
    id: usize,
    domain: Vec<Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

// A directional arc (constraint_id, from, to) means:
// "revise the domain of `from` using the domain of `to` via this constraint".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Arc {
    constraint_id: usize,
    from: usize,
    to: usize,
}

pub struct Engine {
    variables: Vec<Variable>,
    constraints: Vec<(bool, Constraint)>,
    propagation_queue: VecDeque<Arc>,
}

impl Engine {
    pub fn new() -> Self {
        Engine { variables: Vec::new(), constraints: Vec::new(), propagation_queue: VecDeque::new() }
    }

    pub fn add_variable(&mut self, domain: impl IntoIterator<Item = i32>) -> usize {
        let var_id = self.variables.len();
        let variable = Variable {
            id: var_id,
            domain: domain.into_iter().map(|value| Value { value, suppressed_by: None, supported_by: HashMap::new() }).collect(),
        };
        self.variables.push(variable);
        var_id
    }

    pub fn add_constraint(&mut self, constraint: Constraint) -> usize {
        let constraint_id = self.constraints.len();
        self.constraints.push((false, constraint));
        constraint_id
    }

    pub fn val(&self, var_id: usize) -> Vec<i32> {
        self.variables[var_id].domain.iter().filter_map(|v| if v.suppressed_by.is_none() { Some(v.value) } else { None }).collect()
    }

    pub fn assert_constraint(&mut self, constraint_id: usize) {
        let (is_active, constraint) = self.constraints.get_mut(constraint_id).unwrap_or_else(|| panic!("invalid constraint id: {}", constraint_id));

        if !*is_active {
            *is_active = true;
            let arcs: &[(usize, usize)] = match constraint {
                Constraint::Equality(a, b) | Constraint::Inequality(a, b) => &[(*a, *b), (*b, *a)],
                Constraint::Set(a, _) | Constraint::Forbid(a, _) => &[(*a, *a)],
            };
            for &(from, to) in arcs {
                let arc = Arc { constraint_id, from, to };
                if !self.propagation_queue.contains(&arc) {
                    self.propagation_queue.push_back(arc);
                }
            }
        }
    }

    pub fn retract_constraint(&mut self, constraint_id: usize) {
        let (is_active, _) = self.constraints.get_mut(constraint_id).unwrap_or_else(|| panic!("invalid constraint id: {}", constraint_id));

        if *is_active {
            *is_active = false;
            self.propagation_queue.retain(|arc| arc.constraint_id != constraint_id);
        }
    }
}
