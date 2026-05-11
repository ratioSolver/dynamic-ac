use std::{collections::HashMap, fmt};

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
            Constraint::Equality(var1, var2) => write!(f, "{} == {}", var1, var2),
            Constraint::Inequality(var1, var2) => write!(f, "{} != {}", var1, var2),
            Constraint::Set(var, value) => write!(f, "{} == {}", var, value),
            Constraint::Forbid(var, value) => write!(f, "{} != {}", var, value),
        }
    }
}

pub struct Engine {
    variables: Vec<Variable>,
    constraints: Vec<Constraint>,
}

impl Engine {
    pub fn new() -> Self {
        Engine { variables: Vec::new(), constraints: Vec::new() }
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
        self.constraints.push(constraint);
        constraint_id
    }
}
