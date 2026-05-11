use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

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
            Constraint::Equality(i, j) => write!(f, "x{} == x{}", i, j),
            Constraint::Inequality(i, j) => write!(f, "x{} != x{}", i, j),
            Constraint::Set(i, value) => write!(f, "x{} == {}", i, value),
            Constraint::Forbid(i, value) => write!(f, "x{} != {}", i, value),
        }
    }
}

pub struct Engine {
    vars: Vec<HashMap<i32, Option<usize>>>, // Maps variable indices to their possible values and the constraints that suppress them.
    constraints: Vec<(bool, Constraint)>,   // Stores the constraints added to the engine, along with a flag indicating if they are active.
    prop_q: VecDeque<usize>,                // Queue for propagating constraints when they are asserted or retracted.
    in_queue: HashSet<usize>,               // Set to track which constraints are currently in the propagation queue to avoid duplicates.
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    pub fn new() -> Self {
        Engine {
            vars: Vec::new(),
            constraints: Vec::new(),
            prop_q: VecDeque::new(),
            in_queue: HashSet::new(),
        }
    }

    pub fn add_var(&mut self, values: &[i32]) -> usize {
        let var_index = self.vars.len();
        let mut value_map = HashMap::new();
        for value in values {
            value_map.insert(*value, None); // Initially, no constraints suppress any values.
        }
        self.vars.push(value_map);
        var_index
    }

    pub fn add_constraint(&mut self, constraint: Constraint) -> usize {
        let constraint_index = self.constraints.len();
        self.constraints.push((false, constraint)); // Add the new constraint as inactive by default.
        constraint_index
    }

    pub fn assert(&mut self, constraints: &[usize]) -> Result<(), Vec<usize>> {
        for &index in constraints {
            let (active, _) = self.constraints.get_mut(index).unwrap();
            if !*active {
                *active = true; // Mark the constraint as active.
                if self.in_queue.insert(index) {
                    self.prop_q.push_back(index); // Add to propagation queue if not already present.
                }
            }
        }
        self.propagate()
    }

    pub fn retract(&mut self, constraints: &[usize]) -> Result<(), Vec<usize>> {
        for &index in constraints {
            let (active, _) = self.constraints.get_mut(index).unwrap();
            if *active {
                *active = false; // Mark the constraint as inactive.
                if self.in_queue.insert(index) {
                    self.prop_q.push_back(index); // Add to propagation queue if not already present.
                }
            }
        }
        self.propagate()
    }

    fn propagate(&mut self) -> Result<(), Vec<usize>> {
        Ok(())
    }
}
