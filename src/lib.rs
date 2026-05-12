use std::fmt;

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
