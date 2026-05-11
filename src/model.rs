use std::{collections::HashMap, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(usize);

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.0)
    }
}

struct Value {
    value: i32,
    suppressed_by: Option<ConstraintId>, // The constraint that suppresses this value, if any.
    supported_by: HashMap<VarId, usize>, // Maps supporting variables to the value index in their domain.
}

struct Variable {
    id: VarId,
    domain: Vec<Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstraintId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Constraint {
    Equality(VarId, VarId),   // Represents an equality constraint between two variables (e.g., x_i == x_j).
    Inequality(VarId, VarId), // Represents an inequality constraint between two variables (e.g., x_i != x_j).
    Set(VarId, i32),          // Represents a constraint that a variable must take a specific value (e.g., x_i == 5).
    Forbid(VarId, i32),       // Represents a constraint that a variable cannot take a specific value (e.g., x_i != 5).
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
