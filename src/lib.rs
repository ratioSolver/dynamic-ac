use std::fmt::{Display, Formatter, Result};

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
    constraints: Vec<(usize, usize, ConstraintKind)>,
}

impl Display for DynamicAC {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for (i, var_values) in self.values.iter().enumerate() {
            let var_values: Vec<String> = var_values.iter().filter(|v| v.suppressed_by.is_none()).map(|v| v.value.to_string()).collect();
            writeln!(f, "e{}: {{{}}}", i, var_values.join(", "))?;
        }
        for (var1, var2, kind) in &self.constraints {
            let kind_str = match kind {
                ConstraintKind::Equality => "==",
                ConstraintKind::Inequality => "!=",
            };
            writeln!(f, "e{} {} e{}", var1, kind_str, var2)?;
        }
        Ok(())
    }
}
