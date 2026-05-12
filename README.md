# ac3rm

A highly efficient incremental Arc Consistency (AC-3rm) propagator written in Rust.

**ac3rm** maintains constraint consistency dynamically, supporting:
- **Dynamic constraint insertion** with incremental propagation
- **Dynamic constraint retraction** with neighborhood re-propagation
- **AC-3rm algorithm** with residual supports for optimal constraint checking
- **Batch operations** for efficient multi-constraint updates
- **Listener callbacks** for reactive domain change notifications

## Constraint Types

- **Binary equality**: `var_a == var_b`
- **Binary inequality**: `var_a != var_b`
- **Unary set**: `var == value` (domain becomes singleton)
- **Unary forbid**: `var != value` (value removed from domain)

## Key Features

### AC-3rm with Residual Supports
The engine implements the AC-3rm algorithm, which extends AC-3 with residual supports:
- Each value maintains a cached support to avoid redundant domain scans
- When a domain changes, only affected arcs are re-queued
- Incoming arcs are prioritized during propagation for efficiency

### Incremental Architecture
- Constraints can be added and removed dynamically
- Retracting a constraint only re-propagates the affected neighborhood
- Multi-killer support: values can be suppressed by multiple constraints simultaneously

### Batch Operations
For better performance when applying multiple constraints:
- `assert_batch(&[id1, id2, ...])` — Assert multiple constraints with a single propagation pass
- `retract_batch(&[id1, id2, ...])` — Retract multiple constraints with a single re-propagation pass

### Reactive Updates
Register callbacks to monitor domain changes in real-time:
```rust
engine.set_listener(var_id, |var| {
    println!("Variable {} domain changed", var);
});
```

## Installation

Add to `Cargo.toml`:

```toml
[dependencies]
ac3rm = "0.1"
```

## Usage

### Basic Constraint Propagation

```rust
use ac3rm::Engine;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut engine = Engine::new();

    // Create variables
    let a = engine.add_variable([1, 2, 3]);
    let b = engine.add_variable([2, 3, 4]);

    // Add equality constraint
    engine.new_eq(a, b)?;
    
    // Domains are now intersected: {2, 3}
    assert_eq!(engine.val(a), vec![2, 3]);
    assert_eq!(engine.val(b), vec![2, 3]);
    
    Ok(())
}
```

### Dynamic Constraint Retraction

```rust
use ac3rm::Engine;

fn main() -> Result<(), Box<dyn std::error::Error>> {
let mut engine = Engine::new();
let a = engine.add_variable([1, 2, 3]);
let b = engine.add_variable([2, 3, 4]);

let eq_id = engine.new_eq(a, b)?;
assert_eq!(engine.val(a), vec![2, 3]);

// Remove the constraint
engine.retract(eq_id)?;

// Domains return to original state
assert_eq!(engine.val(a), vec![1, 2, 3]);
assert_eq!(engine.val(b), vec![2, 3, 4]);

Ok(())
}
```

### Batch Operations

```rust
use ac3rm::{Constraint, Engine};

fn main() -> Result<(), Box<dyn std::error::Error>> {
let mut engine = Engine::new();
let x = engine.add_variable([1, 2, 3]);
let y = engine.add_variable([1, 2, 3]);

let c1 = engine.add_constraint(Constraint::Equality(x, y));
let c2 = engine.add_constraint(Constraint::Set(x, 2));
let c3 = engine.add_constraint(Constraint::Forbid(y, 1));

// Apply all three constraints with a single propagation pass
engine.assert_batch(&[c1, c2, c3])?;

Ok(())
}
```

### Listener Callbacks

```rust
use ac3rm::Engine;
use std::sync::{Arc, Mutex};

fn main() -> Result<(), Box<dyn std::error::Error>> {
let mut engine = Engine::new();
let x = engine.add_variable([1, 2, 3]);
let y = engine.add_variable([2, 3, 4]);

let changes = Arc::new(Mutex::new(Vec::new()));
let changes_clone = changes.clone();

engine.set_listener(x, move |var_id| {
    changes_clone.lock().unwrap().push(var_id);
});

engine.new_eq(x, y)?;  // Triggers listener callback

Ok(())
}
```

### Error Handling

```rust
use ac3rm::PropagationError;

match engine.new_eq(a, b) {
    Ok(id) => println!("Constraint {} asserted", id),
    Err(PropagationError::DomainWipeout { var, explanation }) => {
        println!("Variable {} has no valid values", var);
        println!("Conflicting constraints: {:?}", explanation);
    }
    Err(PropagationError::InvalidConstraintId(id)) => {
        println!("Constraint {} does not exist", id);
    }
}
```

## Performance Characteristics

- **Assertion**: O(d·k) in worst case, where d is domain size, k is arity (≤2 for this engine)
- **Retraction**: O(d·k) incremental re-propagation of affected neighborhood
- **Residual supports**: Amortized O(1) support lookup in typical scenarios

## Testing

All functionality is thoroughly tested:

```bash
cargo test --lib
```

Tests cover:
- Unary and binary constraint interactions
- Incremental retraction and re-assertion
- Multi-killer scenarios (multiple constraints suppressing the same value)
- Batch operation equivalence with sequential calls
- Listener notification during propagation
- Complex propagation chains

## Architecture

The engine manages:
- **Variables**: Each has a domain of active/suppressed values
- **Constraints**: Can be active (enforced) or inactive
- **Residues**: Cached support values for AC-3rm optimization
- **Listeners**: Callbacks invoked when domains change

The propagation queue processes arcs (directed constraint applications) until quiescence, ensuring arc-consistency is maintained after each update.
