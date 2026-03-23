# dynamic-ac

dynamic-ac is an incremental Arc Consistency (AC-3 style) propagator in Rust.

It supports dynamic addition and retraction of constraints, including:

- Binary equality: var_a == var_b
- Binary inequality: var_a != var_b
- Unary set: var == value
- Unary forbid: var != value

The engine keeps domains consistent after each update and re-propagates only the affected neighborhood when a constraint is retracted.

## Features

- Incremental propagation with a work queue
- Dynamic constraint insertion
- Dynamic constraint retraction
- Conflict reporting on domain wipeout
- Human-readable engine state via Display
- Unit-tested interactions between unary and binary constraints

## Installation

Add the crate to your Cargo.toml:

```toml
[dependencies]
dynamic-ac = "0.1"
```

Or use Cargo:

```bash
cargo add dynamic-ac
```

## Quick Start

```rust
use dynamic_ac::Engine;

fn main() {
	let mut ac = Engine::new();

	let a = ac.add_var(vec![1, 2, 3]);
	let b = ac.add_var(vec![2, 3, 4]);

	let eq_id = ac.new_eq(a, b).unwrap();
	assert_eq!(ac.val(a), vec![2, 3]);
	assert_eq!(ac.val(b), vec![2, 3]);

	let set_id = ac.set(a, 2).unwrap();
	assert_eq!(ac.val(a), vec![2]);
	assert_eq!(ac.val(b), vec![2]);

	ac.retract_constraint(set_id);
	assert_eq!(ac.val(a), vec![2, 3]);

	ac.retract_constraint(eq_id);
	assert_eq!(ac.val(a), vec![1, 2, 3]);
	assert_eq!(ac.val(b), vec![2, 3, 4]);
}
```

## API Overview

### Engine creation and variables

- Engine::new() -> Engine
- add_var(values: Vec<i32>) -> usize
- val(var_id: usize) -> Vec<i32>

### Constraint creation

- new_eq(var1, var2) -> Result<constraint_id, (constraint_id, explanation)>
- new_neq(var1, var2) -> Result<constraint_id, (constraint_id, explanation)>
- set(var, value) -> Result<constraint_id, (constraint_id, explanation)>
- forbid(var, value) -> Result<constraint_id, (constraint_id, explanation)>

On success, each function returns a constraint ID.

On failure, they return:

- The ID of the newly created constraint
- A conflict explanation: the set of constraint IDs involved in the domain wipeout

Note: even if propagation fails, the newly created constraint remains stored. You can retract it with retract_constraint.

### Constraint retraction

- retract_constraint(id)

Retraction is incremental:

- Removes the target constraint
- Releases values suppressed by that exact constraint
- Re-propagates constraints touching the affected variables

### Optional listener hook

- set_listener(var, callback)

You can register callbacks per variable. This is currently exposed by the API but not yet integrated into propagation events.

## Semantics

Each variable has a domain of integer values.

A value is either active or suppressed. Suppression is tracked by the specific constraint ID that removed it.

Propagation enforces local support:

- Equality: a value in var_a must appear in var_b
- Inequality: a value in var_a must have at least one different value in var_b
- Set: only the selected value survives
- Forbid: the selected value is removed

If all values of a variable are suppressed, propagation reports a domain wipeout.

## Example: Forbid and Retract

```rust
use dynamic_ac::Engine;

fn main() {
	let mut ac = Engine::new();
	let x = ac.add_var(vec![1, 2, 3]);

	let c = ac.forbid(x, 2).unwrap();
	assert_eq!(ac.val(x), vec![1, 3]);

	ac.retract_constraint(c);
	assert_eq!(ac.val(x), vec![1, 2, 3]);
}
```

## Display Output

Printing the engine shows active domains and constraints:

```text
e0: {2, 3}
e1: {2, 3}
e0 == e1
e0 forbid 1
```

## Running Tests

```bash
cargo test
```

## Project Status

This project is focused on a compact, understandable incremental propagator.

Current scope:

- Integer domains
- Binary equality/inequality
- Unary set/forbid
- Incremental retraction

Potential future extensions:

- Richer variable types
- Additional global constraints
- Event-driven listener integration
- Performance profiling and optimization passes
