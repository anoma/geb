# GebLean Tests

This directory contains tests for the GebLean library.

## Running Tests

Build and run all tests:

```bash
lake build test
```

## Test Structure

Tests are organized as Lean modules in this directory. The root `test.lean`
file imports all test modules.

## Writing Tests

### Using `#guard`

The simplest way to write tests is using Lean's built-in `#guard` command,
which checks that an expression evaluates to `true` at compile time:

```lean
import GebLean

#guard 1 + 1 == 2
#guard some_function arg == expected_result
```

**Note**: The `linter.hashCommand` linter is disabled for the entire test
library in the lakefile, so you don't need to add `set_option` in each file.

For types that don't have `DecidableEq` instances, you may need to provide
decidability instances to enable equality testing. See
[Brandon Rozek's guide](https://brandonrozek.com/blog/writing-unit-tests-lean-4/)
for details.

### Using Plausible (Property-Based Testing)

Plausible is a property testing framework (similar to QuickCheck/Hypothesis)
that's already available as a dependency. Use it to find counterexamples:

```lean
import Plausible

example (xs : Array Int) (w : ∃ x : Int, x ∈ xs) :
    ∃ x : Int, x ∈ xs.reverse := by
  plausible  -- Automatically generates test cases
```

Plausible integrates with the tactic framework and can automatically:
- Generate test cases for built-in types
- Shrink counterexamples to minimal failing cases
- Find edge cases you might not think of

For custom types, implement `Repr`, `Shrinkable`, and `SampleableExt`
instances.

### Using LSpec (Optional)

For more sophisticated unit testing with a BDD-style DSL, you can add LSpec
as a dependency. LSpec provides a testing interface similar to Haskell's
Hspec.

## Test Guidelines

- Each test file should import `GebLean` or the specific modules being tested
- Use `set_option linter.hashCommand false` to disable the hash command linter
  in test files
- Group related tests into modules (e.g., `test/Semicategory.lean`,
  `test/AcyclicQuiver.lean`)
- Add comprehensive tests for:
  - **Unit tests**: Basic functionality using `#guard`
  - **Property tests**: Algebraic properties using `plausible`
  - **Edge cases**: Boundary conditions and special cases
  - **Equations**: Properties that should hold (check with `#guard`)

## Testing Strategy by Type

- **Algebraic structures** (semicategories, etc.): Use property testing to
  verify laws (associativity, identity, etc.)
- **Functors and morphisms**: Test composition laws and identity preservation
- **Finite structures**: Use `#guard` with concrete examples
- **Decidable predicates**: Test both positive and negative cases
