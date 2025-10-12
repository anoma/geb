# geb-lean

Formalizes the categorical gadgets that underpin the Geb programming
language in Lean 4. The library builds on mathlib to provide structured
treatments of finite quivers, semicategories, and the “judgment” categories
that encode the axioms of (semi)categories.

## Layout

- `GebLean/FiniteQuiver.lean`: witnesses and packages finite quivers
  together with their embeddings into mathlib’s `Quiv`.
- `GebLean/Semicategory.lean`: axiomatizes semicategories and semifunctors
  and bundles them into categorical structures.
- `GebLean/AcyclicQuiver.lean`, `GebLean/AcyclicCat.lean`: extend quivers
  with acyclicity data and assemble bundled (finite) categories.
- `GebLean/CategoryJudgments.lean`, `GebLean/DepCategoryJudgments.lean`:
  parallel encodings of categorical axioms via functor data and dependent
  types, linked by explicit equivalences.
- `test/`: worked examples (see `test/AcyclicCat.lean`) and notes on future
  property-based testing.

`GebLean.lean` re-exports the public API so downstream users can import a
single module.

## Building

The project uses Lake with Lean 4.24.0-rc1 and a pinned mathlib revision.
The first build will download those dependencies.

```bash
lake build
```

## Testing

Run the Lean test driver (configured in `lakefile.toml`):

```bash
lake test
```

See [test/README.md](test/README.md) for conventions and future testing
plans.

## Example

Import the library and access its core definitions:

```lean
import GebLean

example (V : Type) [Quiver V] [AcyclicQuiver V] [AcyclicCategory V] :
    Semicategory V := inferInstance

example (V : Type) [inst : AcyclicQuiver V] [AcyclicCategory V] :
    Quiver V := inst.toQuiver
```

Concrete examples such as the walking parallel pair semicategory are
available in the test directory (see [test/AcyclicCat.lean](test/AcyclicCat.lean)).
