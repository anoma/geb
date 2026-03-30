# Internal Presheaf--Grothendieck Equivalence

## Status: Both functors complete; equivalence proof deferred

## Completed

- **Task 1**: Pointwise category extraction (`fiberCategory`)
- **Task 2**: Externalization functor (`externalize`)
- **Task 3**: Discrete Unit compatibility (all `rfl`)
- **Task 4**: `PshInternalPresheaf` structure
- **Task 5**: `PshInternalPresheafHom` and `Category`
- **Task 7**: Grothendieck via mathlib `Grothendieck`
- **Task 8**: `comparisonFunctor`
- **Task 9**: `inverseFunctor` (both directions done)

## Files

- `GebLean/PshInternalExternalize.lean` (~620 lines)
- `GebLean/PshInternalPresheaf.lean` (~270 lines)
- `GebLean/PshInternalGrothendieck.lean` (~1174 lines)

## Deferred: equivalence proof

The counit naturality proof hits a pattern-matching
reduction obstacle.  `groth_decompose` provides the
morphism decomposition but connecting it to the
match-wrapped `counitApp` needs either a refactored
definition or explicit term manipulation.

## Plan document

`docs/superpowers/plans/2026-03-28-internal-presheaf-grothendieck.md`
