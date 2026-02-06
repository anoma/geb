# (Co)End Universal Properties Research

## Status

Active

## Context

Having established that all three levels of restricted/weighted (co)wedges
correspond to standard (co)ends over particular profunctors, we now
investigate deeper connections to well-known categorical constructions.

## Research Questions

### Q1: Kan Extensions and Initial Algebras

**Hypothesis**: The StructuralEnd construction for `AlgProf G` (which gives
the initial algebra carrier) should connect to the right Kan extension of
the identity functor on `G-Alg` along the forgetful functor.

**Background**:

- `G-Alg ≌ DiagElem (AlgProf G)`
- Forgetful `U : G-Alg → C` corresponds to `DiagElem.forget`
- When `U` has a left adjoint (free algebra), then `Ran_U Id ≅ F` (the
  left adjoint)
- `StructuralEnd (AlgProf G)` is a limit over `DiagElem (AlgProf G)`

**To investigate**:

- Precise relationship between `StructuralEnd` and `Ran_{forget} Id`
- Whether the universal property of StructuralEnd derives from Kan
  extension universal properties
- Role of the free monad in this picture

### Q2: Transfer of Terminality/Initiality (COMPLETED)

**Question**: Under what conditions does terminality/initiality transfer
from `StrongRestrictedWedge`/`Cowedge` to `WeightedWedge`/`Cowedge`?

**Results**:

1. **Fully faithful case (Strong → Restricted)**: Automatic transfer.
   Formalized as `isStrongRestrictedEnd_of_isRestrictedEnd` and
   `isStrongRestrictedCoend_of_isRestrictedCoend`.

2. **Non-full case (Weighted → Strong)**: Transfer requires weight maps
   from diagonals to be jointly surjective. Counterexample: the Hom-
   profunctor on `WalkingParallelPair` (`wpp_weight_maps_not_surjective`).

**Dual**: Same analysis applies for initial objects and cowedges.

### Q3: 2-Categorical Structure

**Question**: Does composability of paranatural/natural transformations
enable 2-categorical structure on `StrongRestrictedWedge`/`WeightedWedge`
that is unavailable for `RestrictedWedge`?

**Structures to explore**:

- 2-cells between wedge morphisms
- Horizontal composition
- Bicategorical or double categorical structure
- Connection to `Para(C)` structure

## Tasks

- [ ] Investigate AlgProf and Kan extension connection (Q1)
- [x] Formalize conditions for terminality transfer across non-full functors (Q2)
- [ ] Explore 2-categorical structure possibilities (Q3)
- [x] Document findings in `docs/coend-formulas-research.md`

## Related Files

- `docs/coend-formulas-research.md` - Main research document
- `GebLean/WeightedAlg.lean` - AlgProf, CoalgProf definitions
- `GebLean/Weighted.lean` - (Co)wedge definitions

## Related Workstreams

- `restricted-wedge-research.md` (completed)
- `weighted-vs-strong-restricted.md`
