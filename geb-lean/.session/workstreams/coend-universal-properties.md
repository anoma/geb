# (Co)End Universal Properties Research

## Status

Active

## Context

Having established that all three levels of restricted/weighted (co)wedges
correspond to standard (co)ends over particular profunctors, we now
investigate deeper connections to well-known categorical constructions.

## Research Questions

### Q1: Kan Extensions and Initial Algebras (FORMALIZED)

**Hypothesis**: The StructuralEnd construction for `AlgProf G` (which gives
the initial algebra carrier) should connect to the right Kan extension of
the identity functor on `G-Alg` along the forgetful functor.

**Result**: Connection formalized via `Functor.sections` (limits in
`Type v`).

**Formalized equivalences** (in `GebLean/ParanatAlg.lean`):

- `structuralEndEquivSections`:
  `StructuralEnd F ≃ (DiagElem.forget F).sections`
  (structural end = limit of forgetful functor in `Type v`)
- `structuralEndLimitCone`:
  `Limits.Cone (DiagElem.forget F ⋙ uliftFunctor.{v+1})`
  (limit cone with `pt = StructuralEnd F`)
- `structuralEndLimitCone_isLimit`:
  `Limits.IsLimit (structuralEndLimitCone F)`
  (structural end satisfies mathlib's formal limit universal property)
- `diagElemAlg_forget_eq`:
  `DiagElem.forget (AlgProf G) = diagElemToAlgFunctor G ⋙ Algebra.forget G`
  (uses mathlib's `Endofunctor.Algebra.forget`)
- `algSectionsEquivStructuralEnd`:
  algebra forgetful functor sections ≃ structural end
- Duals: `diagElemCoalg_forget_eq`, `coalgSectionsEquivStructuralEnd`

**Full chain**:

```text
(diagElemToAlgFunctor G ⋙ Algebra.forget G).sections
  ≃ StructuralEnd (AlgProf G)
  ≃ μG.a
```

**Formal limit connection**:

```text
structuralEndLimitCone F : Cone (DiagElem.forget F ⋙ uliftFunctor)
  pt = StructuralEnd F
  IsLimit via structuralEndLimitCone_isLimit
```

### Q2: Transfer of Terminality/Initiality (COMPLETED)

**Question**: Under what conditions does terminality/initiality transfer
from `StrongRestrictedWedge`/`Cowedge` to `WeightedWedge`/`Cowedge`?

**Results**:

1. **Fully faithful case (Strong → Restricted)**: Automatic transfer.
   Formalized as `isStrongRestrictedEnd_of_isRestrictedEnd` and
   `isStrongRestrictedCoend_of_isRestrictedCoend`.

2. **Non-full case (Weighted → Strong)**: Transfer does NOT hold in general.
   Formalized counterexample on `WalkingParallelPair`:
   - `wppRestrictedCowedgeSumT_isInitial`: Initial RestrictedCowedge has
     `pt = Unit + Unit`
   - `costructureIntegralCowedge_isInitial`: Initial StrongRestrictedCowedge
     has `pt ≃ Unit`
   - `wppInitialCowedges_pt_not_equiv`: These are not equivalent

**Implication**: Initial algebras (which are StructureIntegrals, hence
terminal StrongRestrictedWedges) do NOT correspond to weighted ends.
The WeightedWedge category is "too small" - it has fewer morphisms,
so its terminal objects differ from those in StrongRestrictedWedge.

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

- [x] Formalize AlgProf and Kan extension connection via sections (Q1)
- [x] Formalize conditions for terminality transfer across non-full functors (Q2)
- [ ] Explore 2-categorical structure possibilities (Q3)
- [x] Document findings in `docs/coend-formulas-research.md`

## Related Files

- `docs/coend-formulas-research.md` - Main research document
- `GebLean/ParanatAlg.lean` - Kan extension connection (Q1)
- `GebLean/WeightedAlg.lean` - AlgProf, CoalgProf definitions
- `GebLean/Weighted.lean` - (Co)wedge definitions

## Related Workstreams

- `restricted-wedge-research.md` (completed)
- `weighted-vs-strong-restricted.md`
