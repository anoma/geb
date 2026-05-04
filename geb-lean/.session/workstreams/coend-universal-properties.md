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

**Formal limit/colimit connections**:

```text
structuralEndLimitCone F : Cone (DiagElem.forget F ⋙ uliftFunctor)
  pt = StructuralEnd F
  IsLimit via structuralEndLimitCone_isLimit

structuralCoendColimitCocone F : Cocone (DiagElem.forget F ⋙ uliftFunctor)
  pt = StructuralCoend F
  IsColimit via structuralCoendColimitCocone_isColimit
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

### Q3: 2-Categorical Structure (IN PROGRESS)

**Question**: Does composability of paranatural/natural transformations
enable 2-categorical structure on `StrongRestrictedWedge`/`WeightedWedge`
that is unavailable for `RestrictedWedge`?

**Analysis**:

1. **Within each wedge category**: No non-trivial 2-cells exist.
   Wedge morphisms are determined by their apex morphism plus a Prop
   commutativity condition. The existing `Slice2Hom.paranat_eq`
   result (Paranatural.lean) establishes that `EndoProf` is locally
   discrete under the `Cat/C` embedding.

2. **Between wedge categories (functoriality in the weight)**:
   Composability of paranatural transformations gives a
   contravariant functor
   `StrongRestrictedWedge G (−) : EndoProf^op → Cat`
   via weight pullback. This is unavailable for `RestrictedWedge`
   because dinatural transformations do not compose in general.

3. **Profunctor composition**: Mathlib does not currently formalize
   profunctor composition or the bicategory of profunctors. A
   connection to `Para(C)` would require this.

**Formalized** (in `GebLean/Weighted.lean`):

Weight functoriality (contravariant for wedges, covariant for cowedges):

- `weightPullbackFunctor`:
  `Paranat H₁ H₂ → (StrongRestrictedWedge G H₂ ⥤ StrongRestrictedWedge G H₁)`
- `weightPullbackFunctor_id`:
  pullback along `Paranat.id` = identity functor
- `weightPullbackFunctor_comp`:
  pullback along `α.comp β` = composition of pullback functors
- Duals: `weightPullbackCowedgeFunctor`,
  `weightPullbackCowedgeFunctor_id`,
  `weightPullbackCowedgeFunctor_comp`

Diagram functoriality (covariant for wedges, contravariant for cowedges):

- `profPostcompFunctor`:
  `(η : G₁ ⟶ G₂) → (StrongRestrictedWedge G₁ H ⥤ StrongRestrictedWedge G₂ H)`
- `profPostcompFunctor_id`:
  postcomposition by `𝟙 G` = identity functor
- `profPostcompFunctor_comp`:
  postcomposition by `η ≫ θ` = composition of postcomposition functors
- `profPrecompCowedgeFunctor`:
  `(η : G₁ ⟶ G₂) → (StrongRestrictedCowedge G₂ H ⥤ StrongRestrictedCowedge G₁ H)`
- `profPrecompCowedgeFunctor_id`:
  precomposition by `𝟙 G` = identity functor
- `profPrecompCowedgeFunctor_comp`:
  precomposition by `η ≫ θ` = composition of precomposition functors (reversed)

Interchange laws:

- `wedge_interchange`:
  `profPostcompFunctor H₂ η ⋙ weightPullbackFunctor G₂ α =
   weightPullbackFunctor G₁ α ⋙ profPostcompFunctor H₁ η`
- `cowedge_interchange`:
  `profPrecompCowedgeFunctor H₂ η ⋙ weightPullbackCowedgeFunctor G₁ α =
   weightPullbackCowedgeFunctor G₂ α ⋙ profPrecompCowedgeFunctor H₁ η`

Bifunctors:

- `strongRestrictedWedgeBifunctor`:
  `(Cᵒᵖ ⥤ C ⥤ D) × EndoProf(C)ᵒᵖ ⥤ Cat`
  (covariant in G, contravariant in H)
- `strongRestrictedCowedgeBifunctor`:
  `((Cᵒᵖ ⥤ C ⥤ D) × EndoProf(C))ᵒᵖ ⥤ Cat`
  (contravariant in both G and H)

**Remaining**:

- Connection to `Para(C)` (requires profunctor composition)

## Tasks

- [x] Formalize AlgProf and Kan extension connection via sections (Q1)
- [x] Formalize conditions for terminality transfer across non-full functors (Q2)
- [x] Formalize weight pullback functors (Q3, partial)
- [x] Formalize covariant functoriality in G (Q3)
- [x] Assemble bifunctor structure (Q3)
- [ ] Explore profunctor composition / Para(C) connection (Q3)
- [x] Document findings in `docs/coend-formulas-research.md`

## Related Files

- `docs/coend-formulas-research.md` - Main research document
- `GebLean/ParanatAlg.lean` - Kan extension connection (Q1)
- `GebLean/WeightedAlg.lean` - AlgProf, CoalgProf definitions
- `GebLean/Weighted.lean` - (Co)wedge definitions

## Related Workstreams

- `restricted-wedge-research.md` (completed)
- `weighted-vs-strong-restricted.md`
