# Weighted Wedges via Diagonal Elements

## Problem Statement

We have defined `WeightedWedge` and `WeightedCowedge` as weighted cones and
weighted cocones over specific functors derived from profunctors (via the
twisted arrow category). There is a known result that weighted cones/cocones
can be defined as ordinary cones/cocones using the category of elements of
the weight functor.

The question: can we find a category K with an endoprofunctor Q such that
ordinary wedges/cowedges over Q are equivalent to weighted wedges/cowedges?
If so, this would validate our definitions by showing that two different
approaches (via weighted cones and via ordinary wedges) yield equivalent
categories.

## Current Definitions

From `GebLean/Weighted.lean`:

```lean
abbrev WeightedWedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCone (C := D) (J := TwistedArrow C)
    (profunctorOnTwistedArrow C W) (profunctorOnTwistedArrow C P)

abbrev WeightedCowedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCocone (C := D) (J := CoTwistedArrow C)
    (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)
```

So:

- `WeightedWedge W P` is a weighted cone over `TwistedArrow C` with weight
  `profunctorOnTwistedArrow C W` and diagram `profunctorOnTwistedArrow C P`
- `WeightedCocone W D` has weight `W : Jᵒᵖ ⥤ Type v` (a presheaf) and consists
  of a natural transformation `W ⟶ homToFunctor D pt`

## Four Candidates

The question suggests four possibilities for the base category K:

1. `El(W)` - Category of elements of the weight profunctor
2. `El(W)` for wedges, `El(W)ᵒᵖ` for cowedges
3. `DiagElem W` - Category of diagonal elements of the weight profunctor
4. `DiagElem W` for wedges, `(DiagElem W)ᵒᵖ` for cowedges

## Analysis Results

### Option 1: Already Implemented

The codebase already implements the category of elements approach via
`weightedWedgeElementsEquiv` (Weighted.lean, line 1760):

```lean
def weightedWedgeElementsEquiv (W : Cᵒᵖ ⥤ C ⥤ Type v₅) (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedWedge W P ≌ Cone (weightedWedgeDiagram W P) :=
  weightedConeElementsEquiv (profunctorOnTwistedArrow C W)
    (profunctorOnTwistedArrow C P)
```

This shows that `WeightedWedge W P` is equivalent to ordinary cones over the
diagram `weightedWedgeDiagram W P`, which is obtained by composing:

- The projection `π : El(profunctorOnTwistedArrow C W) → TwistedArrow C`
- The profunctor diagram `profunctorOnTwistedArrow C P`

Similarly for cowedges via `weightedCowedgeElementsEquiv`.

### Options 3 and 4: Variance Obstruction

The codebase explicitly documents why the DiagElem approach does NOT work
in general (Weighted.lean, lines 1778-1833, section "WeightedWedgeAsProfunctor").

The naive idea is to define a profunctor `P'` on the category of elements such
that `Wedge P' ≌ WeightedWedge W P`. However:

**Variance Obstruction**: For a TwistedArrow morphism `f : tw₁ ⟶ tw₂`:

- `twDomArr f : twDom tw₂ ⟶ twDom tw₁` (contravariant in the domain)
- `twCodArr f : twCod tw₁ ⟶ twCod tw₂` (covariant in the codomain)

For `P : Cᵒᵖ ⥤ C ⥤ D` (contravariant in first arg, covariant in second):

- The second argument works: `twCodArr` is covariant, matching P's second slot
- The first argument fails: `twDomArr` is contravariant, but when composed with
  P's contravariance and the opposite category structure, we get the wrong
  direction for the overall morphism

**Promonad Explanation**: For a weighted wedge to reduce to an ordinary wedge
over some profunctor `P' : C'ᵒᵖ ⥤ C' ⥤ D`, we need `TwistedArrow C' ≅ W.Elements`
for some `C'`. But `TwistedArrow C'` is itself the category of elements of the
hom-profunctor `Hom_{C'} : C'ᵒᵖ × C' → Set`.

This requires the weight W to be (isomorphic to) the hom-profunctor of some
category. Not every profunctor is a hom-profunctor - a profunctor needs the
structure of a **promonad** (a monad in the bicategory of profunctors) to
correspond to some category's hom-functor.

### DiagElem vs Full Category of Elements

There is also an indexing mismatch:

- `WeightedWedge W P` has components at ALL twisted arrows with weight data:
  objects `(f : c → d, w ∈ W(c, d))`
- `DiagElem W` only has objects at DIAGONAL elements: `(c, w ∈ W(c, c))`

For ordinary wedges, the naturality condition allows reconstructing non-diagonal
components from diagonal ones (via the canonical morphisms in TwistedArrow).
But for weighted wedges, this reconstruction requires that every element
`w ∈ W(c, d)` can be obtained from diagonal elements via the weight's
functorial action - which is only true when W is a hom-profunctor.

## Conclusion

**The canonical reduction is via the category of elements (Option 1)**, which
is already implemented in the codebase. Reduction to ordinary wedges over
DiagElem W (Options 3 and 4) does NOT work in general due to:

1. The variance obstruction for defining a suitable profunctor
2. The weight needing to be a hom-profunctor (promonad structure)
3. Insufficient data in diagonal elements alone to reconstruct all components

## Status

- [x] Task 1: Analyze which "Option" is most likely to give equivalence
  - **Result**: Option 1 (category of elements) is the canonical reduction
  - Options 3/4 (DiagElem W) do NOT work in general
- [x] Task 2: Check if equivalence is already implemented
  - **Result**: `weightedWedgeElementsEquiv` and
    `weightedCowedgeElementsEquiv` are already proven
- [ ] Task 3: Document findings in codebase (this file)
- [x] Task 4: Close investigation - the existing implementation is correct

## References

- Weighted.lean lines 1760-1774: `weightedWedgeElementsEquiv`,
  `weightedCowedgeElementsEquiv`
- Weighted.lean lines 1778-1833: Variance obstruction analysis
- Weighted.lean lines 1835-1919: Analysis for profunctor-derived weights
