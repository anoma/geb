# Weighted Cowedges as Canonical Restricted Cowedge Definition

## Motivation

The current `RestrictedCowedge` definition uses dinaturality conditions
(following Vene's thesis), but there's an alternative using paranaturality.
For ordinary wedges, dinaturality and paranaturality coincide because the
wedge conditions form a commutative square that can be read in either
direction. However, for restricted cowedges, the two choices lead to
potentially different definitions.

This workstream investigates whether weighted colimits provide a
"canonical" definition that resolves this ambiguity.

## Background

### Existing Wedge-to-Cone Correspondence

In `GebLean/Weighted.lean`, we have:

- `coneToWedge` (line ~247): Converts a cone over the twisted arrow diagram
  to a wedge
- `wedgeToCone` (line ~328): Converts a wedge to a cone over the twisted
  arrow diagram
- `coconeToCowedge` (line ~469): Converts a cocone to a cowedge
- `cowedgeToCocone` (line ~455): Converts a cowedge to a cocone

This establishes that wedges over `F : Cᵒᵖ ⥤ C ⥤ D` correspond to
cones over `profunctorOnTwistedArrow C F : TwistedArrow C ⥤ D`.

### Twisted Arrow Infrastructure

In `GebLean/Utilities/TwistedArrow.lean`:

- `twistedArrowForget : TwistedArrow C ⥤ Cᵒᵖ × C` - forgetful functor
- `coTwistedArrowForget : CoTwistedArrow C ⥤ Cᵒᵖᵒᵖ × Cᵒᵖ` - forgetful
  functor for the co-twisted arrow category

In `GebLean/Utilities/TwArrPresheaf.lean`:

- `profunctorOnTwistedArrow` (line ~1590): Pre-composes a profunctor with
  the twisted arrow forgetful functor
- `profunctorOnCoTwistedArrow` (line ~1623): Pre-composes a profunctor with
  the co-twisted arrow forgetful functor

### Weighted Colimits

Mathlib does not currently have explicit weighted limit/colimit definitions.
See `docs/mathlib-limits-colimits-guide.md` for details.

From the documentation:

- Ends and coends are weighted limits/colimits with the hom-functor as weight
- Kan extensions are weighted colimits when computed pointwise

External references:

- [Weighted Limits and Colimits (Riehl)](https://math.jhu.edu/~eriehl/weighted.pdf)
- [nLab: weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)

### Vene's Restricted Coend

From `docs/restricted-coends.md`:

A restricted cowedge involves:

- An endodifunctor `G : Cᵒᵖ × C → C`
- A difunctor `H : Cᵒᵖ × C → Set`
- A dinatural transformation between `H` and `G/C` (the slice profunctor)

## Tasks

### 1. Define Weighted Cones (General)

A weighted cone over `D : J ⥤ C` with weight `W : J ⥤ Type v` consists of:

- An object `c : C`
- For each `j : J` and `w : W.obj j`, a morphism `π j w : c ⟶ D.obj j`
- Naturality: for `f : j ⟶ j'` and `w : W.obj j`, we have
  `D.map f ∘ π j w = π j' (W.map f w)`

Equivalently: a natural transformation `W ⟶ Hom(c, D(-))`.

**Status**: Not started

**Location**: New file `GebLean/WeightedLimits.lean` or add to `Weighted.lean`

### 2. Define Weighted Cocones (General)

Dual to weighted cones:

- An object `c : C`
- For each `j : J` and `w : W.obj j`, a morphism `ι j w : D.obj j ⟶ c`
- Naturality: for `f : j ⟶ j'` and `w : W.obj j'`, we have
  `ι j' w ∘ D.map f = ι j (W.map f w)`

Equivalently: a natural transformation `Hom(D(-), c) ⟶ W`.

**Status**: Not started

**Location**: Same file as weighted cones

### 3. Define Weighted Wedges

A weighted wedge combines the twisted arrow reduction with weighted cones:

Given `F : Cᵒᵖ ⥤ C ⥤ Type v` and weight `W : Tw(C)ᵒᵖ ⥤ Type v`:

- Reduce `F` to a diagram on `Tw(C)` via `profunctorOnTwistedArrow`
- Take a weighted cone with weight `W`

**Status**: Not started

**Location**: `GebLean/Weighted.lean`

### 4. Define Weighted Cowedges

Dual construction using weighted cocones.

For restricted cowedges specifically:

- The weight `H : Cᵒᵖ × C → Type v` pulls back along the forgetful functor
  `coTwistedArrowForget` to give a weight on `CoTwistedArrow C`
- The functor `G : Cᵒᵖ × C → C` becomes a diagram via
  `profunctorOnCoTwistedArrow`

**Status**: Not started

**Location**: `GebLean/Weighted.lean`

### 5. Compare with Vene's Restricted Cowedge (Dinaturality)

The current `RestrictedCowedge` in `GebLean/Weighted.lean` uses:

- `ParanatSig H (G ⇓ pt)` for the family structure
- `IsDinatural H (G ⇓ pt) family` for the dinaturality condition

Compare this with the weighted cowedge definition from Task 4.

Questions to answer:

- Are they equivalent?
- If not, what's the relationship?
- Which captures Vene's original definition more faithfully?

**Status**: Not started

### 6. Define Strong Restricted Cowedges

Define `StrongRestrictedCowedge` analogously to `RestrictedCowedge`, but using
`IsParanatural` instead of `IsDinatural`. Paranatural transformations are also
called "strong dinatural transformations", hence the name.

The structure should have:

- `pt : C` - the summit object
- `family : ParanatSig H (G ⇓ pt)` - the family of morphisms
- `isParanatural : IsParanatural H (G ⇓ pt) family` - paranaturality condition

Define the category of strong restricted cowedges with the same notion of
homomorphism as for `RestrictedCowedge` (post-composition commuting with the
family). Verify that this forms a category by proving the identity and
associativity laws.

**Status**: Not started

**Location**: `GebLean/Weighted.lean`

### 7. Compare with Paranaturality Version

Compare `StrongRestrictedCowedge` (from Task 6) with `RestrictedCowedge` and
with weighted cowedges (from Task 4).

Questions to answer:

- Is `StrongRestrictedCowedge` equivalent to the weighted cowedge?
- Is it equivalent to `RestrictedCowedge` (the dinaturality version)?
- If all three differ, which is "correct"?

**Status**: Not started

### 8. Determine Canonical Definition

Based on the comparisons in Tasks 5 and 7:

- If all definitions coincide, document this equivalence
- If they differ, determine which is canonical (likely the weighted
  cowedge, as it's derived from first principles)
- Update the codebase accordingly

**Status**: Not started

## References

### Code References

- `GebLean/Weighted.lean`: Current restricted cowedge implementation
  - `RestrictedCowedge` structure (~line 740)
  - `sliceProfunctor` (~line 576)
  - `sliceProfunctorFunctor` (~line 609)
  - `sliceProfunctorBifunctor` (~line 699)
  - `coneToWedge` (~line 247)
  - `wedgeToCone` (~line 328)
  - `coconeToCowedge` (~line 469)
  - `cowedgeToCocone` (~line 455)

- `GebLean/Utilities/TwistedArrow.lean`: Twisted arrow infrastructure
  - `twistedArrowForget` functor
  - `coTwistedArrowForget` functor
  - `CoTwistedArrow` definition

- `GebLean/Utilities/TwArrPresheaf.lean`: Pre-composition functors
  - `profunctorOnTwistedArrow` (~line 1590)
  - `profunctorOnCoTwistedArrow` (~line 1623)

- `GebLean/Paranatural.lean`: Paranaturality definitions
  - `ParanatSig` structure
  - `IsDinatural` predicate

### Documentation References

- `docs/restricted-coends.md`: Vene's restricted coend theory
- `docs/mathlib-limits-colimits-guide.md`: Mathlib limit infrastructure

### External References

- Vene's thesis (2000): Original restricted coend definition
- Riehl's weighted limits paper: General theory
- nLab: weighted colimit article
