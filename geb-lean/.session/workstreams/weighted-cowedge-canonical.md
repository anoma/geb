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

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 580)

**Implementation**: `WeightedCone W D` with `π : W ⟶ homFromFunctor pt D`

### 2. Define Weighted Cocones (General)

Dual to weighted cones:

- An object `c : C`
- For each `j : J` and `w : W.obj j`, a morphism `ι j w : D.obj j ⟶ c`
- Naturality: for `f : j ⟶ j'` and `w : W.obj j'`, we have
  `ι j' w ∘ D.map f = ι j (W.map f w)`

Equivalently: a natural transformation `W ⟶ Hom(D(-), c)` where `W : Jᵒᵖ ⥤ Type v`.

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 613)

**Implementation**: `WeightedCocone W D` with `ι : W ⟶ homToFunctor D pt`

### 3. Define Weighted Wedges

A weighted wedge combines the twisted arrow reduction with weighted cones:

Given `P : Cᵒᵖ ⥤ C ⥤ D` and weight `W : TwistedArrow C ⥤ Type v`:

- Reduce `P` to a diagram on `TwistedArrow C` via `profunctorOnTwistedArrow`
- Take a weighted cone with weight `W`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 648)

**Implementation**:
`WeightedWedge W P := WeightedCone W (profunctorOnTwistedArrow C P)`

### 4. Define Weighted Cowedges

Dual construction using weighted cocones.

For restricted cowedges specifically:

- The weight `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` is a presheaf on the
  co-twisted arrow category
- The functor `G : Cᵒᵖ ⥤ C ⥤ C` becomes a diagram via
  `profunctorOnCoTwistedArrow`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 662)

**Implementation**:
`WeightedCowedge W P := WeightedCocone W (profunctorOnCoTwistedArrow C P)`

### 5. Compare with Vene's Restricted Cowedge (Dinaturality)

The current `RestrictedCowedge` in `GebLean/Weighted.lean` uses:

- `ParanatSig H (G ⇓ pt)` for the family structure
- `IsDinatural H (G ⇓ pt) family` for the dinaturality condition

Compare this with the weighted cowedge definition from Task 4.

Questions to answer:

- Are they equivalent?
- If not, what's the relationship?
- Which captures Vene's original definition more faithfully?

**Status**: In progress

**Findings**:

The two structures are not directly equivalent:

1. **Weighted cowedge** (`WeightedCowedge W G`): Uses a weight functor
   `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` and provides data at *all* co-twisted
   arrows (morphisms `f : A ⟶ B` in `C`).

2. **Restricted cowedge** (`RestrictedCowedge G H`): Uses a profunctor
   `H : Cᵒᵖ ⥤ C ⥤ Type v` but only provides data at *diagonal* elements
   (identity morphisms `id_A : A ⟶ A`), with a dinaturality condition
   relating the diagonal data across different objects.

The relationship:

- A restricted cowedge can be seen as specifying the "diagonal restriction"
  of a potential weighted cowedge
- The dinaturality condition ensures consistency of the diagonal data
- To get a weight `W` from `H`, one would compose `H` with the co-twisted
  arrow forgetful functor: `profunctorOnCoTwistedArrow C H`
- The restricted cowedge only uses diagonal values of this composition

Vene's original definition uses dinaturality, so `RestrictedCowedge` is
faithful to Vene's thesis. The weighted formulation is more general but
requires data at all co-twisted arrows, not just diagonals.

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

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 966)

**Implementation**:

- `StrongRestrictedCowedge G H` structure with `pt`, `family`, `isParanatural`
- `StrongRestrictedCowedge.toParanat`: Convert to `Paranat H (G ⇓ pt)`
- `StrongRestrictedCowedge.ofParanat`: Convert from `Paranat H (G ⇓ pt)`
- `StrongRestrictedCowedge.toRestrictedCowedge`: Every strong restricted
  cowedge is a restricted cowedge (paranaturality implies dinaturality)
- `StrongRestrictedCowedge.Hom`: Morphisms between strong restricted cowedges
- `StrongRestrictedCowedge.Hom.id`, `Hom.comp`: Identity and composition
- `StrongRestrictedCowedgeCat`: Category instance for strong restricted cowedges
- `inclusion`: Inclusion functor from strong restricted cowedges to
  restricted cowedges
- `inclusion_fullyFaithful`: Proof that the inclusion is fully faithful,
  making strong restricted cowedges a full subcategory

### 7. Compare with Paranaturality Version

Compare `StrongRestrictedCowedge` (from Task 6) with `RestrictedCowedge` and
with weighted cowedges (from Task 4).

Questions to answer:

- Is `StrongRestrictedCowedge` equivalent to the weighted cowedge?
- Is it equivalent to `RestrictedCowedge` (the dinaturality version)?
- If all three differ, which is "correct"?

**Status**: Completed

**Findings**:

The three definitions form a hierarchy with strict inclusions:

```text
WeightedCowedge  ⊋  StrongRestrictedCowedge  ⊋  RestrictedCowedge
   (most data)         (paranaturality)          (dinaturality)
```

**1. StrongRestrictedCowedge vs RestrictedCowedge**:

- `StrongRestrictedCowedge.toRestrictedCowedge` exists (paranaturality implies
  dinaturality)
- The reverse does NOT hold in general
- Paranaturality tests ALL compatible diagonal pairs `(d₀, d₁)` with
  `DiagCompat F I₀ I₁ f d₀ d₁`
- Dinaturality only tests pairs of the form `(F.lmap f x, F.rmap f x)` for
  off-diagonal elements `x`
- Not every compatible pair arises from an off-diagonal element

**2. WeightedCowedge vs StrongRestrictedCowedge**:

- WeightedCowedge provides data at ALL co-twisted arrows (all morphisms in C)
- StrongRestrictedCowedge provides data only at diagonal elements
- The weighted formulation has strictly more data
- To embed StrongRestrictedCowedge into WeightedCowedge, one would need to
  extend diagonal data to all co-twisted arrows (likely via Kan extension)
- This extension is not generally unique or canonical without additional
  structure

**3. Relationship to Vene's Definition**:

- Vene's original definition uses dinaturality, so `RestrictedCowedge` matches
  Vene's thesis
- `StrongRestrictedCowedge` is a strengthening that uses paranaturality
- `WeightedCowedge` is the most general formulation from first principles

### 8. Determine Canonical Definition

Based on the comparisons in Tasks 5 and 7:

- If all definitions coincide, document this equivalence
- If they differ, determine which is canonical (likely the weighted
  cowedge, as it's derived from first principles)
- Update the codebase accordingly

**Status**: Completed

**Conclusion**:

The three definitions are NOT equivalent and serve different purposes. Which
is "canonical" depends on context:

**For Vene's Mendler-style recursion (original motivation)**:

Use `RestrictedCowedge` (dinaturality). This matches Vene's thesis exactly and
is sufficient for the categorical semantics of inductive and coinductive types.

**For the strongest condition on diagonal data**:

Use `StrongRestrictedCowedge` (paranaturality). This is a natural strengthening
that preserves all compatible diagonal pairs, not just those arising from
off-diagonal elements. Useful when paranaturality is required by the
application.

**For the most general weighted formulation**:

Use `WeightedCowedge`. This is derived from first principles of weighted
colimits and provides data at all morphisms, not just identities. This is the
"correct" categorical formulation when full generality is needed.

**Recommendation**:

Keep all three definitions in the codebase:

1. `RestrictedCowedge`: For Vene-style restricted coends
2. `StrongRestrictedCowedge`: For applications requiring paranaturality
3. `WeightedCowedge`: For general weighted colimit theory

The fully faithful inclusion functor `StrongRestrictedCowedge → RestrictedCowedge`
establishes that strong restricted cowedges form a full subcategory of restricted
cowedges. The relationship between `WeightedCowedge` and the restricted variants
would require additional work (diagonal restriction and Kan extension) to
formalize.

## References

### Code References

- `GebLean/Weighted.lean`: Weighted limits and restricted cowedges
  - Weighted cones/cocones: `WeightedCone` (~line 580),
    `WeightedCocone` (~line 613)
  - Weighted wedges/cowedges: `WeightedWedge` (~line 648),
    `WeightedCowedge` (~line 661)
  - Slice profunctor: `sliceProfunctor` (~line 689),
    `sliceProfunctorFunctor` (~line 722)
  - Restricted cowedges: `RestrictedCowedge` (~line 840),
    `RestrictedCowedgeCat` (~line 905)
  - Strong restricted cowedges: `StrongRestrictedCowedge` (~line 966),
    `StrongRestrictedCowedgeCat` (~line 1032)
  - Inclusion functor: `inclusion` (~line 1177),
    `inclusion_fullyFaithful` (~line 1189)
  - Wedge/cone equivalences: `coneToWedge` (~line 247), `wedgeToCone` (~line 328)

- `GebLean/Utilities/TwistedArrow.lean`: Twisted arrow infrastructure
  - `twistedArrowForget` functor
  - `coTwistedArrowForget` functor
  - `CoTwistedArrow` definition

- `GebLean/Utilities/TwArrPresheaf.lean`: Pre-composition functors
  - `profunctorOnTwistedArrow` (~line 1590)
  - `profunctorOnCoTwistedArrow` (~line 1623)

- `GebLean/Paranatural.lean`: Paranaturality definitions
  - `ParanatSig` structure (~line 241)
  - `IsParanatural` predicate (~line 248)
  - `IsDinatural` predicate (~line 730)
  - `paranatural_implies_dinatural` theorem (~line 772)

### Documentation References

- `docs/restricted-coends.md`: Vene's restricted coend theory
- `docs/mathlib-limits-colimits-guide.md`: Mathlib limit infrastructure

### External References

- Vene's thesis (2000): Original restricted coend definition
- Riehl's weighted limits paper: General theory
- nLab: weighted colimit article
