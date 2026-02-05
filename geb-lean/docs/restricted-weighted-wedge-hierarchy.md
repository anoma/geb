# Restricted and Weighted (Co)Wedges: A Three-Level Hierarchy

This document describes how restricted and weighted (co)wedges relate to
standard (co)wedges via categorical equivalences.

## Overview

Three related constructions generalize (co)wedges with additional structure:

1. **RestrictedWedge/Cowedge** (Vene): dinaturality indexed by a profunctor
2. **StrongRestrictedWedge/Cowedge**: paranaturality (stronger than dinaturality)
3. **WeightedWedge/Cowedge**: cocones over (co)twisted arrow categories

Each can be expressed as a standard (co)wedge over an appropriate profunctor
when the target category has (co)powers. Their universal objects (terminal
wedges/initial cowedges) are then (co)ends.

## The Hierarchy

| Structure | Profunctor | Universal |
| --- | --- | --- |
| `RestrictedWedge G H` | `powerProfunctorProfArg G H` | End |
| `RestrictedCowedge G H` | `copowerProfunctorProfArg G H` | Coend |
| `StrongRestrictedWedge G H` | `diagElemProf G H` | `StructureIntegral` |
| `StrongRestrictedCowedge G H` | `diagElemProf G H` | `CostructureIntegral` |
| `WeightedWedge W G` | `powerWeightedProfunctor W G` | End |
| `WeightedCowedge W G` | `copowerWeightedProfunctor W G` | Coend |

## Profunctor Definitions

### For Restricted (Co)Wedges

Given `G, H : Cᵒᵖ ⥤ C ⥤ Type v`:

- `powerProfunctorProfArg G H` at `(I, J)` = `H(J, I) → G(I, J)`
  - On diagonal: `H(I, I) → G(I, I)`
  - The argument swap in `H` accounts for contravariance of `→` in
    its domain

- `copowerProfunctorProfArg G H` at `(I, J)` = `H(I, J) × G(I, J)`
  - On diagonal: `H(I, I) × G(I, I)`
  - No argument swap since `×` is covariant in both factors

### For Strong Restricted (Co)Wedges

- `diagElemProf G H` = `profPullback G (DiagElem.forget H)`
  - Evaluates `G` at the base objects of diagonal elements of `H`
  - Morphisms in `DiagElem H` encode the paranaturality condition

### For Weighted (Co)Wedges

Given `W : CoTwistedArrow C ⥤ Type v` and `G : CoTwistedArrow C ⥤ Type v`:

- `powerWeightedProfunctor W G` at `j` = `W(j) → G(j)`
- `copowerWeightedProfunctor W G` at `j` = `W(j) × G(j)`

## Equivalences

### RestrictedWedge ≌ Wedge

```lean
restrictedWedgePowerEquiv :
  RestrictedWedge G H ≌ Wedge (powerProfunctorProfArg G H)
```

The family `∀ I, H(I,I) → (pt → G(I,I))` corresponds to legs
`∀ I, pt → (H(I,I) → G(I,I))` via function swap.

### RestrictedCowedge ≌ Cowedge

```lean
restrictedCowedgeCopowerEquiv :
  RestrictedCowedge G H ≌ Cowedge (copowerProfunctorProfArg G H)
```

The family `∀ I, H(I,I) → (G(I,I) → pt)` corresponds to legs
`∀ I, H(I,I) × G(I,I) → pt` via currying.

### StrongRestrictedWedge ≌ Wedge

```lean
strongRestrictedWedgeEquiv :
  StrongRestrictedWedge G H ≌ Wedge (diagElemProf G H)
```

### StrongRestrictedCowedge ≌ Cowedge

```lean
strongRestrictedCowedgeEquiv :
  StrongRestrictedCowedge G H ≌ Cowedge (diagElemProf G H)
```

### WeightedWedge ≌ Wedge

```lean
weightedWedgeWedgeEquiv :
  WeightedWedge W G ≌ Wedge (powerWeightedProfunctor W G)
```

### WeightedCowedge ≌ Cowedge

```lean
weightedCowedgeCowedgeEquiv :
  WeightedCowedge W G ≌ Cowedge (copowerWeightedProfunctor W G)
```

## Universal Properties

### StructureIntegral as Terminal StrongRestrictedWedge

```lean
structureIntegralWedge_isTerminal :
  IsTerminal (structureIntegralWedge G H)
```

The structure integral `StructureIntegral H G` consists of paranatural
families `(x : DiagElem H) → diagApp G x.base` satisfying an equalizer
condition. It is the terminal strong restricted wedge.

### CostructureIntegral as Initial StrongRestrictedCowedge

```lean
costructureIntegralCowedge_isInitial :
  IsInitial (costructureIntegralCowedge G H)
```

The costructure integral `CostructureIntegral H G` is the quotient of
pairs `(x : DiagElem H, g : diagApp G x.base)` by the paranaturality
relation. It is the initial strong restricted cowedge.

## Relationships Between Levels

### Restriction vs Strong Restriction

There is a fully faithful inclusion:

```lean
StrongRestrictedCowedge.inclusion :
  StrongRestrictedCowedge G H ⥤ RestrictedCowedge G H
```

Every paranatural family is dinatural, but not conversely.

### Weighted vs Strong Restricted

There is a faithful (but not full) functor:

```lean
strongRestrictionFunctor :
  WeightedCowedge H G ⥤ StrongRestrictedCowedge G H
```

This extracts the family at identity co-twisted arrows. The functor is
not full because weighted cowedges carry additional data at off-diagonal
co-twisted arrows.

There is no inclusion in the reverse direction: strong restricted
cowedges lack data at off-diagonal positions needed for weighted
cowedges.

## References

- `GebLean/Weighted.lean`: Main definitions and equivalences
- `GebLean/Paranatural.lean`: DiagElem, StructureIntegral, CostructureIntegral
- `GebLean/Utilities/PowersAndCopowers.lean`: Weighted profunctor equivalences
- Vene (2000): Original restricted coend definition
