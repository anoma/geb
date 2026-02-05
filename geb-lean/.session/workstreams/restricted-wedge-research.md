# Restricted Wedge/Cowedge Research Directions

## Status

Completed

## Summary

All three forms of restricted/weighted (co)wedges reduce to standard
(co)wedges over different profunctors. Their initial/terminal objects
are the corresponding (co)ends.

| Structure | Profunctor | Universal |
| --- | --- | --- |
| `RestrictedWedge G H` | `powerProfunctorProfArg G H` | End |
| `RestrictedCowedge G H` | `copowerProfunctorProfArg G H` | Coend |
| `StrongRestrictedWedge G H` | `diagElemProf G H` | `StructureIntegral` |
| `StrongRestrictedCowedge G H` | `diagElemProf G H` | `CostructureIntegral` |
| `WeightedWedge W G` | `powerWeightedProfunctor W G` | End |
| `WeightedCowedge W G` | `copowerWeightedProfunctor W G` | Coend |

The profunctors are:

- `powerProfunctorProfArg G H` at `(I,J)` = `H(J,I) → G(I,J)`
- `copowerProfunctorProfArg G H` at `(I,J)` = `H(I,J) × G(I,J)`
- `diagElemProf G H` = `profPullback G (DiagElem.forget H)`
- `powerWeightedProfunctor W G` at `j` = `W(j) → G(j)`
- `copowerWeightedProfunctor W G` at `j` = `W(j) × G(j)`

## Context

With the generalization of `sliceProfunctor` and all restricted cowedge
structures to a separate target category `D`, several new research
directions have emerged connecting structural (co)ends, restricted
(co)wedges, and categories of diagonal elements.

## Research Questions

### Q1: StructuralCoend = initial StrongRestrictedCowedge? (PROVEN)

**Result**: `CostructureIntegral H G` is the initial
`StrongRestrictedCowedge G H` via `costructureIntegralCowedge_isInitial`.
Dually, `StructureIntegral H G` is the terminal `StrongRestrictedWedge G H`
via `structureIntegralWedge_isTerminal`.

For `G = IdProf`, this gives `StructuralCoend F` as initial
`StrongRestrictedCowedge IdProf F` and `StructuralEnd F` as terminal
`StrongRestrictedWedge IdProf F`.

The results transfer via equivalences to give terminal/initial
wedges/cowedges for `diagElemProf G H`.

### Q2: RestrictedWedge/Cowedge generalize Wedge/Cowedge of power/copower profunctors

Define `RestrictedWedge G H` (dual of `RestrictedCowedge`):

- `pt : D`
- `family : (I : C) -> H(I,I) -> Hom_D(pt, G(I,I))`, dinatural

**Result**: Both wedge and cowedge equivalences hold!

For **wedges**: `RestrictedWedge G H ≌ Wedge (powerProfunctorProfArg G H)`
via `restrictedToPowerWedge` and `powerWedgeToRestricted` using
`Function.swap`. The wedge condition involves `H(I₁, I₀) → G(I₀, I₁)`,
which matches the off-diagonals in RestrictedWedge dinaturality.

For **cowedges**: `RestrictedCowedge G H ≌ Cowedge (copowerProfunctorProfArg G H)`
via `restrictedToCopowerCowedge` and `copowerCowedgeToRestricted`.
The cowedge condition for `copowerProfunctorProfArg G H` at `f : I₀ ⟶ I₁`
involves pairs `(h, g) : H(I₁, I₀) × G(I₁, I₀)`, and after currying,
the conditions align correctly with `RestrictedCowedge` dinaturality.

Full categorical equivalences implemented:

- `restrictedWedgePowerEquiv :`
  `RestrictedWedge G H ≌ Wedge (powerProfunctorProfArg G H)`
- `restrictedCowedgeCopowerEquiv :`
  `RestrictedCowedge G H ≌ Cowedge (copowerProfunctorProfArg G H)`

### Q3: Diagonal elements give StrongRestrictedWedge

Three-level hierarchy:

| Elements category | Cone/Cocone | Result |
| - | - | - |
| Full `(profOnTwArr W).Elements` | Cone | WeightedWedge |
| `DiagElem W` (identity TwArr) | Cone/Cocone | StrongRestrictedWedge/Cowedge |
| ??? | Cone | RestrictedWedge |

Morphisms in `DiagElem W` encode `DiagCompat`, which is the paranaturality
condition. Naturality of a cone along these morphisms gives paranaturality.

The existing equivalence `diagElemIdentityTwCoprEquiv : DiagElem P ≌
IdentityTwCoprArrElem P` connects diagonal elements to identity
co-twisted arrows.

`RestrictedWedge` (dinaturality only) may not have a clean "cone over
elements" characterization.

## Tasks

- Task #42: Define RestrictedWedge and StrongRestrictedWedge as duals
  (DONE)
- Task #43: Prove StrongRestrictedCowedge ≌ Cocone(DiagElem) (DONE)
  - `strongRestrictedCowedgeEquiv` in `Weighted.lean`
  - Uses `profPullback G (DiagElem.forget H)` as the profunctor
- Task #44: Prove RestrictedWedge generalizes Wedge(powerProfunctor) (DONE)
  - Defined `powerProfunctorProfArg G H : Cᵒᵖ ⥤ C ⥤ Type v` where
    `(powerProfunctorProfArg G H)(I, J) = H(J, I) → G(I, J)`
    Note: H's arguments are swapped due to contravariance of → in domain.
  - On diagonal: `H(I, I) → G(I, I)`, matching `RestrictedWedge` families.
  - Defined `copowerProfunctorProfArg G H : Cᵒᵖ ⥤ C ⥤ Type v` where
    `(copowerProfunctorProfArg G H)(I, J) = H(I, J) × G(I, J)`
    Note: No argument swap needed since × is covariant in both.
  - On diagonal: `H(I, I) × G(I, I)`, matching `RestrictedCowedge` families.
  - Added forgetful profunctor utilities to `Profunctors.lean`:
    - `covProfunctor F` for `F : C ⥤ Type v` gives `(I, J) ↦ F(J)`
    - `contravProfunctor F` for `F : Cᵒᵖ ⥤ Type v` gives `(I, J) ↦ F(I)`
  - Added consistency theorems in `Weighted.lean`
  - **Result**: Both equivalences hold!
    - `RestrictedWedge G H ≌ Wedge (powerProfunctorProfArg G H)` - DONE
      via `restrictedToPowerWedge` and `powerWedgeToRestricted`
      Full categorical equivalence `restrictedWedgePowerEquiv`
    - `RestrictedCowedge G H ≌ Cowedge (copowerProfunctorProfArg G H)` - DONE
      via `restrictedToCopowerCowedge` and `copowerCowedgeToRestricted`
      Full categorical equivalence `restrictedCowedgeCopowerEquiv`
- Task #45: Prove StructuralCoend = initial StrongRestrictedCowedge (DONE)
  - General case: `CostructureIntegral H G` is the initial
    `StrongRestrictedCowedge G H` via `costructureIntegralCowedge_isInitial`
    in `Weighted.lean`.
  - Dually: `StructureIntegral H G` is the terminal
    `StrongRestrictedWedge G H` via `structureIntegralWedge_isTerminal`.
  - Transfer across equivalences:
    `structureIntegralWedge_isTerminal_transfer` and
    `costructureIntegralCowedge_isInitial_transfer` give
    terminal wedge / initial cowedge for `diagElemProf G H`.
  - IdProf specialization via universe-polymorphic structures:
    - `sliceProfunctorPoly` and `cosliceProfunctorPoly` allow apex in
      any universe `Type p` while profunctors are valued in `Type w`.
    - `StrongRestrictedWedgePoly` and `StrongRestrictedCowedgePoly`
      allow `pt : Type p` independent of profunctor universes.
    - `structuralEndWedgePoly : StrongRestrictedWedgePoly IdProf F
      (StructuralEnd F)` with universal property:
      `structuralEndWedgePolyHom`, `structuralEndWedgePolyHom_comm`,
      `structuralEndWedgePolyHom_unique`.
    - `structuralCoendCowedgePoly : StrongRestrictedCowedgePoly IdProf F
      (StructuralCoend F)` with universal property:
      `structuralCoendCowedgePolyHom`, `structuralCoendCowedgePolyHom_comm`,
      `structuralCoendCowedgePolyHom_unique`.
- Task #46: Investigate comparison: initial RestrictedCowedge -> initial
  StrongRestrictedCowedge
- Task #47: Characterize RestrictedWedge/Cowedge as cones/cocones (DONE)
  - Based on Task #44 analysis:
    - `RestrictedWedge G H ≌ Wedge (powerProfunctorProfArg G H)` - DONE
      Full categorical equivalence `restrictedWedgePowerEquiv` implemented
      with functors `restrictedToPowerWedgeFunctor` and
      `powerWedgeToRestrictedFunctor`.
    - `RestrictedCowedge G H ≌ Cowedge (copowerProfunctorProfArg G H)` - DONE
      Full categorical equivalence `restrictedCowedgeCopowerEquiv` implemented
      with functors `restrictedToCopowerCowedgeFunctor` and
      `copowerCowedgeToRestrictedFunctor`.

## Related Files

- `GebLean/Weighted.lean` - RestrictedCowedge, StrongRestrictedCowedge
- `GebLean/Paranatural.lean` - DiagElem, StructuralEnd, StructuralCoend
- `GebLean/Utilities/PowersAndCopowers.lean` - powerProfunctor,
  copowerProfunctor, weighted equivalences

## Related Workstreams

- `weighted-vs-paranatural-algebra.md`
- `weighted-vs-strong-restricted.md`
