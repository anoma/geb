# Restricted Wedge/Cowedge Research Directions

## Status

Active

## Context

With the generalization of `sliceProfunctor` and all restricted cowedge
structures to a separate target category `D`, several new research
directions have emerged connecting structural (co)ends, restricted
(co)wedges, and categories of diagonal elements.

## Research Questions

### Q1: StructuralCoend = initial StrongRestrictedCowedge?

`StructuralCoend F = CostructureIntegral F IdProf` is built from the
paranaturality quotient. `StrongRestrictedCowedge` requires paranatural
families.

Conjecture: `StructuralCoend F` is the initial `StrongRestrictedCowedge
F IdProf` (for `C = D = Type v`).

Dually: `StructuralEnd F` is the terminal `StrongRestrictedWedge F
IdProf`.

The comparison with Vene's restricted coend (initial `RestrictedCowedge`)
goes: initial `RestrictedCowedge` -> initial `StrongRestrictedCowedge`,
not the other way. Reason: the fully faithful inclusion
`StrongRestrictedCowedge -> RestrictedCowedge` means initiality in the
larger category implies initiality in the smaller, but not conversely.

### Q2: RestrictedWedge generalizes Wedge(powerProfunctor)

Define `RestrictedWedge G H` (dual of `RestrictedCowedge`):

- `pt : D`
- `family : (I : C) -> H(I,I) -> Hom_D(pt, G(I,I))`, dinatural

Conjecture: when `D` has powers, `RestrictedWedge G H` is equivalent to
`Wedge` of a profunctor built from pointwise powers `G(I,J) ^. H(I,J)`.
The power adjunction converts between morphisms to powers and families
indexed by the exponent.

Similarly, `StrongRestrictedWedge` generalizes `Wedge(powerProfunctor)`
with the paranaturality condition.

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
- Task #44: Prove RestrictedWedge generalizes Wedge(powerProfunctor)
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
- Task #47: Characterize RestrictedWedge/Cowedge as cones/cocones

## Related Files

- `GebLean/Weighted.lean` - RestrictedCowedge, StrongRestrictedCowedge
- `GebLean/Paranatural.lean` - DiagElem, StructuralEnd, StructuralCoend
- `GebLean/Utilities/PowersAndCopowers.lean` - powerProfunctor,
  copowerProfunctor, weighted equivalences

## Related Workstreams

- `weighted-vs-paranatural-algebra.md`
- `weighted-vs-strong-restricted.md`
