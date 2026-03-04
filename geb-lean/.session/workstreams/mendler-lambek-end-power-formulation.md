# Workstream: Mendler-Lambek Equivalence via Ends and Powers

## Status

Active

## Context

This workstream extends the completed Mendler-Lambek correspondence
(in `WeightedAlg.lean`) to derive an equivalent formulation of the
`GExtFunctor` (Vene's `G^e`) using ends and powers instead of
restricted coends. The existing `mendlerLambekEquiv` uses restricted
coends (initial objects in the category of hom-restricted cowedges).
This workstream re-expresses the same equivalence via a chain of
transformations: restricted coends to copower-profunctor coends,
then to an impredicative end formula, then replacing copowers with
powers.

### Mathematical Goal

Starting from:

```
G^e(pt) = restricted coend of G by HomToProf(pt)
        = initial hom-restricted cowedge
```

Derive:

```
Hom(G^e(pt), Y) ≅ ∫_A Hom(G(A,A), Y^(A→pt))
```

where `Y^(A→pt)` denotes the power and `∫_A` denotes the end.
This characterizes `G^e` via ends and powers rather than coends.

### Derivation Chain

1. `homRestrictedCopowerEquiv` transfers the restricted coend to
   an ordinary coend of `copowerProf (HomToProf pt) G`, where
   `copowerProf(H,G)(A,B) = H(A,B) . G(A,B)` (copower).

2. `typeCoend.endEquiv` (or its C-valued representable analogue)
   gives the impredicative end formula:
   `Hom(coend, Y) ≅ ∫_A Hom(P(A,A), Y)`.

3. `copowerPowerEquiv` replaces `Hom((A→pt) . G(A,A), Y)` with
   `Hom(G(A,A), Y^(A→pt))` inside the end.

### References

- Vene, "Categorical Programming with Inductive and Coinductive Types",
  sections 5.3-5.7
- Existing codebase:
  - `GebLean/WeightedAlg.lean` - mendlerLambekEquiv
  - `GebLean/RestrictedCoendAsColimit.lean` - homRestrictedCopowerEquiv
  - `GebLean/Utilities/EndsAndCoends.lean` - typeCoend.endEquiv,
    typeCoend.endImpredicative
  - `GebLean/Utilities/PowersAndCopowers.lean` - copowerPowerEquiv,
    copowerPowerAdjunction
  - `GebLean/Utilities/Category.lean` - isInitialOfEquivFunctor

## Tasks

### Task 1: Restricted coend as copower-profunctor coend

- [ ] 1a. Define `HasAllCopowerProfCoends` typeclass: for all pt,
  `HomCopowerCowedge G pt` has an initial object
- [ ] 1b. Prove `HasAllHomToProfCoends.toCopowerProfCoends`:
  transfer `HasAllHomToProfCoends → HasAllCopowerProfCoends` using
  `isInitialOfEquivFunctor` with `homRestrictedCopowerEquiv`
- [ ] 1c. Prove `HasAllCopowerProfCoends.toHomToProfCoends`:
  transfer in the reverse direction using the inverse equivalence
- [ ] 1d. Define copower-coend variants of `GExtObj`, `GExtInj`,
  `GExtDesc`, `GExtFunctor` using copower-profunctor coends
- [ ] 1e. Define copower-coend variants of `floor`, `ceil`,
  `floorFunctor`, `ceilFunctor`
- [ ] 1f. Prove `mendlerLambekCopowerEquiv`: the Mendler-Lambek
  equivalence under `HasAllCopowerProfCoends`

### Task 2: Impredicative coend via ends (generic)

- [ ] 2a. Verify that `typeCoend.endEquiv` and
  `typeCoend.endImpredicative` already exist in EndsAndCoends.lean
  (they do: lines 1641 and 1710)
- [ ] 2b. Check whether `pointwiseTypeCoend.endEquiv` and
  `pointwiseTypeCoend.endImpredicative` exist for presheaf-valued
  profunctors (they do: lines 2262 and 2320)
- [ ] 2c. If needed, develop a representable coend-end duality for
  C-valued profunctors: for a C-valued coend (initial cowedge) of P,
  `Hom(coend_P, Y) ≅ typeEnd (A ↦ Hom(P(A,A), Y))` for all Y
- [ ] 2d. Ensure the derivation chain goes through:
  coNinjaYonedaEquiv → weightedColimitImpredicative →
  ninjaYonedaEquiv (in reverse)

### Task 3: Mendler-Lambek end formula with copower profunctor

- [ ] 3a. Apply coend-end duality to the copower-profunctor coend
  from task 1: `Hom(GExtObj_copower(pt), Y) ≅
  ∫_A Hom(copowerProf(HomToProf(pt), G)(A,A), Y)`
- [ ] 3b. Simplify using `copowerProf(HomToProf(pt), G)(A,A) =
  (A→pt) . G(A,A)`:
  `Hom(GExtObj(pt), Y) ≅ ∫_A Hom((A→pt) . G(A,A), Y)`
- [ ] 3c. Define the end-formula version of GExtFunctor

### Task 4: Replace copower with power inside the end

- [ ] 4a. Apply `copowerPowerEquiv` inside the end:
  `Hom((A→pt) . G(A,A), Y) ≅ Hom(G(A,A), Y^(A→pt))`
- [ ] 4b. Compose with task 3 to get the final formula:
  `Hom(GExtObj(pt), Y) ≅ ∫_A Hom(G(A,A), Y^(A→pt))`
- [ ] 4c. Define the end-and-power version of GExtFunctor
- [ ] 4d. Prove `mendlerLambekEndPowerEquiv`: the Mendler-Lambek
  equivalence expressed via ends and powers

## Notes

### Existing Infrastructure

- `isInitialOfEquivFunctor` (Category.lean:2487) transfers initial
  objects across category equivalences
- `homRestrictedCopowerEquiv` (RestrictedCoendAsColimit.lean:960)
  gives the category equivalence between hom-restricted cowedges and
  hom-copower cowedges
- `typeCoend.endEquiv` (EndsAndCoends.lean:1641) gives
  `(typeCoend P → Y) ≅ typeEnd(sliceProfunctorPoly P Y)`
- `copowerPowerEquiv` (PowersAndCopowers.lean:719) gives
  `(S . X → Y) ≅ (X → Y^S)`

### File Placement

- Task 1: Extends `RestrictedCoendAsColimit.lean` (or a new file)
- Task 2: `EndsAndCoends.lean` (verify existing, add if needed)
- Tasks 3-4: New file or extension of `WeightedAlg.lean`

### Dependencies Between Tasks

- Task 1 is independent (builds on existing equivalence)
- Task 2 is independent (verifies/extends generic infrastructure)
- Task 3 depends on tasks 1 and 2
- Task 4 depends on task 3
