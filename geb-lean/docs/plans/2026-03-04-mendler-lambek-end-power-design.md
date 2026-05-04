# Mendler-Lambek End-Power Formulation Implementation Plan

**Goal:** Express the Mendler-Lambek `GExtFunctor` via ends and
powers instead of restricted coends, yielding a representable
characterization `Hom(G^e(pt), Y) = end_A Hom(G(A,A), Y^(A->pt))`.

**Architecture:** Four tasks form a dependency chain. Tasks 1 and 2
are independent; task 3 composes them; task 4 applies
`copowerPowerEquiv` to the result. Task 1 goes in
`RestrictedCoendAsColimit.lean`, task 2 in `EndsAndCoends.lean`,
tasks 3-4 in a new `MendlerLambekEndPower.lean`.

**Tech Stack:** Lean 4 with mathlib (category theory library).

---

## Task 1: Transfer Restricted Coend to Copower-Profunctor Coend

**Files:**

- Modify: `GebLean/RestrictedCoendAsColimit.lean`

Use `homRestrictedCopowerEquiv` (equivalence between hom-restricted
cowedge and hom-copower cowedge categories) with
`isInitialOfEquivFunctor` (from `Utilities/Category.lean`) to
transfer initial objects between the two categories.

Definitions:

- `CopowerCoendCone` -- bundles initial copower cowedge
- `HasAllCopowerProfCoends` -- typeclass for existence
- `HasAllHomToProfCoends.toCopowerProfCoends` -- forward transfer
- `HasAllCopowerProfCoends.toHomToProfCoends` -- backward transfer
- `CopowerGExtObj`, `CopowerGExtInj` -- coend carrier and injection
- `mendlerLambekCopowerEquiv` -- the equivalence under copower
  assumption
- `copowerGExtIso` -- isomorphism between the two coend carriers

---

## Task 2: C-Valued Representable Coend-End Duality

**Files:**

- Modify: `GebLean/Utilities/EndsAndCoends.lean`

For a profunctor `P : C^op x C -> D` with an initial cowedge
(coend), derive:

```text
(coend.pt ⟶ Y) ≃ typeEnd (homSliceProf P Y)
```

where `homSliceProf P Y` sends `(A, B)` to `Hom_D(P(A,B), Y)`.

Definitions:

- `homSliceProf` -- the hom-slice profunctor for D-valued P
- `cowedgeHomEndEquiv` -- coend-end duality for initial cowedges

---

## Task 3: End Formula for GExtFunctor via Copower Profunctor

**Files:**

- Create: `GebLean/MendlerLambekEndPower.lean`
- Modify: `GebLean.lean` (add import)

Apply `cowedgeHomEndEquiv` to the copower-profunctor coend:

```text
Hom(GExtObj(pt), Y) ≃ end_A Hom((A→pt) . G(A,A), Y)
```

---

## Task 4: Replace Copower with Power Inside the End

**Files:**

- Modify: `GebLean/MendlerLambekEndPower.lean`

Apply `copowerPowerEquiv` fiberwise inside the end:

```text
end_A Hom((A→pt) . G(A,A), Y) ≃ end_A Hom(G(A,A), Y^(A→pt))
```

Definitions:

- `endPowerProf` -- the power-based profunctor
- `endCopowerPowerEquiv` -- equivalence of ends
- `gExtEndPowerEquiv` -- the final characterization

---

## Execution Notes

### Dependencies

- Task 1 and Task 2 are independent
- Task 3 requires both Task 1 and Task 2
- Task 4 requires Task 3

### Existing Utilities

- `isInitialOfEquivFunctor` (Category.lean:2487)
- `homRestrictedCopowerEquiv` (RestrictedCoendAsColimit.lean:960)
- `typeCoend.endEquiv` (EndsAndCoends.lean:1641)
- `typeEnd.map` (EndsAndCoends.lean)
- `copowerPowerEquiv` (PowersAndCopowers.lean:719)
- `copowerPowerAdjunction` (PowersAndCopowers.lean:771)
