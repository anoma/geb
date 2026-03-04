# Mendler-Lambek End-Power Formulation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

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
- Modify: `GebLean/RestrictedCoendAsColimit.lean` (append after
  line 2753, before `end GebLean`)

This task uses the existing `homRestrictedCopowerEquiv` (an
equivalence between the category of hom-restricted cowedges and the
category of hom-copower cowedges) together with
`isInitialOfEquivFunctor` (from `Utilities/Category.lean`) to show
that an initial object in one category transfers to an initial
object in the other.

### Step 1: Define `HasAllCopowerProfCoends` typeclass

```lean
section CopowerProfCoends

variable {C : Type u} [Category.{v} C]
  [HasCopowers C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)

class HasAllCopowerProfCoends where
  hasInitial :
    ∀ (pt : C),
      Limits.HasInitial (HomCopowerCowedge G pt)
```

This states that for all `pt`, the category of cowedges over
`copowerProf (HomToProf pt) G` has an initial object.

### Step 2: Transfer forward (restricted -> copower)

```lean
def HasAllHomToProfCoends.toCopowerProfCoends
    [HasAllHomToProfCoends G] :
    HasAllCopowerProfCoends G where
  hasInitial pt := by
    let e := homRestrictedCopowerEquiv G pt
    let rcInitial :=
      restrictedCoendIsInitial G (HomToProf pt)
    let cpInitial :=
      isInitialOfEquivFunctor e rcInitial
    exact Limits.hasInitial_of_unique
      (e.functor.obj (restrictedCoend G (HomToProf pt)))
```

The argument: `homRestrictedCopowerEquiv G pt` is an equivalence
`HomRestrictedCowedge G pt ≌ HomCopowerCowedge G pt`.
The restricted coend is initial in the source category.
`isInitialOfEquivFunctor` transfers it to the target category.

NOTE: The exact proof may need adjustment based on how
`Limits.HasInitial` is derived from `Limits.IsInitial`. We may
need `Limits.HasInitial.mk` with a `⟨obj, isInitial⟩` pair,
or use `hasInitial_of_unique` / `IsInitial.hasInitial`.

### Step 3: Transfer backward (copower -> restricted)

```lean
def HasAllCopowerProfCoends.toHomToProfCoends
    [HasAllCopowerProfCoends G] :
    HasAllHomToProfCoends G where
  hasCoend pt := by
    let e := (homRestrictedCopowerEquiv G pt).symm
    -- Transfer initial from HomCopowerCowedge to
    -- HomRestrictedCowedge using the inverse equivalence
    _
```

Analogous to step 2, using the inverse equivalence.

NOTE: `HasRestrictedCoend` has a specific structure (a
`RestrictedCoendCowedge`). We may need to construct this
from the `IsInitial` of a cowedge in the copower category.
The construction extracts `pt` and `family` from the image
cowedge.

### Step 4: Define copower-coend variants of GExt

```lean
namespace HasAllCopowerProfCoends

variable [HasAllCopowerProfCoends G]

def copowerCoend (pt : C) :
    HomCopowerCowedge G pt :=
  Limits.initial

def copowerCoendIsInitial (pt : C) :
    Limits.IsInitial (copowerCoend G pt) :=
  Limits.initialIsInitial

def CopowerGExtObj (pt : C) : C :=
  (copowerCoend G pt).pt

-- The injection from copowers into the coend:
-- inj_A : (A -> pt) . G(A,A) -> CopowerGExtObj(pt)
def CopowerGExtInj (pt : C) (A : C) :
    (copowerProfInner (HomToProf pt) G
      (Opposite.op A)).obj A ⟶
      CopowerGExtObj G pt :=
  (copowerCoend G pt).π A

end HasAllCopowerProfCoends
```

### Step 5: Build `CopowerGExtFunctor`

Define the functor `C ⥤ C` using copower-profunctor coends,
analogous to `GExtFunctor`. The map part uses the universal
property of the coend (initiality).

### Step 6: Prove `mendlerLambekCopowerEquiv`

The equivalence `MendlerAlgebra G ≌ ConventionalAlgebra
(CopowerGExtFunctor G)`. This should follow by composing
`mendlerLambekEquiv` with the isomorphism between `GExtFunctor`
and `CopowerGExtFunctor` (which holds because both coends
represent the same universal property).

Alternatively: show `CopowerGExtFunctor ≅ GExtFunctor` as
functors, then transport the equivalence.

### Step 7: Build and verify

Run: `lake build`
Expected: Clean build, no warnings.

---

## Task 2: C-Valued Representable Coend-End Duality

**Files:**
- Modify: `GebLean/Utilities/EndsAndCoends.lean` (append new
  section)

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with an initial cowedge
(coend), derive:

```
(coend.pt ⟶ Y) ≃ typeEnd (homSliceProf P Y)
```

where `homSliceProf P Y` is the profunctor
`(A, B) ↦ ((P.obj (op A)).obj B ⟶ Y)`.

### Step 1: Define the hom-slice profunctor

```lean
section CValuedCoendEndDuality

variable {C : Type u} [Category.{v} C]
  {D : Type w} [Category.{w'} D]

def homSliceProf
    (P : Cᵒᵖ ⥤ C ⥤ D) (Y : D) :
    Cᵒᵖ ⥤ C ⥤ Type w' where
  obj A := {
    obj := fun B =>
      ((P.obj A).obj B ⟶ Y)
    map := fun g f =>
      (P.obj A).map g ≫ f
    -- functoriality proofs
  }
  map := fun h => {
    app := fun B f =>
      (P.map h).app B ≫ f
    -- naturality proof
  }
  -- functor laws
```

This sends `(A, B) ↦ Hom_D(P(A,B), Y)`, which is a
`Type w'`-valued profunctor.

NOTE: This may already exist in the codebase as
`sliceProfunctorPoly` or a variant. Check carefully. The existing
`sliceProfunctorPoly` works for `Type v`-valued profunctors. We
need a version for `D`-valued profunctors using `D`-morphisms.

### Step 2: Prove the coend-end duality

```lean
def cowedgeHomEndEquiv
    (P : Cᵒᵖ ⥤ C ⥤ D)
    (cw : Cowedge P)
    (hcw : Limits.IsInitial cw)
    (Y : D) :
    (cw.pt ⟶ Y) ≃
      typeEnd (homSliceProf P Y) where
  toFun f := ⟨
    fun A x => cw.π A ≫ f,
    fun g => _  -- dinaturality from cowedge condition
  ⟩
  invFun h := hcw.descHom {
    pt := Y
    π := fun A => h.val A
    condition := _ -- from h.property
  }
  left_inv := _  -- uniqueness from initiality
  right_inv := _ -- by construction
```

Wait -- the cowedge here is a mathlib `Cowedge P` where
`P : Cᵒᵖ ⥤ C ⥤ D`. The cowedge legs are `π A : P(A,A) → pt`.
A morphism `f : pt → Y` post-composes to give `π A ≫ f : P(A,A) → Y`.

The forward map sends `f` to the family
`fun A => cw.π A ≫ f`. The backward map uses the universal
property: given a dinatural family `h : ∀ A, P(A,A) → Y`, we
form a cowedge at `Y` and use initiality to get `cw.pt → Y`.

NOTE: We need to check whether mathlib's `Cowedge` has the right
interface for this (it's a `Multicofork`). The legs are accessed via
`Cowedge.π` (or `Multicofork.π`). To construct a new cowedge from
a dinatural family, we need `Cowedge.mk` which requires the family
and the dinaturality proof. Then `IsInitial.desc` or `hcw.from`
gives the universal map.

### Step 3: Build and verify

Run: `lake build`
Expected: Clean build, no warnings.

---

## Task 3: End Formula for GExtFunctor via Copower Profunctor

**Files:**
- Create: `GebLean/MendlerLambekEndPower.lean`
- Modify: `GebLean.lean` (add import)

This task composes the copower-profunctor coend (task 1) with the
coend-end duality (task 2) to express `GExtObj(pt)` via an end.

### Step 1: Create the file with imports

```lean
import GebLean.RestrictedCoendAsColimit
import GebLean.Utilities.EndsAndCoends

namespace GebLean
```

### Step 2: Apply coend-end duality to copower-profunctor coend

```lean
variable {C : Type u} [Category.{v} C]
  [HasCopowers C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

def gExtCopowerEndEquiv (pt : C) (Y : C) :
    (CopowerGExtObj G pt ⟶ Y) ≃
      typeEnd (homSliceProf
        (copowerProf (HomToProf pt) G) Y) :=
  cowedgeHomEndEquiv
    (copowerProf (HomToProf pt) G)
    (copowerCoend G pt)
    (copowerCoendIsInitial G pt)
    Y
```

This gives:
`Hom(G^e_cp(pt), Y) ≃ ∫_A Hom(copowerProf(HomToProf(pt), G)(A,A), Y)`

where `copowerProf(HomToProf(pt), G)(A,A) = (A → pt) . G(A,A)`.

### Step 3: Build and verify

Run: `lake build`
Expected: Clean build.

---

## Task 4: Replace Copower with Power Inside the End

**Files:**
- Modify: `GebLean/MendlerLambekEndPower.lean`

### Step 1: Define the end-power profunctor

The profunctor `(A, B) ↦ Hom(G(A,B), Y^(A→pt))`:

```lean
def endPowerProf
    [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt Y : C) :
    Cᵒᵖ ⥤ C ⥤ Type v :=
  homSliceProf
    (copowerProf (HomToProf pt) G)
    Y
  -- Then compose with copowerPowerEquiv fiberwise
```

Wait -- we need to be more careful. The hom-slice profunctor gives:
`(A, B) ↦ Hom(copowerProf(HomToProf pt, G)(A,B), Y)`
`= Hom((A→pt) . G(A,B), Y)`

After applying `copowerPowerEquiv` (A→pt) G(A,B) Y:
`≃ Hom(G(A,B), Y^(A→pt))`

So we define:
```lean
def endPowerProf
    [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt Y : C) :
    Cᵒᵖ ⥤ C ⥤ Type v where
  obj A := {
    obj := fun B =>
      ((G.obj A).obj B ⟶
        HasPowers.power Y
          ((HomToProf pt).obj A).obj B))
    map := fun g f =>
      (G.obj A).map g ≫ f ≫
        HasPowers.mapIdx (· ≫ ·) -- ?
  }
  -- etc.
```

NOTE: The exact definition requires care with functoriality of
powers. `HasPowers.power Y S` is contravariant in `S` via
`HasPowers.mapIdx`. The `HomToProf(pt)(A,B) = (A → pt)` is
constant in `B`, which simplifies things. But it is contravariant
in `A` (via precomposition).

### Step 2: Prove the equivalence of profunctors

```lean
def copowerPowerProfEquiv
    [HasCopowers C] [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt Y : C)
    (A : Cᵒᵖ) (B : C) :
    (homSliceProf
      (copowerProf (HomToProf pt) G) Y).obj A).obj B ≃
    (endPowerProf G pt Y).obj A).obj B :=
  copowerPowerEquiv
    ((HomToProf pt).obj A).obj B)
    ((G.obj A).obj B) Y
```

### Step 3: Lift the fiberwise equivalence to an end equivalence

```lean
def endCopowerPowerEquiv
    [HasCopowers C] [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt Y : C) :
    typeEnd (homSliceProf
      (copowerProf (HomToProf pt) G) Y) ≃
    typeEnd (endPowerProf G pt Y) :=
  typeEnd.map _ _
    (copowerPowerProfNatIso G pt Y)
```

where `copowerPowerProfNatIso` is the natural isomorphism between
the two profunctors (fiberwise `copowerPowerEquiv`), and
`typeEnd.map` transports the end along a natural isomorphism.

NOTE: `typeEnd.map` exists in the codebase (EndsAndCoends.lean).
We need to verify it accepts a natural isomorphism (not just a
natural transformation) and produces an equivalence (not just a
map). If it only gives a map, we use `typeEnd.map` in both
directions.

### Step 4: Compose to get the final characterization

```lean
def gExtEndPowerEquiv
    [HasCopowers C] [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C)
    [HasAllCopowerProfCoends G]
    (pt Y : C) :
    (CopowerGExtObj G pt ⟶ Y) ≃
      typeEnd (endPowerProf G pt Y) :=
  (gExtCopowerEndEquiv G pt Y).trans
    (endCopowerPowerEquiv G pt Y)
```

This is the target result:
`Hom(G^e(pt), Y) ≃ ∫_A Hom(G(A,A), Y^(A→pt))`

### Step 5: Define the Mendler-Lambek end-power equivalence

```lean
def mendlerLambekEndPowerEquiv
    [HasCopowers C] [HasPowers C]
    (G : Cᵒᵖ ⥤ C ⥤ C)
    [HasAllCopowerProfCoends G] :
    MendlerAlgebra G ≌
      ConventionalAlgebra
        (CopowerGExtFunctor G) :=
  mendlerLambekCopowerEquiv G
```

The equivalence itself is `mendlerLambekCopowerEquiv` from task 1.
The new content is the characterization `gExtEndPowerEquiv` which
shows that the functor `CopowerGExtFunctor` is described by the
end-and-power formula.

### Step 6: Add import to GebLean.lean

Add `import GebLean.MendlerLambekEndPower` to `GebLean.lean`.

### Step 7: Build and verify

Run: `lake build` and `lake test`
Expected: Clean build, no warnings, tests pass.

---

## Execution Notes

### Dependencies
- Task 1 and Task 2 are independent and can be developed in
  parallel
- Task 3 requires both Task 1 and Task 2
- Task 4 requires Task 3

### Incremental Development
Per CLAUDE.md, develop one definition at a time. After each
definition, run `lake build` to check types. Use `_` (never
`sorry`) for holes to see goal types.

### Existing Utilities
- `isInitialOfEquivFunctor` (Category.lean:2487)
- `homRestrictedCopowerEquiv` (RestrictedCoendAsColimit.lean:960)
- `typeCoend.endEquiv` (EndsAndCoends.lean:1641)
- `typeEnd.map` (EndsAndCoends.lean)
- `copowerPowerEquiv` (PowersAndCopowers.lean:719)
- `copowerPowerAdjunction` (PowersAndCopowers.lean:771)
- `HasCopowers.bimap` (PowersAndCopowers.lean)
