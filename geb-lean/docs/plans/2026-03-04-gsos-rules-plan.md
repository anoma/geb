# GSOS Rules and Operational Monad Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

**Goal:** Define abstract GSOS rules (E1) and construct the
polynomial-specific induced distributive law and operational
monad (E2).

**Architecture:** E1 defines `GSOSRule` as a natural
transformation in a general categorical setting
(`Utilities/GSOSRule.lean`).  E2 instantiates this for
polynomial endofunctors on `Over X`, constructing the induced
`DistributiveLaw` via a parameterized fold (structural
recursion with accumulators) and `polyCofixUnfold`, then
obtains the operational monad via `liftedMonad`
(`PolyGSOS.lean`).

**Tech Stack:** Lean 4, mathlib (CategoryTheory), GebLean
polynomial infrastructure.

---

## Task 1: GSOSRule Definition (General)

**Files:**

- Create: `GebLean/Utilities/GSOSRule.lean`
- Modify: `GebLean.lean` (add import)

### Step 1-1: Create file with imports and namespace

Create `GebLean/Utilities/GSOSRule.lean` with:

```lean
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace GebLean

open CategoryTheory Limits

universe v u
```

Build: `lake build GebLean.Utilities.GSOSRule`
Expected: compiles with no warnings.

### Step 1-2: Define idBehaviorFunctor

The functor `X ↦ X × B(X)` on a category with binary
products.

```lean
variable {C : Type u} [Category.{v} C]
  [HasBinaryProducts C]

def idBehaviorFunctor (B : C ⥤ C) : C ⥤ C where
  obj := fun X => X ⨯ B.obj X
  map := fun f => prod.map f (B.map f)
  map_id := fun X => by
    simp [prod.map, prod.lift]
    _
  map_comp := fun f g => by
    simp [prod.map, prod.lift]
    _
```

Build after implementing.  The `map_id` and `map_comp`
proofs require the product universal property.  Use
`prod.hom_ext` and `prod.lift_fst`/`prod.lift_snd` lemmas
from mathlib, or `ext` tactics.  Fill in underscores one
at a time.

### Step 1-3: Define GSOSRule structure

```lean
@[ext]
structure GSOSRule
    (Sigma : C ⥤ C) (B : C ⥤ C) (T : Monad C) where
  rule :
    idBehaviorFunctor B ⋙ Sigma ⟶
    T.toFunctor ⋙ B
```

Build: `lake build GebLean.Utilities.GSOSRule`
Expected: compiles.

### Step 1-4: Add import to GebLean.lean

Add `import GebLean.Utilities.GSOSRule` to `GebLean.lean`
(after the `DistributiveLaw` import, around line 58).

Build: `lake build` and `lake test`
Expected: full build succeeds, all tests pass.

### Step 1-5: Commit

Commit with message describing E1: the `GSOSRule` definition
and `idBehaviorFunctor`.

---

## Task 2: Polynomial GSOS Rule Type

**Files:**

- Create: `GebLean/PolyGSOS.lean`
- Modify: `GebLean.lean` (add import)

### Step 2-1: Create file with imports

```lean
import GebLean.PolyDistributiveLaw
import GebLean.Utilities.GSOSRule
import GebLean.Utilities.LambdaBialgebra

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}
```

Build: `lake build GebLean.PolyGSOS`
Expected: compiles.

### Step 2-2: Define the id-behavior functor for polynomial Q

The functor `A ↦ overPullback A (polyEndoEval Q A)` on
`Over X`, using the constructive `overPullback` from
`Slice.lean` rather than assuming `HasBinaryProducts`.

```lean
def polyIdBehaviorObj (Q : PolyEndo X)
    (A : Over X) : Over X :=
  overPullback A ((polyEndoFunctor X Q).obj A)

def polyIdBehaviorMap (Q : PolyEndo X)
    {A B : Over X} (f : A ⟶ B) :
    polyIdBehaviorObj Q A ⟶
    polyIdBehaviorObj Q B :=
  overPullbackMap f ((polyEndoFunctor X Q).map f)

def polyIdBehaviorFunctor (Q : PolyEndo X) :
    Over X ⥤ Over X where
  obj := polyIdBehaviorObj Q
  map := polyIdBehaviorMap Q
  map_id := _
  map_comp := _
```

Fill in `map_id` and `map_comp` proofs.  These should
follow from `overPullbackMap` functoriality.  Use
`Over.OverMorphism.ext` and `funext`.

Build after each proof.

### Step 2-3: Define PolyGSOSRule

```lean
structure PolyGSOSRule (P Q : PolyEndo X) where
  rule :
    polyIdBehaviorFunctor Q ⋙
      polyEndoFunctor X P ⟶
    (polyFreeMonad X P).toFunctor ⋙
      polyEndoFunctor X Q
```

This specializes `GSOSRule` to polynomial endofunctors on
`Over X` using the constructive product.  It wraps a natural
transformation
`P(A ×_X Q(A)) → Q(T_P(A))`.

Build: `lake build GebLean.PolyGSOS`

### Step 2-4: Add import and commit

Add `import GebLean.PolyGSOS` to `GebLean.lean` (after
`PolyDistributiveLaw`).

Build: `lake build` and `lake test`
Commit.

---

## Tasks 3-8: Done

Tasks 3-8 (product algebra, parameterized fold, distributive
law morphism, counit, unit, naturality) are all complete.
See `.session/workstreams/gsos-distributive-law.md` for full
details.

---

## Task 9: Coherence -- Comultiplication

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

Prove:
`polyFreeMap ... (polyCoalgUnit Q ...) ≫
  polyGSOSDistLawMor (polyCofreeCarrier A Q) P Q rho ≫
  polyCofreeMap ... (polyGSOSDistLawMor A P Q rho) =
  polyGSOSDistLawMor A P Q rho ≫
  polyCoalgUnit Q ...`

Follow `polyDistLaw_comul` proof pattern.

---

## Task 10: Coherence -- Multiplication

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

Prove:
`polyFreeCounitFold P ... ≫
  polyGSOSDistLawMor A P Q rho =
  polyFreeMap ... (polyGSOSDistLawMor A P Q rho) ≫
  polyGSOSDistLawMor (polyFreeMCarrier A P) P Q rho ≫
  polyCofreeMap ...
    (polyFreeCounitFold P ...)`

Follow `polyDistLaw_mul` proof pattern.  This is typically
the longest coherence proof.

---

## Task 11: Package as DistributiveLaw

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

### Step 11-1: Natural transformation wrapper

```lean
def polyGSOSDistLawNatApp
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    ((polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).obj A ⟶
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor).obj A :=
  polyGSOSDistLawMor A P Q rho

def polyGSOSDistLawNat
    (P Q : PolyEndo X) (rho : PolyGSOSRule P Q) :
    (polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor ⟶
    (polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor where
  app := fun A => polyGSOSDistLawNatApp A P Q rho
  naturality := fun {A B} f =>
    polyGSOSDistLaw_naturality A B P Q rho f
```

### Step 11-2: DistributiveLaw instance

```lean
def polyGSOSDistLaw
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    DistributiveLaw
      (polyFreeMonad X P)
      (polyCofreeComonad X Q) where
  dist := polyGSOSDistLawNat P Q rho
  unit := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyFreeMonad_eta_eq,
      polyCofreeComonad_map_eq]
    exact polyGSOSDistLaw_unit A P Q rho
  counit := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyCofreeComonad_eps_eq,
      polyFreeMonad_map_eq]
    exact polyGSOSDistLaw_counit A P Q rho
  mul := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyFreeMonad_mu_eq,
      polyFreeMonad_map_eq,
      polyCofreeComonad_map_eq]
    exact polyGSOSDistLaw_mul A P Q rho
  comul := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyCofreeComonad_delta_eq,
      polyCofreeComonad_map_eq,
      polyFreeMonad_map_eq]
    exact polyGSOSDistLaw_comul A P Q rho
```

Build: `lake build GebLean.PolyGSOS`

### Step 11-3: Commit

---

## Task 12: Operational Monad

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

### Step 12-1: Define operational monad

```lean
def polyGSOSOperationalMonad
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    Monad (polyCofreeComonad X Q).Coalgebra :=
  liftedMonad (polyGSOSDistLaw P Q rho)
```

This reuses `liftedMonad` from
`Utilities/LambdaBialgebra.lean`.

Build: `lake build GebLean.PolyGSOS`

### Step 12-2: Commit

---

## Task 13: Canonical GSOS Rule (P = Q)

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

### Step 13-1: Define canonical GSOS rule

When `P = Q`, the canonical GSOS rule sends
`P(A ×_X P(A)) → P(T_P(A))` by the following procedure.
At position `(p, children)` where each child is a pair
`(a, q) : A ×_X P(A)`:

- Return position `p`
- For each direction `d` of `p`, embed the `P(A)`
  component `q_d` into `T_P(A)` via `T_P` applied to
  the inclusion of `P`-operations

```lean
def polyCanonicalGSOSRule (P : PolyEndo X) :
    PolyGSOSRule P P where
  rule := _
```

The natural transformation is defined pointwise using
the same structure as `polyFreeMCoalgStrAt` (which defines
the canonical P-coalgebra on `T_P(C)` by using `k` on
leaves and identity on nodes).

### Step 13-2: Show canonical rule induces polyDistributiveLaw

```lean
theorem polyCanonicalGSOS_eq_polyDistLaw
    (P : PolyEndo X) :
    polyGSOSDistLaw P P (polyCanonicalGSOSRule P) =
    polyDistributiveLaw P := by
  _
```

This requires showing the two anamorphisms agree by
uniqueness: both are the unique coalgebra morphism from the
same `polyScale`-coalgebra.  Use
`polyCofixUnfold_unique` or `PolyCoalg` terminal property.

Build: `lake build GebLean.PolyGSOS`

### Step 13-3: Commit

---

## Task 14: Final Bookkeeping

**Files:**

- Modify: `GebLean.lean`
- Modify:
  `.session/workstreams/polynomial-algebra-coalgebra-combinators.md`

### Step 14-1: Verify full build

```bash
lake build && lake test
```

Expected: all green, no warnings.

### Step 14-2: Update workstream

Mark E1 and E2 as completed in the workstream file.
Add notes about the `PolyGSOSRule` structure, the
parameterized fold construction, and the canonical rule
connection.

### Step 14-3: Commit

---

## Proof Strategy Notes

The coherence proofs (Tasks 6-10) follow the same patterns
as `PolyDistributiveLaw.lean`.  Refer to:

- `polyDistLaw_counit` (lines 280-294) for counit
- `polyDistLaw_unit` (lines 431-480) for unit
- `polyDistLaw_naturality` (lines 906-940) for naturality
- `polyDistLaw_comul` (lines 1471-1500) for comultiplication
- `polyDistLaw_mul` (lines 1851-2410) for multiplication

Recurring techniques:

1. `Over.OverMorphism.ext` + `funext` to reduce to
   pointwise equality
2. `simp only [...]` with definition unfoldings
3. `apply Sigma.ext` + `· rfl` / `· simp [heq_eq_eq]`
   for sigma-type equality
4. `polyCofixUnfold_precomp` and `polyCofixUnfold_unique`
   for anamorphism equalities
5. Induction on `PolyFreeM` trees for the multiplication
   coherence
6. Factor out helper lemmas when proofs grow beyond
   ~30 lines (per CLAUDE.md guidelines)
7. Use underscores to check goal types at each step
