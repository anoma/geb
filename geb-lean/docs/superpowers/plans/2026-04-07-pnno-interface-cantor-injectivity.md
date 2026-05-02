# PNNO Interface and Cantor Pairing Injectivity

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Show that a PBTO gives a PNNO (via
right-spine nats), use the PNNO interface to prove
Cantor pairing injectivity, and make `treeEqG_ββ`
unconditional.

**Architecture:** Define an NNO recursion wrapper
(`nnoElim`) around `p.elim` that normalizes via
`toRSpineNat`, prove its computation and uniqueness
rules, then use it to prove the Cantor unpairing
section property and `NatEqCantorPair`.  The
paramorphism form (`paraElim` restricted to NNO
algebras) provides access to the predecessor at each
step.

**Tech Stack:** Lean 4, mathlib (category theory),
`HasPBTO`, `HasChosenFiniteProducts`

---

## File Structure

- Modify: `GebLean/NatNNO.lean` (new file, NNO
  interface + Cantor injectivity)
- Modify: `GebLean/TreeEqGoedel.lean` (remove `hCP`
  from `treeEqG_ββ`)
- Modify: `GebLean.lean` (add import)

`NatNNO.lean` imports `NatArith` and `TreeLogic` and
builds the NNO theory.

## Existing Infrastructure

In `NatArith.lean`:
- `natSucc`, `natPred`, `natPred_natSucc`
- `toRSpineNat`, `toRSpineNat_ℓ`, `toRSpineNat_β`,
  `toRSpineNat_idem`
- `natSucc_toRSpineNat_comm`
- `natEq_toRSpineNat`, `natEq_succ_cancel`
- `natPlus_cancel_left` (unrestricted)
- `cantorPair`, `cantorPair_succ_fst`,
  `cantorPair_ℓℓ`
- `cantorNextPair`, `cantorNextPair_ℓ`,
  `cantorNextPair_β`
- `cantorUnpairHelper`, `cantorUnpairHelper_cantorPair`
- `cantorPair_cantorNextPair`
- `natTri_natSucc`, `natTri_isLeafEndo`
- `natPlus_ℓ_left_eq_toRSpineNat`,
  `natPlus_comm_rsn`

In `TreeLogic.lean`:
- `paraElim`, `paraElim_ℓ`, `paraElim_β`,
  `paraElim_uniq`
- `isLeafEndo`, `treeIte`, `boolAnd`

In `TreeEqGoedel.lean`:
- `NatEqCantorPair` (definition), `treeEqG_ββ`
  (currently takes `hCP`)

---

### Task 1: NNO Recursion Interface

**Files:**
- Create: `GebLean/NatNNO.lean`

Define the NNO eliminator as a thin wrapper around
`p.elim` that normalizes via `toRSpineNat`, and prove
its computation and uniqueness rules.

- [ ] **Step 1: Create NatNNO.lean with header**

```lean
import GebLean.NatArith
import GebLean.TreeLogic

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]
```

- [ ] **Step 2: Define `nnoElim`**

```lean
def nnoElim {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpProd A p.T ⟶ X :=
  cfpMap (𝟙 A) toRSpineNat ≫
    p.elim f (cfpSnd X X ≫ g)
```

The NNO fold: normalize the tree argument, then
apply the PBTO fold with step `cfpSnd ≫ g` (which
discards the left-child result and applies `g` to the
right-child result).

- [ ] **Step 3: Build and verify**

Run: `lake build`
Expected: success

- [ ] **Step 4: Prove `nnoElim_ℓ`**

```lean
theorem nnoElim_ℓ {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpInsertSnd p.ℓ A ≫ nnoElim f g = f := by
  unfold nnoElim
  rw [← Category.assoc]
  have : cfpInsertSnd p.ℓ A ≫
      cfpMap (𝟙 A) toRSpineNat =
    cfpInsertSnd p.ℓ A := by
    unfold cfpInsertSnd
    rw [cfpLift_cfpMap, Category.id_comp,
      Category.assoc, toRSpineNat_ℓ]
  rw [this, p.elim_ℓ]
```

- [ ] **Step 5: Prove `nnoElim_s`**

The step equation: `nnoElim(a, natSucc(n)) =
g(nnoElim(a, n))`.

```lean
theorem nnoElim_s {A X : C}
    (f : A ⟶ X) (g : X ⟶ X) :
    cfpMap (𝟙 A) natSucc ≫ nnoElim f g =
    nnoElim f g ≫ g := by
  unfold nnoElim
  -- cfpMap (𝟙) natSucc ≫ cfpMap (𝟙) toRSN
  -- = cfpMap (𝟙) (natSucc ≫ toRSN)
  -- = cfpMap (𝟙) (toRSN ≫ natSucc)
  --     (by natSucc_toRSpineNat_comm)
  -- = cfpMap (𝟙) toRSN ≫ cfpMap (𝟙) natSucc
  -- Then cfpMap (𝟙) natSucc ≫ p.elim f (cfpSnd ≫ g)
  -- reduces via the PBTO β step
  -- (natSucc = cfpLift (F ≫ ℓ) (𝟙) ≫ β, left
  -- child is ℓ, so cfpLiftAssoc gives
  -- (f(a), elim(a,n)), cfpSnd ≫ g gives
  -- g(elim(a,n))).
  sorry -- proof uses natSucc_toRSpineNat_comm,
        -- cfpMap_comp, p.elim_β, and algebraic
        -- manipulation of the natSucc structure
```

The proof strategy:
1. `cfpMap (𝟙) natSucc ≫ cfpMap (𝟙) toRSN =
   cfpMap (𝟙) (natSucc ≫ toRSN) =
   cfpMap (𝟙) (toRSN ≫ natSucc)` (by
   `natSucc_toRSpineNat_comm`)
2. `= cfpMap (𝟙) toRSN ≫ cfpMap (𝟙) natSucc`
   (split)
3. Expand `natSucc = cfpLift (F ≫ ℓ) (𝟙) ≫ β` and
   apply `p.elim_β`
4. The `cfpLiftAssoc` step with left child = ℓ gives
   `(f(a), elim(a, n))`, then `cfpSnd ≫ g` gives
   `g(elim(a, n))`

- [ ] **Step 6: Prove `nnoElim_uniq`**

Uniqueness among morphisms that are
toRSpineNat-invariant.

```lean
theorem nnoElim_uniq {A X : C}
    (f : A ⟶ X) (g : X ⟶ X)
    (φ : cfpProd A p.T ⟶ X)
    (hℓ : cfpInsertSnd p.ℓ A ≫ φ = f)
    (hs : cfpMap (𝟙 A) natSucc ≫ φ = φ ≫ g)
    (hnorm : cfpMap (𝟙 A) toRSpineNat ≫ φ = φ) :
    φ = nnoElim f g := by
  sorry -- Show cfpMap (𝟙) toRSN ≫ φ satisfies
        -- PBTO base+step, then use p.elim_uniq.
        -- hnorm collapses φ to its normalized form.
```

- [ ] **Step 7: Build and verify**

Run: `lake build`
Expected: success (after filling in sorrys)

- [ ] **Step 8: Commit**

```bash
git add GebLean/NatNNO.lean
git commit -m "feat: NNO recursion interface from PBTO"
```

---

### Task 2: Cantor Unpairing Section Property

**Files:**
- Modify: `GebLean/NatNNO.lean`

Prove that pair-then-unpair recovers the normalized
components: `cantorPair ≫ unpair = cfpMap toRSN toRSN`.

The proof uses double induction:
- Outer induction on `a` (first arg of cantorPair)
  using `cantorPair_succ_fst`
- Inner induction on `b` for the base case `a = ℓ`,
  using the outer IH at `(b', ℓ)` for the inner step

- [ ] **Step 1: Define `cantorUnpair`**

```lean
def cantorUnpair : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    cantorUnpairHelper
```

- [ ] **Step 2: Define component projections**

```lean
def cantorUnpairFst : p.T ⟶ p.T :=
  cantorUnpair ≫ cfpFst p.T p.T

def cantorUnpairSnd : p.T ⟶ p.T :=
  cantorUnpair ≫ cfpSnd p.T p.T
```

- [ ] **Step 3: Prove `cantorUnpair_ℓ`**

`cantorUnpair(ℓ) = (ℓ, ℓ)`.

```lean
theorem cantorUnpair_ℓ :
    p.ℓ ≫ cantorUnpair =
    cfpLift p.ℓ p.ℓ := by
  sorry -- unfold, use cantorUnpairHelper base case
```

- [ ] **Step 4: Prove `cantorUnpair_natSucc`**

`cantorUnpair(natSucc(n)) =
cantorNextPair(cantorUnpair(n))`.

```lean
theorem cantorUnpair_natSucc :
    natSucc ≫ cantorUnpair =
    cantorUnpair ≫ cantorNextPair := by
  sorry -- unfold natSucc, use cantorUnpairHelper
        -- step equation
```

- [ ] **Step 5: Prove helper
  `cantorNextPair_nonzero_snd`**

When the second component is `natSucc(y)` (non-zero),
`cantorNextPair` advances: `cantorNextPair(x,
natSucc(y)) = (natSucc(x), y)`.

```lean
theorem cantorNextPair_nonzero_snd :
    cfpLift (cfpFst p.T p.T)
      (cfpSnd p.T p.T ≫ natSucc) ≫
      cantorNextPair =
    cfpLift
      (cfpFst p.T p.T ≫ natSucc)
      (cfpSnd p.T p.T) := by
  sorry -- use cantorNextPair_β on the second
        -- component (natSucc = cfpLift ... ≫ β)
```

- [ ] **Step 6: Prove the section property**

The main theorem: `cantorPair ≫ cantorUnpair =
cfpMap toRSpineNat toRSpineNat`.

Proof by `nnoElim_uniq` (or `p.elim_uniq`) on the
first argument `a`, with `b` as parameter.

**Outer step** (`a → succ(a)`): uses
`cantorPair_succ_fst` to reduce to
`succ(cantorPair(a, succ(b)))`, then
`cantorUnpair_natSucc` and
`cantorNextPair_nonzero_snd` (since `toRSN(succ(b))`
is non-zero), giving
`(natSucc(toRSN(a)), toRSN(b)) =
(toRSN(succ(a)), toRSN(b))`.

**Outer base** (`a = ℓ`): reduces to
`cantorUnpair(natTri(toRSN(b))) = (ℓ, toRSN(b))`.
Proved by inner induction on `b`:
- Inner base: `natTri(ℓ) = ℓ`,
  `cantorUnpair(ℓ) = (ℓ, ℓ)`. Done.
- Inner step: `natTri(succ(b')) =
  succ(natPlus(b', natTri(b')))`.  By commutativity
  on rsn: `natPlus(b', natTri(b')) =
  natPlus(natTri(b'), b') = cantorPair(b', ℓ)`.
  Then `succ(cantorPair(b', ℓ))`:
  `cantorUnpair(succ(cantorPair(b', ℓ))) =
  cantorNextPair(cantorUnpair(cantorPair(b', ℓ)))`.
  By outer IH at `(b', ℓ)`:
  `= cantorNextPair(toRSN(b'), ℓ)`.
  By `cantorNextPair_ℓ`:
  `= (ℓ, natSucc(toRSN(b')))
  = (ℓ, toRSN(succ(b')))`.

```lean
theorem cantorPair_cantorUnpair :
    cantorPair ≫ cantorUnpair =
    cfpMap toRSpineNat
      (toRSpineNat : p.T ⟶ p.T) := by
  sorry -- double induction as described above
```

- [ ] **Step 7: Build and verify**

Run: `lake build`

- [ ] **Step 8: Commit**

```bash
git add GebLean/NatNNO.lean
git commit -m \
  "feat: Cantor unpairing section property"
```

---

### Task 3: NatEqCantorPair and Unconditional ββ

**Files:**
- Modify: `GebLean/NatNNO.lean`
- Modify: `GebLean/TreeEqGoedel.lean`

Use the section property to prove
`NatEqCantorPair`, then remove the `hCP` hypothesis
from `treeEqG_ββ`.

- [ ] **Step 1: Prove forward direction helper**

Congruence: equal components give equal pairings.

```lean
theorem natEq_cantorPair_compat :
    cfpLift
      (cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpFst p.T p.T)
        (cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpFst p.T p.T) ≫ natEq)
      (cfpLift
        (cfpFst (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T)
        (cfpSnd (cfpProd p.T p.T)
          (cfpProd p.T p.T) ≫
          cfpSnd p.T p.T) ≫ natEq) ≫
      boolAnd ≫
      boolAnd_with
        (cfpMap cantorPair cantorPair ≫ natEq) =
    cfpLift (...) (...) ≫ boolAnd := by
  sorry
```

The forward direction uses: cantorPair is
compatible with natEq, meaning
`boolAnd(natEq(a,c), natEq(b,d))` implies
`natEq(CP(a,b), CP(c,d))`.  Proved by showing
cantorPair preserves natEq equality (it is built
from natPlus, natTri which are morphisms, so equal
inputs give equal outputs).

- [ ] **Step 2: Prove reverse direction helper**

Injectivity: equal pairings give equal components.
Uses section property.

```lean
theorem natEq_cantorPair_inject :
    cfpMap cantorPair cantorPair ≫ natEq ≫
      boolAnd_with
        (cfpLift (...) (...) ≫ boolAnd) =
    cfpMap cantorPair cantorPair ≫ natEq := by
  sorry
```

The reverse direction uses:
1. `cantorPair ≫ cantorUnpair =
   cfpMap toRSN toRSN` (section property)
2. If `natEq(CP(a,b), CP(c,d)) = treeTrue`,
   then `unpair` gives
   `(toRSN(a), toRSN(b)) = (toRSN(c), toRSN(d))`.
3. Component-wise natEq via `natEq_toRSpineNat`.

- [ ] **Step 3: Prove `NatEqCantorPair`**

Combine forward and reverse directions.

```lean
theorem natEqCantorPair_proof :
    NatEqCantorPair (p := p) C := by
  sorry -- combine compat and inject via
        -- boolAnd bidirectional
```

- [ ] **Step 4: Make `treeEqG_ββ` unconditional**

In `GebLean/TreeEqGoedel.lean`, change the
signature from:

```lean
theorem treeEqG_ββ
    (hCP : NatEqCantorPair (p := p) C) :
```

to:

```lean
theorem treeEqG_ββ :
```

And replace `hCP` in the proof body with
`natEqCantorPair_proof`.

- [ ] **Step 5: Add import to GebLean.lean**

```lean
import GebLean.NatNNO
```

- [ ] **Step 6: Build and test**

Run: `lake build && lake test`

- [ ] **Step 7: Commit**

```bash
git add GebLean/NatNNO.lean \
  GebLean/TreeEqGoedel.lean GebLean.lean
git commit -m \
  "feat: NatEqCantorPair unconditional, \
treeEqG_ββ unconditional"
```

---

## Self-Review

**Spec coverage:**
- NNO interface from PBTO: Task 1
- Section property: Task 2
- NatEqCantorPair + unconditional ββ: Task 3

**Placeholder scan:** Tasks use `sorry` as
implementation placeholders with proof strategies
documented alongside.  The exact tactic proofs depend
on intermediate goal shapes that must be discovered
during implementation.

**Type consistency:** `nnoElim`, `cantorUnpair`,
`cantorUnpairFst`, `cantorUnpairSnd` defined in Task
1-2; used consistently in Task 3.
`NatEqCantorPair` defined in `TreeEqGoedel.lean`;
proved in `NatNNO.lean`; referenced in modified
`treeEqG_ββ`.
