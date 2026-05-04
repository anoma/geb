# natEq Transitivity + ElegantPairing Injectivity

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Prove `natEq` transitivity, then define
Szudzik's ElegantPairing, prove its injectivity,
and use it to make `treeEqG_ββ` unconditional.

**Architecture:** natEq transitivity via
`isLeafEndo_natTruncSub_mono` + `natTruncSub_assoc`.
ElegantPairing via `iteBranches` conditional dispatch
on `isLeafEndo(natTruncSub(x, y))`.  Injectivity via
integer square root (`isqrt`) band property + the
two-phase level decomposition (column walk = 1D fold
on x with fixed y; row walk = 1D fold on y with
fixed x).

**Tech Stack:** Lean 4, `HasPBTO`,
`HasChosenFiniteProducts`, `nnoElim`

---

## Current State (start of next session)

### Files

- `GebLean/NatArith.lean` (~4500 lines): Cantor
  pairing, `natTruncSub`, `natEq`, `natPlus`,
  `isLeafEndo`, `toRSpineNat`, all computation and
  cancellation lemmas.
- `GebLean/NatNNO.lean` (~2128 lines): NNO
  interface (`nnoElim` + rules), Cantor unpairing,
  `natTruncSub_natPlus_cancel`,
  `natTruncSub_assoc`, `natEq_symm`,
  `natEq_eq_boolAnd_natTruncSub`,
  `isLeafEndo_natPred_mono`, triRoot infrastructure.
- `GebLean/TreeGoedel.lean` (~620 lines):
  `treeToNat` (Cantor-based), `treeEqG`.
- `GebLean/TreeEqGoedel.lean` (~615 lines):
  `treeEqG_ββ` (takes `hCP : NatEqCantorPair`).

### Key proved lemmas

```
-- NatNNO.lean
nnoElim_ℓ, nnoElim_s, nnoElim_uniq
natEq_symm : cfpSwap ≫ natEq = natEq
natEq_eq_boolAnd_natTruncSub :
  natEq = cfpLift natTruncSub
    (cfpSwap ≫ natTruncSub) ≫ boolAnd
natTruncSub_assoc :
  cfpLift (natTruncSub) (cfpSnd ≫ natPlus) ≫
    natTruncSub =
  cfpAssocSnd ≫ natTruncSub
  -- (x-y)-z = x-(y+z)
natTruncSub_natSucc_second :
  cfpMap (𝟙) natSucc ≫ natTruncSub =
    natTruncSub ≫ natPred
isLeafEndo_natPred_mono :
  cfpLift isLeafEndo (natPred ≫ isLeafEndo) ≫
    boolAnd = isLeafEndo
natTruncSub_natPlus_cancel :
  cfpLift natPlus (cfpSnd) ≫ natTruncSub = cfpFst

-- NatArith.lean
natEq_succ_cancel, natEq_toRSpineNat
natEq_refl, natEq_bool
natPlus_cancel_left (unrestricted)
natPlus_cancel_right
natTruncSub_ℓ_left : natTruncSub(ℓ, c) = ℓ
natPlus_isLeafEndo_eq_boolAnd :
  natPlus ≫ isLeafEndo = boolAnd

-- TreeLogic.lean
boolAnd_fst_proj, boolAnd_snd_proj, boolAnd_comm
boolAnd_ℓ_right, boolAnd_β_right
boolAnd_treeFalse_left
iteBranches_ℓ, iteBranches_β
isLeafEndo_ℓ, isLeafEndo_β, isLeafEndo_idem
```

---

### Task 1: Complete natEq Transitivity

**Files:**
- Modify: `GebLean/NatNNO.lean`

#### Lemma 2: isLeafEndo_natTruncSub_mono

```lean
theorem isLeafEndo_natTruncSub_mono :
    cfpLift (cfpFst p.T p.T ≫ isLeafEndo)
      (natTruncSub ≫ isLeafEndo) ≫ boolAnd =
    cfpFst p.T p.T ≫ isLeafEndo
```

Says: `boolAnd(isLeafEndo(w),
isLeafEndo(natTruncSub(w, c))) = isLeafEndo(w)`.

**Proof by `p.elim_uniq` on `w` (FIRST argument),
with `c` as parameter.**  This is the crux: fold on
`w`, NOT on `c`.  Swap via `cfpSwap` to put `w` in
the fold position.

- [ ] **Step 1:** Show both sides, after
  `cfpSwap`, equal
  `p.elim (cfpTerminalFrom T ≫ ℓ)
    (cfpTerminalFrom (T × T) ≫ treeFalse)`.
  This is the fold that gives `ℓ` at leaf and
  `treeFalse` at any branch — i.e.,
  `cfpSnd T T ≫ isLeafEndo` (after the swap puts
  `w` in the second position).

- [ ] **Step 2:** Base case (w = ℓ):
  `boolAnd(isLeafEndo(ℓ),
    isLeafEndo(natTruncSub(ℓ, c))) =
  boolAnd(ℓ, isLeafEndo(ℓ)) = boolAnd(ℓ, ℓ) = ℓ`.
  Uses `natTruncSub_ℓ_left` (natTruncSub(ℓ, c) = ℓ
  for all c) and `isLeafEndo_ℓ`.
  RHS: `isLeafEndo(ℓ) = ℓ`. Match. ✓

- [ ] **Step 3:** β-step (w = β(l, r)):
  LHS = `boolAnd(treeFalse, ...) = treeFalse`
  (by `boolAnd_treeFalse_left` after
  `isLeafEndo_β`).
  RHS = `isLeafEndo(β(l,r)) = treeFalse`.
  Both = `treeFalse`. ✓
  The `p.elim_uniq` step function is
  `cfpTerminalFrom ≫ treeFalse`.

- [ ] **Step 4:** Apply `p.elim_uniq` to conclude.
  May need `swap_isLeafEndo_boolAnd_elim` (already
  proved helper) or prove directly via the swap +
  p.elim_uniq pattern.

- [ ] **Step 5:** Build and verify. `lake build`.

#### Lemma 3: leq_trans

≤-transitivity: `(x ≤ y) ∧ (y ≤ z) → (x ≤ z)`.

```lean
theorem leq_trans :
    cfpLift
      (cfpLift (proj_x) (proj_y) ≫
        natTruncSub ≫ isLeafEndo)
      (cfpLift (proj_y) (proj_z) ≫
        natTruncSub ≫ isLeafEndo) ≫
      boolAnd ≫
      cfpLift (𝟙 p.T)
        (cfpLift (proj_x) (proj_z) ≫
          natTruncSub ≫ isLeafEndo) ≫
      boolAnd =
    [LHS without the last boolAnd]
```

(Where `proj_x = cfpFst T (T×T)`,
`proj_y = cfpSnd T (T×T) ≫ cfpFst T T`,
`proj_z = cfpSnd T (T×T) ≫ cfpSnd T T`.)

**Proof using `natTruncSub_assoc` +
`isLeafEndo_natTruncSub_mono`:**

- [ ] **Step 1:** From the hypothesis
  `isLeafEndo(natTruncSub(x, y)) = ℓ`, derive
  `isLeafEndo(natTruncSub(natTruncSub(x, y),
    natTruncSub(z, y))) = ℓ`
  via `isLeafEndo_natTruncSub_mono`.

- [ ] **Step 2:** By `natTruncSub_assoc`:
  `natTruncSub(natTruncSub(x, y),
    natTruncSub(z, y)) =
  natTruncSub(x, natPlus(y, natTruncSub(z, y)))`.

- [ ] **Step 3:** Show
  `isLeafEndo(natTruncSub(x,
    natPlus(y, natTruncSub(z, y))))` implies
  `isLeafEndo(natTruncSub(x, z))`.
  This requires: `natPlus(y, natTruncSub(z, y)) ≥ z`
  (always true), so subtracting more gives a
  smaller-or-equal result, hence still zero.
  Use `isLeafEndo_natTruncSub_mono` on the
  second argument: from
  `isLeafEndo(natTruncSub(x, a))` with
  `a = natPlus(y, z-y)`, derive
  `isLeafEndo(natTruncSub(x, a'))` for
  `a' ≤ a` ... wait, this is the WRONG direction.

  **Alternative:** Show
  `natTruncSub(x, z) ≤ natTruncSub(x,
    natPlus(y, z-y))` directly. Since
  `natPlus(y, z-y) ≥ z`, by
  `natTruncSub_assoc`:
  `natTruncSub(x, natPlus(y, z-y)) =
  natTruncSub(natTruncSub(x, y), z-y)`.
  And `isLeafEndo(natTruncSub(x, y)) = ℓ`
  implies by `isLeafEndo_natTruncSub_mono`:
  `isLeafEndo(natTruncSub(natTruncSub(x,y),
    z-y)) = ℓ`.
  So `isLeafEndo(natTruncSub(x,
    natPlus(y, z-y))) = ℓ`.

  **Now:** We need to go from
  `isLeafEndo(natTruncSub(x, natPlus(y, z-y)))
  = ℓ` to
  `isLeafEndo(natTruncSub(x, z)) = ℓ`.
  Since `natPlus(y, z-y) ≥ z` (more subtraction),
  `natTruncSub(x, natPlus(y,z-y)) ≤
  natTruncSub(x, z)`.  **But zero for the
  smaller does NOT imply zero for the larger.**

  **Correct approach:** Factor differently.
  `natTruncSub(x, z)`:
  By `natTruncSub_assoc`:
  `= natTruncSub(natTruncSub(x, y),
    natTruncSub(z, y))`.
  Wait — `natTruncSub_assoc` says
  `(x-y)-c = x-(y+c)`.  Setting c = z-y:
  `(x-y)-(z-y) = x-(y+(z-y))`.  But the LHS
  is `natTruncSub(natTruncSub(x,y),
  natTruncSub(z,y))`, and the RHS is
  `natTruncSub(x, natPlus(y, natTruncSub(z,y)))`.

  We have `isLeafEndo` of the LHS = ℓ (from
  Lemma 2 applied to `natTruncSub(x,y)` with
  `c = natTruncSub(z,y)`).  By assoc,
  `isLeafEndo` of the RHS = ℓ.

  **Key:** The RHS equals
  `natTruncSub(x, natPlus(y, z-y))`,
  NOT `natTruncSub(x, z)`.  These differ when
  `natPlus(y, z-y) ≠ z`.  So we need the
  **reconstruction lemma**:
  `natPlus(y, natTruncSub(z, y)) = z`
  when `y ≤ z`.

  **Reconstruction lemma proof** (fold on y):

  - Base (y = ℓ):
    `natPlus(ℓ, natTruncSub(z, ℓ)) =
    natPlus(ℓ, z) = toRSN(z)`.
    `natEq(toRSN(z), z) = ℓ`
    (by `natEq_toRSpineNat` + `natEq_refl`).

  - Step (y → succ(y')):
    `natPlus(succ(y'),
      natTruncSub(z, succ(y'))) =
    succ(natPlus(y',
      natPred(natTruncSub(z, y'))))`.
    When `y' < z` (so `natTruncSub(z, y')` is a
    successor `succ(d)`):
    `natPred(succ(d)) = d`.
    `succ(natPlus(y', d))`.
    By IH: `natPlus(y', succ(d)) = z`.
    So `natPlus(y', d) = natPred(z)`.
    And `succ(natPred(z)) = z` when z is a
    successor (guaranteed by `y' < z` implying
    `z ≥ 1`).

  **Note:** The reconstruction lemma is
  CONDITIONAL on `y ≤ z`.  Express it as a
  `boolAnd`-gated equation.  The gating by
  `isLeafEndo(natTruncSub(y, z))` ensures the
  condition.

  **Alternatively:** Skip the reconstruction lemma
  and prove `leq_trans` by fold on one variable,
  using `isLeafEndo_natTruncSub_mono` and
  `natTruncSub_assoc`.  Multiple agents have
  attempted this — the fold on z using
  `natTruncSub_natSucc_second` is the most
  promising but requires chaining implications
  through `isLeafEndo_natPred_mono`.

- [ ] **Step 4:** Build and verify.

#### Lemma 4: natEq_trans

```lean
theorem natEq_trans : [transitivity equation]
```

From `leq_trans` (both directions) +
`natEq_eq_boolAnd_natTruncSub`:

- [ ] **Step 1:** Decompose `natEq(x, y)` and
  `natEq(y, z)` via `natEq_eq_boolAnd_natTruncSub`.
- [ ] **Step 2:** Extract the four ≤ conditions:
  `x ≤ y`, `y ≤ x`, `y ≤ z`, `z ≤ y`.
- [ ] **Step 3:** Apply `leq_trans` twice:
  `x ≤ y ∧ y ≤ z → x ≤ z` and
  `z ≤ y ∧ y ≤ x → z ≤ x`.
- [ ] **Step 4:** Reassemble via
  `natEq_eq_boolAnd_natTruncSub` and
  `boolAnd` associativity/commutativity.
- [ ] **Step 5:** Build and verify. Commit.

---

### Task 2: ElegantPairing Definition

**Files:**
- Create: `GebLean/NatElegantPair.lean`

Reference: `.claude/docs/ElegantPairing.pdf`
(Szudzik 2006).

- [ ] **Step 1:** Create file with header:

```lean
import GebLean.NatNNO

namespace GebLean
open CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]
```

- [ ] **Step 2:** Define `natSquare`:

```lean
def natSquareStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpFst p.T p.T ≫ natSucc)
    (cfpLift
      (cfpLift (cfpSnd p.T p.T)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpLift (cfpFst p.T p.T)
        (cfpFst p.T p.T ≫ natSucc) ≫
          natPlus) ≫ natPlus)
-- step(n, s) = (n+1, s + n + (n+1)) = (n+1, s+2n+1)

def natSquare : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      natSquareStep ≫
    cfpSnd p.T p.T
```

- [ ] **Step 3:** Prove `natSquare` computation
  rules:
  - `natSquare_ℓ : ℓ ≫ natSquare = ℓ`
  - `natSquare_succ`: `natSucc ≫ natSquare =
    natSquare ≫ ... ≫ natPlus` (n+1)² = n² + 2n + 1

- [ ] **Step 4:** Define `elegantPair`:

```lean
def elegantPair :
    cfpProd p.T p.T ⟶ p.T :=
  iteBranches
    (cfpLift (cfpSnd p.T p.T ≫ natSquare)
      (cfpFst p.T p.T) ≫ natPlus)
    (cfpLift
      (cfpLift (cfpFst p.T p.T ≫ natSquare)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpSnd p.T p.T) ≫ natPlus)
    (natTruncSub ≫ isLeafEndo)
-- when x ≤ y (isLeafEndo(x-y) = ℓ): y² + x
-- when x > y (isLeafEndo(x-y) = treeFalse):
--   x² + x + y
```

- [ ] **Step 5:** Prove `elegantPair` computation
  rules for when `x ≤ y` (column) and `x > y` (row)
  using `iteBranches_ℓ` and `iteBranches_β`.

- [ ] **Step 6:** Build and verify. Commit.

---

### Task 3: Integer Square Root and Unpairing

**Files:**
- Modify: `GebLean/NatElegantPair.lean`

- [ ] **Step 1:** Define `isqrtStep`:

```lean
def isqrtStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  -- state = (s, remaining)
  -- when remaining = 0: (s+1, 2s+2)
  -- when remaining > 0: (s, remaining-1)
  cfpLift
    (iteBranches
      (cfpFst p.T p.T ≫ natSucc)
      (cfpFst p.T p.T)
      (cfpSnd p.T p.T ≫ isLeafEndo))
    (iteBranches
      (cfpLift (cfpFst p.T p.T)
        (cfpLift (cfpFst p.T p.T)
          (cfpTerminalFrom _ ≫
            natSucc ≫ natSucc) ≫
          natPlus) ≫ natPlus)
      (cfpSnd p.T p.T ≫ natPred)
      (cfpSnd p.T p.T ≫ isLeafEndo))
```

Note: when `remaining = 0`, new remaining =
`s + (s + 2) = 2s + 2 = 2(s+1)`.  This is the
gap to the next perfect square:
`(s+1+1)² - (s+1)² - 1 = 2s + 2`.

- [ ] **Step 2:** Define `isqrt` and
  `elegantUnpair`:

```lean
def isqrtState : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      isqrtStep

def isqrt : p.T ⟶ p.T :=
  isqrtState ≫ cfpFst p.T p.T

def elegantUnpairRemainder : p.T ⟶ p.T :=
  cfpLift (𝟙 p.T) (isqrt ≫ natSquare) ≫
    natTruncSub  -- z - isqrt(z)²

def elegantUnpair : p.T ⟶ cfpProd p.T p.T :=
  -- s = isqrt(z), r = z - s²
  -- if r < s: (r, s) else (s, r - s)
  cfpLift
    (iteBranches
      elegantUnpairRemainder
      isqrt
      (cfpLift isqrt elegantUnpairRemainder ≫
        natTruncSub ≫ isLeafEndo))
    (iteBranches
      isqrt
      (cfpLift elegantUnpairRemainder isqrt ≫
        natTruncSub)
      (cfpLift isqrt elegantUnpairRemainder ≫
        natTruncSub ≫ isLeafEndo))
```

- [ ] **Step 3:** Prove `isqrt` computation rules.
- [ ] **Step 4:** Build and verify. Commit.

---

### Task 4: ElegantPairing Band Property

**Files:**
- Modify: `GebLean/NatElegantPair.lean`

Prove `isqrt(EP(x, y)) = max(x, y) ≫ toRSN`.

- [ ] **Step 1:** Prove column band:
  `isqrt(y² + x) = toRSN(y)` when `x ≤ y`.
  Proof: the isqrt fold walks through levels
  0, 1, ..., y-1, then enters level y with
  remaining = y² + x - y² = x < 2y+1. Since
  `x ≤ y < 2y+1`, the remaining never reaches 0
  during level y, so isqrt stays at y.

  Express as: after `y² + x` steps of `isqrtStep`
  from `(0, 0)`, the state is `(toRSN(y), ...)`.
  The column walk (x steps within level y) is a
  simple fold with fixed `s = y`.

- [ ] **Step 2:** Prove row band:
  `isqrt(x² + x + y) = toRSN(x)` when `x ≥ y`.
  Similar proof with the row walk.

- [ ] **Step 3:** Combine using `iteBranches`.
- [ ] **Step 4:** Build and verify. Commit.

---

### Task 5: ElegantPairing Injectivity

**Files:**
- Modify: `GebLean/NatElegantPair.lean`

Prove `NatEqElegantPair`:
```lean
theorem natEqElegantPair :
    cfpMap elegantPair elegantPair ≫ natEq =
    cfpLift (fst-natEq) (snd-natEq) ≫ boolAnd
```

i.e., `natEq(EP(x₁,y₁), EP(x₂,y₂)) =
boolAnd(natEq(x₁,x₂), natEq(y₁,y₂))`.

- [ ] **Step 1:** From `natEq(EP₁, EP₂)`:
  apply `isqrt` to both sides.  By band property:
  `natEq(max(x₁,y₁), max(x₂,y₂))`.

- [ ] **Step 2:** Apply `natTruncSub(EP, isqrt²)`
  to both sides: get equal remainders.

- [ ] **Step 3:** Both pairs are in the same phase
  (column/row) since `r < s` iff column, and they
  have the same `r` and `s`.

- [ ] **Step 4:** Within-phase unpairing recovers
  `(x, y)`:
  - Column: `(r, s) = (x, y)`. Same `r` and `s`
    → same `(x, y)`. ✓
  - Row: `(s, r-s) = (x, y)`. Same `r` and `s`
    → same `(x, y)`. ✓

- [ ] **Step 5:** Prove the congruence direction
  (equal components → equal pairings) using
  `natEq_trans` and compatibility of `natSquare` +
  `natPlus` with `natEq`.

- [ ] **Step 6:** Combine both directions via
  `boolAnd` properties.

- [ ] **Step 7:** Build and verify. Commit.

---

### Task 6: Unconditional treeEqG_ββ

**Files:**
- Create: `GebLean/TreeGoedelEP.lean`
  (or modify `GebLean/TreeEqGoedel.lean`)
- Modify: `GebLean.lean` (add imports)

- [ ] **Step 1:** Define `treeToNatEP` using
  ElegantPairing:

```lean
def treeToNatEP : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    p.elim p.ℓ
      (cfpSnd (cfpProd p.T p.T)
        (cfpProd p.T p.T) ≫
        elegantPair ≫ natSucc)
```

- [ ] **Step 2:** Define `treeEqEP`:

```lean
def treeEqEP : cfpProd p.T p.T ⟶ p.T :=
  cfpMap treeToNatEP treeToNatEP ≫ natEq
```

- [ ] **Step 3:** Prove `treeEqEP_ℓℓ`,
  `treeEqEP_ℓβ`, `treeEqEP_βℓ` (same structure
  as the Cantor versions — independent of the
  pairing function choice).

- [ ] **Step 4:** Prove `treeEqEP_ββ`
  unconditionally using `natEqElegantPair` (from
  Task 5).  This is the main payoff.

- [ ] **Step 5:** Package `HasTreeEq` instance
  using ElegantPairing-based tree equality.

- [ ] **Step 6:** Add imports to `GebLean.lean`.

- [ ] **Step 7:** Build and test. Commit.

---

## Notes

### Why ElegantPairing instead of Cantor

Cantor pairing has a "shifted parameter" problem:
`CP(succ(a), b) = succ(CP(a, succ(b)))` couples
both dimensions, preventing expression as a 1D
NNO fold.  ElegantPairing enumerates by squares
with a two-phase level structure:
- Column: `(0,k), (1,k), ..., (k-1,k)` — fold on
  x with y = k fixed.
- Row: `(k,0), (k,1), ..., (k,k)` — fold on y
  with x = k fixed.

Each phase is a standard 1D `nnoElim`.

### Existing Cantor code

Keep all existing Cantor pairing code in
`NatArith.lean`, `TreeGoedel.lean`,
`TreeEqGoedel.lean` intact.  The ElegantPairing
code is added alongside, not replacing.

### Reference

`.claude/docs/ElegantPairing.pdf` — Szudzik 2006,
"An Elegant Pairing Function".
