import GebLean.NatNNO

/-!
# Szudzik's Elegant Pairing Function

Defines an injective pairing function on NNO values
using the two-phase square enumeration of Szudzik
(2006).  The pairing enumerates pairs along the edges
of growing squares:

- Column phase (x ≤ y): `EP(x, y) = y² + x`
- Row phase (x > y): `EP(x, y) = x² + x + y`

The definition avoids the shifted-parameter coupling
that makes Cantor pairing inexpressible as a 1D NNO
fold.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

/-- Squaring via NNO iteration.  Maintains a pair
`(n, s)` where `s` accumulates the running sum of
odd numbers `1 + 3 + 5 + ... + (2n-1) = n²`.
The step maps `(n, s) ↦ (n+1, s + 2n + 1)`.  The
result is `cfpSnd` of the final state. -/
def natSquareStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpFst p.T p.T ≫ natSucc)
    (cfpLift
      (cfpLift (cfpSnd p.T p.T)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpLift (cfpFst p.T p.T)
        (cfpFst p.T p.T ≫ natSucc) ≫
          natPlus) ≫ natPlus)

/-- `natSquare(n) = n²`, computed by iterating
the odd-number summation `n` times from the
initial state `(0, 0)`, then projecting the
accumulator. -/
def natSquare : p.T ⟶ p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      natSquareStep ≫
    cfpSnd p.T p.T

/-- Szudzik's elegant pairing function.
`EP(x, y) = x² + x + y` when `x ≥ y` (row phase),
`EP(x, y) = y² + x` when `x < y` (column phase).
The condition is
`isLeafEndo(natTruncSub(y, x))`:
leaf when `y ≤ x` (row), `treeFalse` when
`y > x` (column). -/
def elegantPair :
    cfpProd p.T p.T ⟶ p.T :=
  iteBranches
    (cfpLift
      (cfpLift (cfpFst p.T p.T ≫ natSquare)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpSnd p.T p.T) ≫ natPlus)
    (cfpLift (cfpSnd p.T p.T ≫ natSquare)
      (cfpFst p.T p.T) ≫ natPlus)
    (cfpSwap p.T p.T ≫ natTruncSub ≫ isLeafEndo)

/-- `natSquare(ℓ) = ℓ`: zero squared is zero. -/
theorem natSquare_ℓ :
    p.ℓ ≫ natSquare = p.ℓ := by
  unfold natSquare
  rw [← Category.assoc, ← Category.assoc,
    cfpLift_precomp, Category.comp_id]
  have term_eq : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [term_eq]
  have ins :
      cfpLift (cfpTerminalFrom cfpTerminal)
        p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [ins, nnoElim_ℓ, cfpLift_snd,
    cfpTerminalFrom_terminal, Category.id_comp]

/-- Step rule for the `natSquare` state:
the internal state `(n, n²)` steps to
`natSquareStep(n, n²) = (n+1, (n+1)²)`. -/
private theorem natSquareState_s :
    natSucc ≫
      (cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        nnoElim
          (cfpLift
            (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
            (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
          natSquareStep) =
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      nnoElim
        (cfpLift
          (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
          (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
        natSquareStep ≫
      (natSquareStep :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) := by
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      natSucc ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  rw [term_eq]
  have factor :
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal)
          (natSucc : p.T ⟶ p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [factor, Category.assoc, nnoElim_s,
    ← Category.assoc]


/-- Row-phase computation rule: when `y ≤ x`
(i.e., `natTruncSub(y, x)` is a leaf),
`elegantPair(x, y) = x² + x + y`. -/
theorem elegantPair_row {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (hcnd :
      f ≫ cfpSwap p.T p.T ≫
        natTruncSub ≫ isLeafEndo =
      cfpTerminalFrom D ≫ p.ℓ) :
    f ≫ elegantPair =
    f ≫ cfpLift
      (cfpLift (cfpFst p.T p.T ≫ natSquare)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpSnd p.T p.T) ≫ natPlus := by
  unfold elegantPair
  rw [iteBranches_precomp, hcnd, iteBranches_ℓ]

/-- Column-phase computation rule: when `y > x`
(i.e., `natTruncSub(y, x)` factors through `β`),
`elegantPair(x, y) = y² + x`. -/
theorem elegantPair_column {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (r : D ⟶ cfpProd p.T p.T)
    (hcnd :
      f ≫ cfpSwap p.T p.T ≫
        natTruncSub ≫ isLeafEndo =
      r ≫ p.β) :
    f ≫ elegantPair =
    f ≫ cfpLift (cfpSnd p.T p.T ≫ natSquare)
      (cfpFst p.T p.T) ≫ natPlus := by
  unfold elegantPair
  rw [iteBranches_precomp, hcnd, iteBranches_β]

/-- Step function for the integer square root.
Maintains a state `(s, remaining)` where `s` is the
current root and `remaining` counts down within the
current level.  When `remaining` reaches zero
(= leaf), the root increments and the remaining
resets to `2s + 2` (the gap to the next perfect
square minus one).  When `remaining > 0`, it
decrements. -/
def isqrtStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift
    (iteBranches
      (cfpFst p.T p.T ≫ natSucc)
      (cfpFst p.T p.T)
      (cfpSnd p.T p.T ≫ isLeafEndo))
    (iteBranches
      (cfpLift (cfpFst p.T p.T)
        (cfpLift (cfpFst p.T p.T)
          (cfpTerminalFrom (cfpProd p.T p.T) ≫
            p.ℓ ≫ natSucc ≫ natSucc) ≫
          natPlus) ≫ natPlus)
      (cfpSnd p.T p.T ≫ natPred)
      (cfpSnd p.T p.T ≫ isLeafEndo))

/-- Full `isqrt` state: fold `isqrtStep` from the
initial state `(0, 0)` for `n` steps. -/
def isqrtState : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      isqrtStep

/-- Integer square root: `isqrt(n) = ⌊√n⌋`.
The first component of the `isqrtState`. -/
def isqrt : p.T ⟶ p.T :=
  isqrtState ≫ cfpFst p.T p.T

/-- The remainder after subtracting `isqrt(z)²`
from `z`: `z - isqrt(z)²`. -/
def elegantUnpairRemainder : p.T ⟶ p.T :=
  cfpLift (𝟙 p.T) (isqrt ≫ natSquare) ≫
    natTruncSub

/-- Szudzik's elegant unpairing function.  Given
`z`, compute `s = isqrt(z)` and `r = z - s²`.
The condition `isLeafEndo(natTruncSub(s, r))`
dispatches:
- ℓ (s ≤ r, row phase): return `(s, r - s)`.
- treeFalse (s > r, column phase): return
  `(r, s)`. -/
def elegantUnpair :
    p.T ⟶ cfpProd p.T p.T :=
  cfpLift
    (iteBranches
      isqrt
      elegantUnpairRemainder
      (cfpLift isqrt elegantUnpairRemainder ≫
        natTruncSub ≫ isLeafEndo))
    (iteBranches
      (cfpLift elegantUnpairRemainder isqrt ≫
        natTruncSub)
      isqrt
      (cfpLift isqrt elegantUnpairRemainder ≫
        natTruncSub ≫ isLeafEndo))

/-- Base case for `isqrtState`:
`isqrtState(ℓ) = (ℓ, ℓ)`. -/
theorem isqrtState_ℓ :
    p.ℓ ≫ isqrtState =
    cfpLift p.ℓ p.ℓ := by
  unfold isqrtState
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [term_eq]
  have ins :
      cfpLift (cfpTerminalFrom cfpTerminal)
        p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [ins, nnoElim_ℓ]
  congr 1 <;>
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]

/-- Base case for `isqrt`: `isqrt(ℓ) = ℓ`. -/
theorem isqrt_ℓ :
    p.ℓ ≫ isqrt = p.ℓ := by
  unfold isqrt
  rw [← Category.assoc, isqrtState_ℓ,
    cfpLift_fst]

/-- Step rule for `isqrtState`:
`isqrtState(natSucc(n))
  = isqrtStep(isqrtState(n))`. -/
theorem isqrtState_s :
    natSucc ≫ isqrtState =
    isqrtState ≫
      (isqrtStep : cfpProd p.T p.T ⟶
        cfpProd p.T p.T) := by
  unfold isqrtState
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      natSucc ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  rw [term_eq]
  have factor :
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal)
          (natSucc : p.T ⟶ p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [factor, Category.assoc, nnoElim_s,
    ← Category.assoc]

/-- Fold composition for `isqrtState`:
`isqrtState(m + n) = isqrtStep^n(isqrtState(m))`.
Proved by `nnoElim_uniq` showing the LHS satisfies
the NNO recurrence with base `isqrtState` and step
`isqrtStep`. -/
theorem isqrtState_natPlus :
    natPlus ≫ isqrtState =
    nnoElim isqrtState
      (isqrtStep :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) := by
  apply nnoElim_uniq
  · -- Base: natPlus(m, ℓ) = m, then isqrtState(m)
    rw [← Category.assoc, natPlus_ℓ, Category.id_comp]
  · -- Step: natPlus(m, n+1) = natPlus(m, n) + 1
    have natPlus_natSucc_snd :
        cfpMap (𝟙 p.T) natSucc ≫ natPlus =
        natPlus ≫ (natSucc : p.T ⟶ p.T) := by
      have h1 : cfpMap (𝟙 p.T)
          (natSucc : p.T ⟶ p.T) =
          cfpLift (cfpFst p.T p.T)
            (cfpSnd p.T p.T ≫ natSucc) := by
        unfold cfpMap; congr 1
        exact Category.comp_id _
      have h2 : cfpLift (cfpFst p.T p.T)
          (cfpSnd p.T p.T) = 𝟙 _ :=
        (cfpLift_uniq _ _ _
          (Category.id_comp _)
          (Category.id_comp _)).symm
      rw [h1, natPlus_succ, h2, Category.id_comp]
    rw [← Category.assoc, natPlus_natSucc_snd,
      Category.assoc, isqrtState_s,
      ← Category.assoc]
  · -- Norm: natPlus absorbs toRSN on second arg
    rw [← Category.assoc,
      natPlus_toRSpineNat_second]

/-- The first component of `isqrtStep` is an
`iteBranches` on the remaining counter:
`fst(isqrtStep(s, r)) = s+1` when `r = ℓ`,
`fst(isqrtStep(s, r)) = s` when `r > 0`. -/
theorem isqrtStep_fst :
    isqrtStep ≫ cfpFst p.T p.T =
    iteBranches
      (cfpFst p.T p.T ≫ natSucc)
      (cfpFst p.T p.T)
      (cfpSnd p.T p.T ≫ isLeafEndo) := by
  unfold isqrtStep
  exact cfpLift_fst _ _

/-- The second component of `isqrtStep` is an
`iteBranches` on the remaining counter:
when `r = ℓ`, resets to `s + (s + 2)`;
when `r > 0`, decrements to `r - 1`. -/
theorem isqrtStep_snd :
    isqrtStep ≫ cfpSnd p.T p.T =
    iteBranches
      (cfpLift (cfpFst p.T p.T)
        (cfpLift (cfpFst p.T p.T)
          (cfpTerminalFrom (cfpProd p.T p.T) ≫
            p.ℓ ≫ natSucc ≫ natSucc) ≫
          natPlus) ≫ natPlus)
      (cfpSnd p.T p.T ≫ natPred)
      (cfpSnd p.T p.T ≫ isLeafEndo) := by
  unfold isqrtStep
  exact cfpLift_snd _ _

/-- Step function for the isqrt level state:
maps `(s, r) ↦ (s+1, r+2)`.  Iterating from
`(ℓ, ℓ)` gives `(toRSN(k), 2·toRSN(k))` at
step `k`. -/
def isqrtLevelStep :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpFst p.T p.T ≫ natSucc)
    (cfpSnd p.T p.T ≫ natSucc ≫ natSucc)

/-- The isqrt state at perfect squares:
`isqrtLevelState(k) = (toRSN(k), 2·toRSN(k))`.
Defined as an NNO fold of `isqrtLevelStep` from
`(ℓ, ℓ)`. -/
def isqrtLevelState : p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
    nnoElim
      (cfpLift
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ)
        (cfpTerminalFrom cfpTerminal ≫ p.ℓ))
      isqrtLevelStep

/-- Base case: `isqrtLevelState(ℓ) = (ℓ, ℓ)`. -/
theorem isqrtLevelState_ℓ :
    p.ℓ ≫ isqrtLevelState =
    cfpLift p.ℓ p.ℓ := by
  unfold isqrtLevelState
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq : p.ℓ ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom cfpTerminal :=
    h.terminal.uniq _
  rw [term_eq]
  have ins :
      cfpLift (cfpTerminalFrom cfpTerminal)
        p.ℓ =
      cfpInsertSnd p.ℓ cfpTerminal := by
    unfold cfpInsertSnd
    congr 1
    · exact cfpTerminalFrom_terminal
    · rw [cfpTerminalFrom_terminal,
        Category.id_comp]
  rw [ins, nnoElim_ℓ]
  congr 1 <;>
    rw [cfpTerminalFrom_terminal,
      Category.id_comp]

/-- Step rule: `isqrtLevelState(natSucc(k))
= isqrtLevelStep(isqrtLevelState(k))`. -/
theorem isqrtLevelState_s :
    natSucc ≫ isqrtLevelState =
    isqrtLevelState ≫
      (isqrtLevelStep :
        cfpProd p.T p.T ⟶
          cfpProd p.T p.T) := by
  unfold isqrtLevelState
  rw [← Category.assoc, cfpLift_precomp,
    Category.comp_id]
  have term_eq :
      natSucc ≫ cfpTerminalFrom p.T =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  rw [term_eq]
  have factor :
      cfpLift (cfpTerminalFrom p.T)
        (natSucc : p.T ⟶ p.T) =
      cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
        cfpMap (𝟙 cfpTerminal)
          (natSucc : p.T ⟶ p.T) := by
    rw [cfpLift_cfpMap, Category.comp_id,
      Category.id_comp]
  rw [factor, Category.assoc, nnoElim_s,
    ← Category.assoc]

/-- At the level boundary, when remaining = ℓ,
`isqrtStep` increments the root and resets the
remaining to `2·root + 2`:
`isqrtStep(s, ℓ) = (s+1, s + (s + 2))`. -/
theorem isqrtStep_at_ℓ :
    cfpLift (𝟙 p.T) (cfpTerminalFrom p.T ≫ p.ℓ) ≫
      isqrtStep =
    cfpLift (natSucc : p.T ⟶ p.T)
      (cfpLift (𝟙 p.T)
        (cfpLift (𝟙 p.T)
          (cfpTerminalFrom p.T ≫
            p.ℓ ≫ natSucc ≫ natSucc) ≫
          natPlus) ≫ natPlus) := by
  set embed := cfpLift (𝟙 p.T)
    (cfpTerminalFrom p.T ≫ p.ℓ) with hembed
  have h_fst : embed ≫
      cfpFst p.T p.T = 𝟙 p.T :=
    cfpLift_fst _ _
  have h_term : embed ≫
      cfpTerminalFrom (cfpProd p.T p.T) =
      cfpTerminalFrom p.T :=
    h.terminal.uniq _
  have h_cnd : embed ≫ cfpSnd p.T p.T ≫
      isLeafEndo =
      cfpTerminalFrom p.T ≫ p.ℓ := by
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, isLeafEndo_ℓ]
  apply cfpLift_uniq
  · -- First component: root increments.
    rw [Category.assoc, isqrtStep_fst,
      iteBranches_precomp, h_cnd,
      iteBranches_ℓ,
      ← Category.assoc, h_fst,
      Category.id_comp]
  · -- Second component: remaining resets.
    rw [Category.assoc, isqrtStep_snd,
      iteBranches_precomp, h_cnd,
      iteBranches_ℓ]
    -- Simplify the reset expression.
    rw [← Category.assoc embed,
      cfpLift_precomp, h_fst,
      ← Category.assoc embed,
      cfpLift_precomp, h_fst,
      ← Category.assoc embed
        (cfpTerminalFrom (cfpProd p.T p.T)),
      h_term]

/-- When the remaining counter is nonzero
(factors through `β`), `isqrtStep` preserves the
root and decrements the remaining:
`isqrtStep(s, r) = (s, natPred(r))`. -/
theorem isqrtStep_at_β {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (r : D ⟶ cfpProd p.T p.T)
    (hcnd : f ≫ cfpSnd p.T p.T ≫ isLeafEndo =
      r ≫ p.β) :
    f ≫ isqrtStep =
    cfpLift (f ≫ cfpFst p.T p.T)
      (f ≫ cfpSnd p.T p.T ≫ natPred) := by
  apply cfpLift_uniq
  · rw [Category.assoc, isqrtStep_fst,
      iteBranches_precomp, hcnd,
      iteBranches_β]
  · rw [Category.assoc, isqrtStep_snd,
      iteBranches_precomp, hcnd,
      iteBranches_β]

/-- Root stability under one `isqrtStep` when the
remaining counter is nonzero:
`fst(isqrtStep(s, r)) = fst(s, r)` when
`isLeafEndo(r)` factors through `β`. -/
theorem isqrtStep_fst_stable {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (r : D ⟶ cfpProd p.T p.T)
    (hcnd : f ≫ cfpSnd p.T p.T ≫ isLeafEndo =
      r ≫ p.β) :
    f ≫ isqrtStep ≫ cfpFst p.T p.T =
    f ≫ cfpFst p.T p.T := by
  rw [← Category.assoc,
    isqrtStep_at_β f r hcnd, cfpLift_fst]

/-- Countdown step: preserves root, decrements
remaining.  `countdown(s, r) = (s, natPred(r))`. -/
def isqrtCountdown :
    cfpProd p.T p.T ⟶ cfpProd p.T p.T :=
  cfpLift (cfpFst p.T p.T)
    (cfpSnd p.T p.T ≫ natPred)

/-- `countdown ≫ cfpFst = cfpFst`:
the countdown step preserves the root. -/
private theorem isqrtCountdown_fst :
    isqrtCountdown ≫ cfpFst p.T p.T =
    cfpFst p.T p.T := by
  unfold isqrtCountdown; exact cfpLift_fst _ _

/-- The countdown fold unconditionally preserves
the root (first component of the state):
`fst(countdown^j(s, r)) = s`. -/
theorem nnoElim_countdown_fst :
    nnoElim (𝟙 (cfpProd p.T p.T))
      (isqrtCountdown :
        cfpProd p.T p.T ⟶ cfpProd p.T p.T) ≫
      cfpFst p.T p.T =
    nnoElim (cfpFst p.T p.T) (𝟙 p.T) := by
  apply nnoElim_uniq
  · -- Base: fold at ℓ gives cfpFst
    rw [← Category.assoc, nnoElim_ℓ,
      Category.id_comp]
  · -- Step: fold ≫ countdown ≫ fst = fold ≫ fst
    rw [← Category.assoc, nnoElim_s,
      Category.assoc, isqrtCountdown_fst,
      Category.comp_id]
  · -- Norm: absorption of toRSN
    rw [← Category.assoc]
    congr 1
    unfold nnoElim
    rw [← Category.assoc, cfpMap_comp,
      Category.id_comp, toRSpineNat_idem]

/-- The number of `isqrtStep` applications at
each level: `natSquareGap(k) = 2k + 1`, defined
as `natPlus(k, natPlus(k, natSucc(ℓ)))`. -/
def natSquareGap : p.T ⟶ p.T :=
  cfpLift (𝟙 p.T)
    (cfpLift (𝟙 p.T)
      (cfpTerminalFrom p.T ≫ p.ℓ ≫ natSucc) ≫
      natPlus) ≫ natPlus

end GebLean
