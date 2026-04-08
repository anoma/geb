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

end GebLean
