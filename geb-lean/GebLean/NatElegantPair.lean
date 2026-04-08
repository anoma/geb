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
`EP(x, y) = y² + x` when `x ≤ y` (column phase),
`EP(x, y) = x² + x + y` when `x > y` (row phase).
The condition is `isLeafEndo(natTruncSub(x, y))`:
leaf when `x ≤ y`, `treeFalse` when `x > y`. -/
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

/-- Column-phase computation rule: when `x ≤ y`
(i.e., `natTruncSub(x,y)` is a leaf),
`elegantPair(x, y) = natPlus(natSquare(y), x)`. -/
theorem elegantPair_column {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (hcnd :
      f ≫ natTruncSub ≫ isLeafEndo =
      cfpTerminalFrom D ≫ p.ℓ) :
    f ≫ elegantPair =
    f ≫ cfpLift (cfpSnd p.T p.T ≫ natSquare)
      (cfpFst p.T p.T) ≫ natPlus := by
  unfold elegantPair
  rw [iteBranches_precomp, hcnd,
    iteBranches_ℓ]

/-- Row-phase computation rule: when `x > y`
(i.e., `natTruncSub(x,y)` factors through `β`),
`elegantPair(x, y) =
  natPlus(natPlus(natSquare(x), x), y)`. -/
theorem elegantPair_row {D : C}
    (f : D ⟶ cfpProd p.T p.T)
    (r : D ⟶ cfpProd p.T p.T)
    (hcnd :
      f ≫ natTruncSub ≫ isLeafEndo =
      r ≫ p.β) :
    f ≫ elegantPair =
    f ≫ cfpLift
      (cfpLift (cfpFst p.T p.T ≫ natSquare)
        (cfpFst p.T p.T) ≫ natPlus)
      (cfpSnd p.T p.T) ≫ natPlus := by
  unfold elegantPair
  rw [iteBranches_precomp, hcnd,
    iteBranches_β]

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
If `r < s` (column phase): return `(r, s)`.
If `r ≥ s` (row phase): return `(s, r - s)`. -/
def elegantUnpair :
    p.T ⟶ cfpProd p.T p.T :=
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

end GebLean
