import GebLean
import GebLean.Ramified.Definability.Simultaneous

/-!
# Tests for case, destructor, and the selector

Executable checks over the `1 + X` word algebra `natAlgSig` for the definability
building blocks of `GebLean.Ramified.Definability.Simultaneous`: the case
function `ramCase` selects a parameter by the argument's top constructor, the
destructor `ramDstr` is the predecessor, and the selector `chooseIdent` reads off
the entry indexed by the selector numeral and falls through to the last entry on
out-of-range values. The value checks read out via `freeAlgToNat` so that
`#guard` decides `Nat` equalities; the interpretation lemmas over all inputs are
exercised through `example`s. The identifier-morphism helper `identHom` (Task
5.1a) is checked here on `ramAdd` at the environment `(2, 3)`.
-/

namespace GebLeanTests.Ramified.Definability.SimultaneousTest

open GebLean.Ramified

-- The case function selects by the argument's top constructor: at the nullary
-- constructor `0` it returns `y₀ = 7`, at the unary constructor `succ 0` it
-- returns `y₁ = 9`.
#guard freeAlgToNat
  ((ramCase RType.o).interp
    (caseEnv RType.o (natToFreeAlg 7) (natToFreeAlg 9) (natToFreeAlg 0))) = 7
#guard freeAlgToNat
  ((ramCase RType.o).interp
    (caseEnv RType.o (natToFreeAlg 7) (natToFreeAlg 9) (natToFreeAlg 1))) = 9

-- The destructor is the predecessor: `dstr 0 = 0`, `dstr 1 = 0`, `dstr 3 = 2`.
#guard freeAlgToNat (ramDstr.interp (dstrEnv (natToFreeAlg 0))) = 0
#guard freeAlgToNat (ramDstr.interp (dstrEnv (natToFreeAlg 1))) = 0
#guard freeAlgToNat (ramDstr.interp (dstrEnv (natToFreeAlg 3))) = 2

-- The selector reads off the entry indexed by the selector numeral. On four
-- entries `y₀ … y₃ = 10, 11, 12, 13` the selectors `0, 2, 3` pick `10, 12, 13`.
#guard freeAlgToNat
  ((chooseIdent 3 RType.o).interp
    (chooseEnv 3 RType.o (natToFreeAlg 0)
      ![natToFreeAlg 10, natToFreeAlg 11, natToFreeAlg 12, natToFreeAlg 13])) = 10
#guard freeAlgToNat
  ((chooseIdent 3 RType.o).interp
    (chooseEnv 3 RType.o (natToFreeAlg 2)
      ![natToFreeAlg 10, natToFreeAlg 11, natToFreeAlg 12, natToFreeAlg 13])) = 12
#guard freeAlgToNat
  ((chooseIdent 3 RType.o).interp
    (chooseEnv 3 RType.o (natToFreeAlg 3)
      ![natToFreeAlg 10, natToFreeAlg 11, natToFreeAlg 12, natToFreeAlg 13])) = 13

-- On selector values at or beyond the entry count the selector falls through to
-- the last entry: `chooseIdent 2` at selector `5` and `chooseIdent 3` at
-- selector `7` both return the last entry.
#guard freeAlgToNat
  ((chooseIdent 2 RType.o).interp
    (chooseEnv 2 RType.o (natToFreeAlg 5)
      ![natToFreeAlg 10, natToFreeAlg 11, natToFreeAlg 12])) = 12
#guard freeAlgToNat
  ((chooseIdent 3 RType.o).interp
    (chooseEnv 3 RType.o (natToFreeAlg 7)
      ![natToFreeAlg 10, natToFreeAlg 11, natToFreeAlg 12, natToFreeAlg 13])) = 13

-- The identifier-morphism helper `identHom` reads off `RIdent.interp`: on
-- `ramAdd` at the environment `(2, 3)` its evaluation reads `5` through
-- `freeAlgToNat`.
example :
    freeAlgToNat
      ((identHom ramAdd).eval (addEnv (natToFreeAlg 2) (natToFreeAlg 3)) 0) = 5 := by
  rw [identHom_eval]; exact ramAdd_interp 2 3

-- The case function selects the parameter over all carrier arguments.
example (τ : RType) (y0 y1 : RType.interp (FreeAlg natAlgSig) τ)
    (b : Bool) (subs : Fin (natAlgSig.ar b) → FreeAlg natAlgSig) :
    (ramCase τ).interp (caseEnv τ y0 y1 (FreeAlg.mk b subs)) = cond b y1 y0 :=
  ramCase_interp τ y0 y1 b subs

-- The destructor is the predecessor over all counts.
example (z : FreeAlg natAlgSig) :
    freeAlgToNat (ramDstr.interp (dstrEnv z)) = freeAlgToNat z - 1 :=
  ramDstr_interp z

-- The selector reads off the entry indexed by the selector numeral over all
-- inputs, and falls through to the last entry on out-of-range values.
example (m : Nat) (τ : RType) (z : FreeAlg natAlgSig)
    (y : Fin (m + 1) → RType.interp (FreeAlg natAlgSig) τ) (j : Fin (m + 1))
    (hz : z = natToFreeAlg j.val) :
    (chooseIdent m τ).interp (chooseEnv m τ z y) = y j :=
  chooseIdent_interp m τ z y j hz

example (m : Nat) (τ : RType) (z : FreeAlg natAlgSig)
    (y : Fin (m + 1) → RType.interp (FreeAlg natAlgSig) τ) (j : Nat)
    (hj : m ≤ j) (hz : z = natToFreeAlg j) :
    (chooseIdent m τ).interp (chooseEnv m τ z y) = y (Fin.last m) :=
  chooseIdent_interp_ge m τ z y j hj hz

end GebLeanTests.Ramified.Definability.SimultaneousTest
