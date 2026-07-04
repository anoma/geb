import GebLean
import GebLean.Ramified.Definability.Simultaneous

/-!
# Tests for case, destructor, selector, and the simultaneous family

Executable checks over the `1 + X` word algebra `natAlgSig` for
`GebLean.Ramified.Definability.Simultaneous`: the case function `ramCase`
selects a parameter by the argument's top constructor, the destructor `ramDstr`
is the predecessor, the selector `chooseIdent` reads off the entry indexed by
the selector numeral and falls through to the last entry on out-of-range
values, and the simultaneous family (`simulProj`, `simulSol`) computes the
alternating pair `f₁(n+1) = f₂(n)`, `f₂(n+1) = succ (f₁(n))` with base
`(0, 0)`. The value checks read out via `freeAlgToNat` so that `#guard` decides
`Nat` equalities; the interpretation lemmas over all inputs are exercised
through `example`s. The identifier-morphism helper `identHom` is checked here
on `ramAdd` at the environment `(2, 3)`.
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

-- The simultaneous family (Lemma 2): the alternating pair
-- `f₁(n+1) = f₂(n)`, `f₂(n+1) = succ (f₁(n))`, base `(0, 0)`, whose closed
-- forms are `f₁(n) = n / 2` and `f₂(n) = (n + 1) / 2`.

/-- The step clauses of the alternating pair as `SimulSteps 2 [] RType.o`: at
the nullary constructor both components return `0`; at the unary constructor
component `0` applies the recursive-result function to the selector numeral `1`
(reading `f₂` at the previous count) and component `1` wraps the value at
selector numeral `0` (reading `f₁`) in a successor. -/
def altSteps : SimulSteps 2 [] RType.o := fun j i =>
  match j, i with
  | _, false => RIdent.defn ⟨0, finZeroElim, tmZero⟩ finZeroElim
  | ⟨0, _⟩, true =>
    RIdent.defn ⟨0, finZeroElim,
      Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
        (Sum.inl (Sum.inl (Sum.inr (RType.o, RType.o))))
        (Fin.cons (Tm.var ⟨0, by decide⟩)
          (Fin.cons (tmSucc tmZero) finZeroElim))⟩ finZeroElim
  | ⟨_ + 1, _⟩, true =>
    RIdent.defn ⟨0, finZeroElim,
      tmSucc (Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
        (Sum.inl (Sum.inl (Sum.inr (RType.o, RType.o))))
        (Fin.cons (Tm.var ⟨0, by decide⟩)
          (Fin.cons tmZero finZeroElim)))⟩ finZeroElim

-- The reference solution matches the closed forms at counts `0, 1, 2, 3`.
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 0 0) = 0
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 0 1) = 0
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 1 0) = 0
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 1 1) = 1
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 2 0) = 1
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 2 1) = 1
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 3 0) = 1
#guard freeAlgToNat (simulSol [] RType.o altSteps finZeroElim 3 1) = 2

-- The projected components of the function-valued recurrence match the closed
-- forms at counts `0, 1, 2, 3`.
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 0).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 0))) = 0
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 1).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 0))) = 0
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 0).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 1))) = 0
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 1).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 1))) = 1
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 0).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 2))) = 1
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 1).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 2))) = 1
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 0).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 3))) = 1
#guard freeAlgToNat ((simulProj (Nat.succ_pos 1) [] RType.o altSteps 1).interp
  (simulEnv [] RType.o finZeroElim (natToFreeAlg 3))) = 2

-- The projected components denote the reference solution over all counts and
-- components.
example (n : Nat) (j : Fin 2) :
    (simulProj (Nat.succ_pos 1) [] RType.o altSteps j).interp
        (simulEnv [] RType.o finZeroElim (natToFreeAlg n))
      = simulSol [] RType.o altSteps finZeroElim n j :=
  simulProj_interp (Nat.succ_pos 1) [] RType.o altSteps finZeroElim n j

end GebLeanTests.Ramified.Definability.SimultaneousTest
