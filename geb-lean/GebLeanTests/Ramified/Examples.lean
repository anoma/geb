import GebLean
import GebLean.Ramified.Examples

/-!
# Tests for the section 2.4 example ladder

Executable checks over the `1 + X` word algebra `natAlgSig` for the ladder items
of `GebLean.Ramified.Examples`: the numeric reading `natToFreeAlg`/`freeAlgToNat`
round trips, addition denotes `+` (checked at `2 + 3`), multiplication denotes
`*` (checked at `2 * 3`), the size function denotes the identity (checked at
`3`), and the downward coercions `kappa` and `delta` denote the identity on the
carrier (checked at small tower sorts, and over all inputs through the proven
interpretation lemmas).

The denotations land in the base carrier `FreeAlg natAlgSig`; the value checks
read out via `freeAlgToNat` so that `#guard` decides `Nat` equalities. Value
checks stay on small inputs; the coercion identity over all inputs is exercised
through the proven interpretation lemmas rather than by kernel evaluation.
-/

namespace GebLeanTests.Ramified.ExamplesTest

open GebLean.Ramified

-- The numeric reading is a round trip on small inputs.
#guard freeAlgToNat (natToFreeAlg 0) = 0
#guard freeAlgToNat (natToFreeAlg 5) = 5

-- Addition denotes `+`: `2 + 3 = 5`.
#guard freeAlgToNat (ramAdd.interp (addEnv (natToFreeAlg 2) (natToFreeAlg 3))) = 5

-- Multiplication denotes `*`: `2 * 3 = 6`.
#guard freeAlgToNat (ramMul.interp (mulEnv (natToFreeAlg 2) (natToFreeAlg 3))) = 6

-- The size function denotes the identity: `size 3 = 3`.
#guard freeAlgToNat (ramSize.interp (sizeEnv (natToFreeAlg 3))) = 3

/-- A one-element environment at the single-`Omega`-lowering source sort
`Omega^2 o`. -/
def kappaEnv1 : ∀ i : Fin ([RType.tower 2] : Ctx RType).length,
    RType.interp (FreeAlg natAlgSig) (([RType.tower 2] : Ctx RType).get i) :=
  Fin.cons (natToFreeAlg 3) finZeroElim

/-- A one-element environment at the lowering source sort `Omega o`. -/
def deltaEnv1 : ∀ i : Fin ([RType.tower 1] : Ctx RType).length,
    RType.interp (FreeAlg natAlgSig) (([RType.tower 1] : Ctx RType).get i) :=
  Fin.cons (natToFreeAlg 2) finZeroElim

-- `kappa` lowers `Omega^2 o -> Omega o` as the identity on the carrier.
#guard objToNat (RType.tower_isObj 1) ((ramKappa 1).interp kappaEnv1) = 3

-- `delta` lowers `Omega o -> o` as the identity on the carrier.
#guard freeAlgToNat ((ramDeltaIdent 1).interp deltaEnv1) = 2

-- The numeric interpretation lemmas hold over all inputs.
example (a b : Nat) :
    freeAlgToNat (ramAdd.interp (addEnv (natToFreeAlg a) (natToFreeAlg b))) = a + b :=
  ramAdd_interp a b

example (x y : Nat) :
    freeAlgToNat (ramMul.interp (mulEnv (natToFreeAlg x) (natToFreeAlg y))) = x * y :=
  ramMul_interp x y

example (t : FreeAlg natAlgSig) :
    freeAlgToNat (ramSize.interp (sizeEnv t)) = freeAlgToNat t :=
  ramSize_interp t

-- The lowering coercion `delta : Omega^m o -> o` is the identity on the carrier
-- over all inputs, at every tower height.
example (t : FreeAlg natAlgSig) :
    freeAlgToNat ((ramDeltaIdent 3).interp (Fin.cons t finZeroElim))
      = freeAlgToNat t := by
  have h := ramDeltaIdent_interp 3 (Fin.cons t finZeroElim)
  simpa [objToNat] using h

/-- A one-element environment at the exponentiation recurrence-argument sort
`Omega (o -> o)`. -/
def expEnv (n : Nat) :
    ∀ i : Fin ([RType.omega ramFun] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega ramFun] : Ctx RType).get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- Exponentiation iterates the successor: `e (1) (3) = 3 + 2^1 = 5`,
-- `e (2) (0) = 2^2 = 4`.
#guard freeAlgToNat ((ramExp.interp (expEnv 1)) (natToFreeAlg 3)) = 5
#guard freeAlgToNat ((ramExp.interp (expEnv 2)) (natToFreeAlg 0)) = 4

-- The `2_m` ladder aligns with the tower: `2_2 (1) = 2^(2^1) = 4`.
#guard freeAlgToNat (ramTwoPow 2 (natToFreeAlg 1)) = 4

-- Exponentiation iterates the successor, over all inputs.
example (n x : Nat) :
    freeAlgToNat ((ramExp.interp (expEnv n)) (natToFreeAlg x)) = x + 2 ^ n := by
  unfold expEnv
  rw [ramExp_interp, freeAlgToNat_natToFreeAlg]
  exact congrArg (fun k => x + 2 ^ k)
    ((congrArg freeAlgToNat (Fin.cons_zero _ _)).trans (freeAlgToNat_natToFreeAlg n))

-- The `2_m` ladder denotes the tower of twos, over all inputs.
example (m : Nat) (x : FreeAlg natAlgSig) :
    freeAlgToNat (ramTwoPow m x) = GebLean.tower m (freeAlgToNat x) :=
  ramTwoPow_interp m x

end GebLeanTests.Ramified.ExamplesTest
