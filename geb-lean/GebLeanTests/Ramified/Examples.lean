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

end GebLeanTests.Ramified.ExamplesTest
