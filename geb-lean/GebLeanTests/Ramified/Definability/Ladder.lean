import GebLean
import GebLean.Ramified.Definability.Ladder

/-!
# Tests for the in-system clock ladder at object sorts

Executable checks over the `1 + X` word algebra `natAlgSig` for the object-sort
numeric family of `GebLean.Ramified.Definability.Ladder`. Concrete value checks
run at the base object sort `o` and at `Ω o`, where the object sort denotes the
carrier so `objToNat` reads out as `freeAlgToNat`; the tower/clock arguments are
kept tiny (`tower 2 1 = 4`). The interpretation lemmas over all inputs are
exercised as `example`s at an abstract object sort.
-/

namespace GebLeanTests.Ramified.Definability.LadderTest

open GebLean.Ramified

/-- The base object sort `o` as an object-sort witness. -/
def oObj' : RType.IsObj RType.o := Or.inl rfl

/-- The object sort `Ω o` as an object-sort witness. -/
def ωoObj : RType.IsObj (RType.omega RType.o) := Or.inr rfl

-- Addition denotes `+`: `2 + 3 = 5` (at `θ = o`).
#guard freeAlgToNat ((addAtIdent RType.o oObj').interp
  (Fin.cons (natToFreeAlg 2) (Fin.cons (natToFreeAlg 3) finZeroElim))) = 5

-- Multiplication denotes `*`: `2 * 3 = 6` (at `θ = o`).
#guard freeAlgToNat ((mulAtIdent RType.o oObj').interp
  (Fin.cons (natToFreeAlg 2) (Fin.cons (natToFreeAlg 3) finZeroElim))) = 6

-- The size function counts the constructors: `sz 0 = 1`, `sz 3 = 4` (at `θ = o`).
#guard freeAlgToNat ((szAtIdent RType.o oObj').interp
  (Fin.cons (natToFreeAlg 0) finZeroElim)) = 1
#guard freeAlgToNat ((szAtIdent RType.o oObj').interp
  (Fin.cons (natToFreeAlg 3) finZeroElim)) = 4

-- The exponentiation copy iterates the successor at `θ = Ω o`:
-- `e (1) (0) = 0 + 2^1 = 2`, `e (2) (0) = 2^2 = 4`.
#guard freeAlgToNat (((expAtIdent (RType.omega RType.o) ωoObj).interp
  (Fin.cons (natToFreeAlg 1) finZeroElim)) (natToFreeAlg 0)) = 2
#guard freeAlgToNat (((expAtIdent (RType.omega RType.o) ωoObj).interp
  (Fin.cons (natToFreeAlg 2) finZeroElim)) (natToFreeAlg 0)) = 4

-- The clock family aligns with the tower: `2_2 (1) = tower 2 1 = 2^(2^1) = 4`
-- (at `θ = o`).
#guard freeAlgToNat ((twoPowIdent 2 RType.o oObj').interp
  (Fin.cons (natToFreeAlg 1) finZeroElim)) = 4

-- Addition denotes `+`, over all inputs.
example (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([θ, RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ, RType.omega θ] : Ctx RType).get i)) :
    objToNat hθ ((addAtIdent θ hθ).interp ρ)
      = objToNat hθ (ρ 0) + freeAlgToNat (ρ 1) :=
  addAtIdent_interp_env θ hθ ρ

-- Multiplication denotes `*`, over all inputs.
example (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega θ, RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega θ, RType.omega θ] : Ctx RType).get i)) :
    objToNat hθ ((mulAtIdent θ hθ).interp ρ)
      = freeAlgToNat (ρ 0) * freeAlgToNat (ρ 1) :=
  mulAtIdent_interp_env θ hθ ρ

-- The exponentiation copy counts `x + 2^n`, over all inputs.
example (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i))
    (x : RType.interp (FreeAlg natAlgSig) θ) :
    objToNat hθ ((expAtIdent θ hθ).interp ρ x)
      = objToNat hθ x + 2 ^ freeAlgToNat (ρ 0) :=
  expAtIdent_interp θ hθ ρ x

-- The size function counts `count a + 1`, over all inputs.
example (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i)) :
    objToNat hθ ((szAtIdent θ hθ).interp ρ) = freeAlgToNat (ρ 0) + 1 :=
  szAtIdent_interp θ hθ ρ

-- The clock family aligns with `GebLean.tower`, over all inputs and heights.
example (m : Nat) (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([clockSort m θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([clockSort m θ] : Ctx RType).get i)) :
    objToNat hθ ((twoPowIdent m θ hθ).interp ρ)
      = GebLean.tower m (objToNat (clockSort_isObj m θ hθ) (ρ 0)) :=
  twoPowIdent_interp m θ hθ ρ

end GebLeanTests.Ramified.Definability.LadderTest
