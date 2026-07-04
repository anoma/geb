import GebLean
import GebLean.Ramified.OmegaShift
import GebLeanTests.Ramified.HigherOrder

/-!
# Tests for the sort-level Omega shift and kappa-hat

Executable checks that `GebLean.Ramified.RType.omegaShift` performs the base
substitution `τ[o := Ω o]` on the base type, an arrow sort, and an arrow sort
with an `Omega` domain, and that the auxiliary coercion kappa-hat denotes the
identity on the carrier: `kappaHatIdent` is interpreted at small inputs over
the `1 + X` word algebra, at the base sort `o` and at the object sort `Ω o`.
The `kappaHat` morphism is exercised against the `Category` instance of
`GebLean.Ramified.RMRecCat`.

The interpretations land in the base carrier `FreeAlg natAlgSig`; the checks
convert to `Nat` via `GebLean.Ramified.freeAlgToNat` so that
`#guard` decides `Nat` equalities.
-/

namespace GebLeanTests.Ramified.OmegaShiftTest

open GebLean.Ramified GebLeanTests.Ramified.HigherOrderTest CategoryTheory

-- The Omega shift substitutes at the base type and distributes over `arrow`
-- and `omega`; in particular it is not postcomposition with `Omega`.
example : RType.omegaShift RType.o = RType.omega RType.o := rfl
example : RType.omegaShift (RType.arrow RType.o RType.o)
    = RType.arrow (RType.omega RType.o) (RType.omega RType.o) := rfl
example : RType.omegaShift (RType.arrow (RType.omega RType.o) RType.o)
    = RType.arrow (RType.omega (RType.omega RType.o)) (RType.omega RType.o) := rfl

/-- A one-element environment at the recurrence-argument sort `Ω o`. -/
def envOmegaO (n : Nat) :
    ∀ i : Fin [RType.omega RType.o].length,
      RType.interp (FreeAlg A) ([RType.omega RType.o].get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

/-- A one-element environment at the recurrence-argument sort `Ω (Ω o)`. -/
def envOmegaOmegaO (n : Nat) :
    ∀ i : Fin [RType.omega (RType.omega RType.o)].length,
      RType.interp (FreeAlg A) ([RType.omega (RType.omega RType.o)].get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- kappa-hat at `o` denotes the identity on the carrier copy.
#guard freeAlgToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 0)) = 0
#guard freeAlgToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 2)) = 2
#guard freeAlgToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 5)) = 5

-- kappa-hat at the object sort `Ω o` denotes the identity on the carrier copy.
#guard freeAlgToNat
  ((kappaHatIdent A (RType.omega RType.o) (by decide)).interp (envOmegaOmegaO 0)) = 0
#guard freeAlgToNat
  ((kappaHatIdent A (RType.omega RType.o) (by decide)).interp (envOmegaOmegaO 3)) = 3

/-- The source context `[Ω o]` of `kappaHat` at `o`. -/
abbrev srcCtx : RMRecCat A := [RType.omega RType.o]

/-- The target context `[o]` of `kappaHat` at `o`. -/
abbrev tgtCtx : RMRecCat A := [RType.o]

/-- `kappaHat` at `o`, read as a morphism of `RMRecCat`. -/
def kappaHatO : srcCtx ⟶ tgtCtx := kappaHat A RType.o (by decide)

-- The `Category` instance composes `kappaHat` with identities.
example : 𝟙 srcCtx ≫ kappaHatO = kappaHatO := Category.id_comp _
example : kappaHatO ≫ 𝟙 tgtCtx = kappaHatO := Category.comp_id _

-- The full kappa-hat agrees with the object-sort instance at an object sort.
example (ρ : ∀ i : Fin ([RType.omega RType.o] : Ctx RType).length,
    RType.interp (FreeAlg A) (([RType.omega RType.o] : Ctx RType).get i)) :
    (kappaHatFull A RType.o).interp ρ
      = (kappaHatIdent A RType.o (by decide)).interp ρ := by
  rw [kappaHatFull_eq_kappaHatIdent]

-- kappa-hat at `o` reconstructs the carrier: identity on `0, 3`.
#guard freeAlgToNat ((kappaHatFull A RType.o).interp (envOmegaO 0)) = 0
#guard freeAlgToNat ((kappaHatFull A RType.o).interp (envOmegaO 3)) = 3

/-- The arrow sort `o → o`. -/
abbrev arrOO : RType := RType.arrow RType.o RType.o

/-- A one-element environment at the recurrence-argument sort `Ω (o → o)`. -/
def envArrOO (n : Nat) :
    ∀ i : Fin ([RType.omega arrOO] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega arrOO] : Ctx RType).get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- At the arrow sort `o → o`, the full kappa-hat denotes the pointwise-lifted
-- reconstruction: on the numeral `2` it is the `2`-fold `cLift` composite, whose
-- value on any input reconstructs `2`.
#guard freeAlgToNat (((kappaHatFull A arrOO).interp (envArrOO 2)) (natToFreeAlg 5)) = 2
#guard freeAlgToNat (((kappaHatFull A arrOO).interp (envArrOO 3)) (natToFreeAlg 0)) = 3

/-- A one-element environment at the object sort `Ω (o → o)`. -/
def deltaArrEnv (n : Nat) :
    ∀ i : Fin ([RType.omega arrOO] : Ctx RType).length,
      RType.interp (FreeAlg A) (([RType.omega arrOO] : Ctx RType).get i) :=
  Fin.cons (natToFreeAlg n) finZeroElim

-- The downward coercion `δ` at the object sort `Ω (o → o)` reads the identity on
-- the carrier: `δ (n) = n`.
#guard freeAlgToNat ((deltaIdent A false rfl (RType.omega arrOO) (by decide)).interp
  (deltaArrEnv 0)) = 0
#guard freeAlgToNat ((deltaIdent A false rfl (RType.omega arrOO) (by decide)).interp
  (deltaArrEnv 3)) = 3

-- The general identity theorem `deltaIdent_interp` at the arrow-Omega object sort
-- `Ω (o → o)`: over a symbolic environment the coercion reads the carrier copy.
example (ρ : ∀ i : Fin ([RType.omega arrOO] : Ctx RType).length,
    RType.interp (FreeAlg A) (([RType.omega arrOO] : Ctx RType).get i)) :
    (deltaIdent A false rfl (RType.omega arrOO) (by decide)).interp ρ
      = cast (RType.interp_isObj (FreeAlg A) (by decide)) (ρ 0) :=
  deltaIdent_interp A false rfl (RType.omega arrOO) (by decide) ρ

end GebLeanTests.Ramified.OmegaShiftTest
