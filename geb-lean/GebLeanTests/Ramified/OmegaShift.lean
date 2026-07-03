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
convert to `Nat` via `GebLeanTests.Ramified.HigherOrderTest.faToNat` so that
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
  Fin.cons (natToFA n) finZeroElim

/-- A one-element environment at the recurrence-argument sort `Ω (Ω o)`. -/
def envOmegaOmegaO (n : Nat) :
    ∀ i : Fin [RType.omega (RType.omega RType.o)].length,
      RType.interp (FreeAlg A) ([RType.omega (RType.omega RType.o)].get i) :=
  Fin.cons (natToFA n) finZeroElim

-- kappa-hat at `o` denotes the identity on the carrier copy.
#guard faToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 0)) = 0
#guard faToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 2)) = 2
#guard faToNat ((kappaHatIdent A RType.o (by decide)).interp (envOmegaO 5)) = 5

-- kappa-hat at the object sort `Ω o` denotes the identity on the carrier copy.
#guard faToNat
  ((kappaHatIdent A (RType.omega RType.o) (by decide)).interp (envOmegaOmegaO 0)) = 0
#guard faToNat
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

end GebLeanTests.Ramified.OmegaShiftTest
