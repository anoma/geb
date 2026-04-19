import GebLean.LawvereNatBTQuot
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import GebLean.Utilities.ComputableLimits

/-!
# `LawvereNatBT0Cat`: the `m = 0` Full Subcategory of `LawvereNatBT`

The full subcategory of `LawvereNatBTCat` whose objects have BT
arity zero.  Provides the intermediate category for Stage β's
two-step factorization
`LawvereERCat ≅ LawvereNatBT0Cat ↪ LawvereNatBTCat`.

`LawvereNatBT0Cat` inherits its `HasChosenFiniteProducts` from
`LawvereNatBTCat`: the product of `(n₁, 0)` and `(n₂, 0)` is
`(n₁ + n₂, 0)`, still in the subcategory; the terminal `(0, 0)` is
also in the subcategory.
-/

namespace GebLean

open CategoryTheory

/-- Selects `LawvereNatBTCat` objects whose BT arity is zero. -/
def isNatBT0 : ObjectProperty LawvereNatBTCat :=
  fun nm => nm.2 = 0

/-- The full subcategory of `LawvereNatBTCat` on `m = 0`
objects. -/
abbrev LawvereNatBT0Cat : Type := isNatBT0.FullSubcategory

/-- Inclusion functor.  Full and faithful by construction (the
underlying mathlib `FullSubcategory` provides those instances). -/
abbrev natBT0Inclusion : LawvereNatBT0Cat ⥤ LawvereNatBTCat :=
  isNatBT0.ι

/-- Terminal object `(0, 0)` lifted to the subcategory. -/
def lawvereNatBT0Terminal : ChosenTerminal LawvereNatBT0Cat where
  obj := ⟨(0, 0), rfl⟩
  from_ a := ObjectProperty.homMk
    (cfpTerminalFrom (C := LawvereNatBTCat) a.obj)
  uniq := fun f => by
    apply ObjectProperty.hom_ext
    exact (NatBTMorNQuo.terminal_uniq f.hom).trans
      (NatBTMorNQuo.terminal_uniq _).symm

/-- Binary product in the subcategory.  The underlying product object
`(a.1 + b.1, a.2 + b.2)` has BT arity `0 + 0 = 0`, inherited from the
parent's chosen finite products. -/
def lawvereNatBT0Product (a b : LawvereNatBT0Cat) :
    ChosenBinaryProduct a b where
  obj := ⟨(a.obj.1 + b.obj.1, a.obj.2 + b.obj.2), by
    change a.obj.2 + b.obj.2 = 0
    rw [a.property, b.property]⟩
  fst := ObjectProperty.homMk
    (cfpFst (C := LawvereNatBTCat) a.obj b.obj)
  snd := ObjectProperty.homMk
    (cfpSnd (C := LawvereNatBTCat) a.obj b.obj)
  lift f g := ObjectProperty.homMk
    (cfpLift (C := LawvereNatBTCat) f.hom g.hom)
  lift_fst f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpFst _ _ = f.hom
    exact NatBTMorNQuo.pair_fst f.hom g.hom
  lift_snd f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpSnd _ _ = g.hom
    exact NatBTMorNQuo.pair_snd f.hom g.hom
  lift_uniq f g h hf hs := by
    apply ObjectProperty.hom_ext
    change h.hom = cfpLift f.hom g.hom
    apply NatBTMorNQuo.pair_uniq
    · have := hf
      exact congrArg (·.hom) this
    · have := hs
      exact congrArg (·.hom) this

instance : HasChosenFiniteProducts LawvereNatBT0Cat where
  terminal := lawvereNatBT0Terminal
  product := lawvereNatBT0Product

end GebLean
