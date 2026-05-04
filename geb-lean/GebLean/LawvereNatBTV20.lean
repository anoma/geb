import GebLean.LawvereNatBTV2Quot
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import GebLean.Utilities.ComputableLimits

/-!
# `LawvereNatBTV20Cat`: the `m = 0` Full Subcategory of `LawvereNatBTV2`

Bottom-up V2 variant of `LawvereNatBT0`.  The full subcategory of
`LawvereNatBTV2Cat` whose objects have BT arity zero.  Used as
the (n, 0)-restricted subcategory for the equivalence with
`LawvereERCat` in Phase E.

`LawvereNatBTV20Cat` inherits its `HasChosenFiniteProducts` from
`LawvereNatBTV2Cat`: the product of `(n₁, 0)` and `(n₂, 0)` is
`(n₁ + n₂, 0)`, still in the subcategory; the terminal `(0, 0)`
is also in the subcategory.

The bottom-up design is documented in
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`.
-/

namespace GebLean

open CategoryTheory

/-- Selects `LawvereNatBTV2Cat` objects whose BT arity is zero. -/
def isNatBTV20 : ObjectProperty LawvereNatBTV2Cat :=
  fun nm => nm.2 = 0

/-- The full subcategory of `LawvereNatBTV2Cat` on `m = 0`
objects. -/
abbrev LawvereNatBTV20Cat : Type := isNatBTV20.FullSubcategory

/-- Inclusion functor.  Full and faithful by construction (the
underlying mathlib `FullSubcategory` provides those instances). -/
abbrev natBTV20Inclusion : LawvereNatBTV20Cat ⥤ LawvereNatBTV2Cat :=
  isNatBTV20.ι

/-- Terminal object `(0, 0)` lifted to the subcategory. -/
def lawvereNatBTV20Terminal :
    ChosenTerminal LawvereNatBTV20Cat where
  obj := ⟨(0, 0), rfl⟩
  from_ a := ObjectProperty.homMk
    (cfpTerminalFrom (C := LawvereNatBTV2Cat) a.obj)
  uniq := fun f => by
    apply ObjectProperty.hom_ext
    exact (NatBTMorNV2Quo.terminal_uniq f.hom).trans
      (NatBTMorNV2Quo.terminal_uniq _).symm

/-- Binary product in the subcategory.  The underlying product
object `(a.1 + b.1, a.2 + b.2)` has BT arity `0 + 0 = 0`,
inherited from the parent's chosen finite products. -/
def lawvereNatBTV20Product (a b : LawvereNatBTV20Cat) :
    ChosenBinaryProduct a b where
  obj := ⟨(a.obj.1 + b.obj.1, a.obj.2 + b.obj.2), by
    change a.obj.2 + b.obj.2 = 0
    rw [a.property, b.property]⟩
  fst := ObjectProperty.homMk
    (cfpFst (C := LawvereNatBTV2Cat) a.obj b.obj)
  snd := ObjectProperty.homMk
    (cfpSnd (C := LawvereNatBTV2Cat) a.obj b.obj)
  lift f g := ObjectProperty.homMk
    (cfpLift (C := LawvereNatBTV2Cat) f.hom g.hom)
  lift_fst f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpFst _ _ = f.hom
    exact NatBTMorNV2Quo.pair_fst f.hom g.hom
  lift_snd f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpSnd _ _ = g.hom
    exact NatBTMorNV2Quo.pair_snd f.hom g.hom
  lift_uniq f g h hf hs := by
    apply ObjectProperty.hom_ext
    change h.hom = cfpLift f.hom g.hom
    apply NatBTMorNV2Quo.pair_uniq
    · have := hf
      exact congrArg (·.hom) this
    · have := hs
      exact congrArg (·.hom) this

instance : HasChosenFiniteProducts LawvereNatBTV20Cat where
  terminal := lawvereNatBTV20Terminal
  product := lawvereNatBTV20Product

end GebLean
