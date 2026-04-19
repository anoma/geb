import GebLean.LawvereNatBTBoundedQuot
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import GebLean.Utilities.ComputableLimits

/-!
# `LawvereNatBTBounded0Cat`: the `m = 0` Full Subcategory of
`LawvereNatBTBounded`

The full subcategory of `LawvereNatBTBoundedCat` whose objects
have BT arity zero.  Used as the `(n, 0)`-restricted subcategory
for the equivalence with `LawvereERCat` in Stage 5 of the
Option E plan.

`LawvereNatBTBounded0Cat` inherits its `HasChosenFiniteProducts`
from `LawvereNatBTBoundedCat`: the product of `(n₁, 0)` and
`(n₂, 0)` is `(n₁ + n₂, 0)`, still in the subcategory; the
terminal `(0, 0)` is also in the subcategory.

The two-stage architecture is documented in
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`.
-/

namespace GebLean

open CategoryTheory

/-- Selects `LawvereNatBTBoundedCat` objects whose BT arity is
zero. -/
def isNatBTBounded0 : ObjectProperty LawvereNatBTBoundedCat :=
  fun nm => nm.2 = 0

/-- The full subcategory of `LawvereNatBTBoundedCat` on `m = 0`
objects. -/
abbrev LawvereNatBTBounded0Cat : Type :=
  isNatBTBounded0.FullSubcategory

/-- Inclusion functor.  Full and faithful by construction (the
underlying mathlib `FullSubcategory` provides those instances). -/
abbrev natBTBounded0Inclusion :
    LawvereNatBTBounded0Cat ⥤ LawvereNatBTBoundedCat :=
  isNatBTBounded0.ι

/-- Terminal object `(0, 0)` lifted to the subcategory. -/
def lawvereNatBTBounded0Terminal :
    ChosenTerminal LawvereNatBTBounded0Cat where
  obj := ⟨(0, 0), rfl⟩
  from_ a := ObjectProperty.homMk
    (cfpTerminalFrom (C := LawvereNatBTBoundedCat) a.obj)
  uniq := fun f => by
    apply ObjectProperty.hom_ext
    exact (NatBTMorNBoundedQuo.terminal_uniq f.hom).trans
      (NatBTMorNBoundedQuo.terminal_uniq _).symm

/-- Binary product in the subcategory.  The underlying product
object `(a.1 + b.1, a.2 + b.2)` has BT arity `0 + 0 = 0`,
inherited from the parent's chosen finite products. -/
def lawvereNatBTBounded0Product (a b : LawvereNatBTBounded0Cat) :
    ChosenBinaryProduct a b where
  obj := ⟨(a.obj.1 + b.obj.1, a.obj.2 + b.obj.2), by
    change a.obj.2 + b.obj.2 = 0
    rw [a.property, b.property]⟩
  fst := ObjectProperty.homMk
    (cfpFst (C := LawvereNatBTBoundedCat) a.obj b.obj)
  snd := ObjectProperty.homMk
    (cfpSnd (C := LawvereNatBTBoundedCat) a.obj b.obj)
  lift f g := ObjectProperty.homMk
    (cfpLift (C := LawvereNatBTBoundedCat) f.hom g.hom)
  lift_fst f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpFst _ _ = f.hom
    exact NatBTMorNBoundedQuo.pair_fst f.hom g.hom
  lift_snd f g := by
    apply ObjectProperty.hom_ext
    change cfpLift f.hom g.hom ≫ cfpSnd _ _ = g.hom
    exact NatBTMorNBoundedQuo.pair_snd f.hom g.hom
  lift_uniq f g h hf hs := by
    apply ObjectProperty.hom_ext
    change h.hom = cfpLift f.hom g.hom
    apply NatBTMorNBoundedQuo.pair_uniq
    · have := hf
      exact congrArg (·.hom) this
    · have := hs
      exact congrArg (·.hom) this

instance : HasChosenFiniteProducts LawvereNatBTBounded0Cat where
  terminal := lawvereNatBTBounded0Terminal
  product := lawvereNatBTBounded0Product

end GebLean
