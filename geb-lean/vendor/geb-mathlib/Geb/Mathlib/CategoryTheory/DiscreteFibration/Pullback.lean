/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.DiscreteFibration.Basic

/-!
# Discrete fibrations: the codomain square

The internal formulation of a discrete fibration ([LoregianRiehl2018]
§ 2.1, Definition `internaldefn`; [nLabDiscreteFibration]): the square

```
Arrow C ---right---> C
   |                 |
   | p               | p
   v                 v
Arrow B ---right---> B
```

of codomain maps is a pullback of types.

## Main definitions

* `CodPullback p`, the pullback `Arrow B ×_B C` of types.
* `codPair p`, the comparison map `Arrow C → Arrow B ×_B C`.
* `IsDiscreteFibration p`, the proposition that `codPair p` is a
  bijection.

## Main statements

* `DiscreteFibration.isDiscreteFibration`: lifting data forces the square
  to be a pullback.  The converse needs `Classical.choice` and lives in
  `Geb/Mathlib/CategoryTheory/DiscreteFibration/Packaged.lean`.

## References

* [LoregianRiehl2018]
* [nLabDiscreteFibration]

## Tags

discrete fibration, pullback, arrow category
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]

/-- The set-theoretic pullback `Arrow B ×_B C` of `right : Arrow B → B`
along `p : C → B`: an arrow of `B` with an object of `C` over its
codomain. -/
abbrev CodPullback (p : C ⥤ B) : Type (max u₁ u₂ v₂) :=
  { q : Arrow B × C // q.1.right = p.obj q.2 }

/-- The comparison map `(p, right) : Arrow C → Arrow B ×_B C`. -/
def codPair (p : C ⥤ B) (a : Arrow C) : CodPullback p :=
  ⟨(Arrow.mk (p.map a.hom), a.right), rfl⟩

@[simp] theorem codPair_val (p : C ⥤ B) (a : Arrow C) :
    (codPair p a).val = (Arrow.mk (p.map a.hom), a.right) := rfl

/-- The pullback-square formulation: `p` is a discrete fibration iff its
codomain square is a pullback of sets, i.e. iff `codPair p` is a
bijection. -/
def IsDiscreteFibration (p : C ⥤ B) : Prop := Function.Bijective (codPair p)

/-- Lifting data forces the codomain square to be a pullback.
No choice is used. -/
theorem DiscreteFibration.isDiscreteFibration {p : C ⥤ B}
    (D : DiscreteFibration p) : IsDiscreteFibration p := by
  constructor
  · rintro ⟨x₁, y₁, f₁⟩ ⟨x₂, y₂, f₂⟩ h
    have hy : y₁ = y₂ := congrArg (fun q : CodPullback p => q.val.2) h
    subst hy
    have hf : Arrow.mk (p.map f₁) = Arrow.mk (p.map f₂) :=
      congrArg (fun q : CodPullback p => q.val.1) h
    exact (D.eq_liftArrow (p.map f₂) f₁ hf).trans
      (D.eq_liftArrow (p.map f₂) f₂ rfl).symm
  · rintro ⟨⟨⟨X, Y, g⟩, c⟩, (hg : Y = p.obj c)⟩
    subst hg
    exact ⟨D.liftArrow g, Subtype.ext (Prod.ext (D.arrow_mk_map_hom g) rfl)⟩

/-- Auxiliary: an arrow equal to `Arrow.mk h` gives back `h` up to
transport of the codomain. -/
theorem sigma_eq_of_arrow_eq {c c' : C} (h : c' ⟶ c) (a : Arrow C)
    (ha' : a = Arrow.mk h) (ha : a.right = c) :
    (⟨c', h⟩ : Σ c', c' ⟶ c) = ⟨a.left, a.hom ≫ eqToHom ha⟩ := by
  subst ha'
  simp

end CategoryTheory
