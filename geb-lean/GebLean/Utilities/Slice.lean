import Mathlib.CategoryTheory.Comma.Over.Basic
import GebLean.Utilities.Opposites
import GebLean.Utilities.Presheaf

/-!
# Slice and coslice category utilities

This module provides utilities for working with slice (over) and coslice (under)
categories, including equivalences involving opposite categories.

## Main definitions

* `underEquivOverOp'Op'` - Equivalence between `Under X` and `(Over X)ᵒᵖ'` in `Dᵒᵖ'`
* `overOpMapFunctor` - Functor `C ⥤ Cat` sending `y` to `(Over y)ᵒᵖ'`
* `OverOpPresheaf` - Presheaves on `(Over y)ᵒᵖ'`
* `overOpCopresheafFunctor` - Functor `Cᵒᵖ' ⥤ Cat` sending `y` to copresheaves on
  `(Over y)ᵒᵖ'`
-/

universe v u

namespace GebLean

open CategoryTheory

section UnderOverEquivalence

variable {D : Type u} [Category.{v} D] (X : D)

/--
Functor from `Under X` in `D` to `(Over X)ᵒᵖ'` in `Dᵒᵖ'`.

An object `(Y, f : X ⟶ Y)` in `Under X` maps to `(Y, f)` viewed as an object
in `Over (X : Dᵒᵖ')` (where `f : Y ⟶ X` in `Dᵒᵖ'`).

Morphisms are reversed: `g : u.right ⟶ v.right` in `D` becomes
`g : v.left ⟶ u.left` in `(Over X)ᵒᵖ'`.
-/
def underToOverOp'Op' : Under X ⥤ (@Over Dᵒᵖ' _ X)ᵒᵖ' where
  obj u := Over.mk (u.hom : @Quiver.Hom Dᵒᵖ' _ u.right X)
  map {u v} f := Over.homMk (f.right : @Quiver.Hom Dᵒᵖ' _ v.right u.right) (by
    dsimp [Over.mk]
    exact Under.w f)

/--
Functor from `(Over X)ᵒᵖ'` in `Dᵒᵖ'` to `Under X` in `D`.
-/
def overOp'Op'ToUnder : (@Over Dᵒᵖ' _ X)ᵒᵖ' ⥤ Under X where
  obj o := Under.mk (o.hom : @Quiver.Hom D _ X o.left)
  map {o p} f := Under.homMk (f.left : @Quiver.Hom D _ o.left p.left) (by
    dsimp [Under.mk]
    exact Over.w f)

/--
Unit isomorphism for the equivalence `Under X ≌ (Over (X : Dᵒᵖ'))ᵒᵖ'`.
-/
def underOverOp'Op'UnitIso :
    𝟭 (Under X) ≅ underToOverOp'Op' X ⋙ overOp'Op'ToUnder X :=
  NatIso.ofComponents
    (fun u => Under.isoMk (Iso.refl _) (by simp [underToOverOp'Op', overOp'Op'ToUnder]))
    (fun {u v} f => by
      ext
      simp [underToOverOp'Op', overOp'Op'ToUnder])

/--
Component isomorphism for counit: an object in `(Over X)ᵒᵖ'` is isomorphic to
the round-trip through Under and back.
-/
def underOverOp'Op'CounitComponent (o : (@Over Dᵒᵖ' _ X)ᵒᵖ') :
    (overOp'Op'ToUnder X ⋙ underToOverOp'Op' X).obj o ≅ o := by
  let lhs := (overOp'Op'ToUnder X ⋙ underToOverOp'Op' X).obj o
  have h_left_eq : lhs.left = o.left := rfl
  have h_hom_eq : lhs.hom = o.hom := rfl
  exact @Iso.refl (@Over Dᵒᵖ' _ X)ᵒᵖ' _ o

/--
Counit isomorphism for the equivalence `Under X ≌ (Over (X : Dᵒᵖ'))ᵒᵖ'`.
-/
def underOverOp'Op'CounitIso :
    overOp'Op'ToUnder X ⋙ underToOverOp'Op' X ≅ 𝟭 ((@Over Dᵒᵖ' _ X)ᵒᵖ') :=
  NatIso.ofComponents
    (fun o => underOverOp'Op'CounitComponent X o)
    (fun {o p} f => by
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        underOverOp'Op'CounitComponent, Iso.refl_hom]
      apply Over.OverMorphism.ext
      simp only [underToOverOp'Op', overOp'Op'ToUnder, Under.homMk_right]
      unfold CategoryOp'Inst CategoryStruct.comp at *
      simp only [commaCategory, instCategoryOver, Over.homMk_left]
      change 𝟙 p.left ≫ f.left = f.left ≫ 𝟙 o.left
      simp only [Category.comp_id, Category.id_comp])

/--
The under category of `X` in `D` is equivalent to the opposite of the over
category of `X` in `Dᵒᵖ'`.

This maps an arrow `f : X ⟶ Y` in `Under X` to the same arrow viewed as
`f : Y ⟶ X` in `Over X` (in `Dᵒᵖ'`), with morphisms reversed.
-/
def underEquivOverOp'Op' : Under X ≌ (@Over Dᵒᵖ' _ X)ᵒᵖ' where
  functor := underToOverOp'Op' X
  inverse := overOp'Op'ToUnder X
  unitIso := underOverOp'Op'UnitIso X
  counitIso := underOverOp'Op'CounitIso X
  functor_unitIso_comp X := by
    simp only [Functor.comp_obj, underOverOp'Op'UnitIso, NatIso.ofComponents_hom_app,
      underOverOp'Op'CounitIso, underOverOp'Op'CounitComponent, Iso.refl_hom]
    apply Over.OverMorphism.ext
    simp only [underToOverOp'Op', overOp'Op'ToUnder, Under.isoMk_hom_right, Iso.refl_hom]
    unfold CategoryOp'Inst CategoryStruct.comp at *
    simp only [commaCategory, instCategoryOver, Over.homMk_left]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]

end UnderOverEquivalence

section OverOpFunctors

variable (C : Type u) [Category.{v} C]

/--
The functor `C ⥤ Cat` sending `y` to `Cat.of ((Over y)ᵒᵖ')` and
`h : y ⟶ y'` to `(Over.map h).op' : (Over y)ᵒᵖ' ⥤ (Over y')ᵒᵖ'`.

This is `Over.mapFunctor` postcomposed with the opposite-category functor.
-/
def overOpMapFunctor : C ⥤ Cat :=
  Cat.postCompOpFunctor'.obj (Over.mapFunctor C)

/--
Precomposition with `(overOpMapFunctor C).map h` for a morphism `h : y ⟶ y'`.
-/
def precompOverOpMap {y y' : C} (h : y ⟶ y') :
    ((Over y')ᵒᵖ' ⥤ Type v) ⥤ ((Over y)ᵒᵖ' ⥤ Type v) :=
  (Functor.whiskeringLeft ((Over y)ᵒᵖ') (Over y')ᵒᵖ' (Type v)).obj
    ((overOpMapFunctor C).map h)

/--
The type of presheaves on `(Over y)ᵒᵖ'` for a fixed `y : C`.
-/
abbrev OverOpPresheaf (y : C) := Presheaf (Over y)

/--
Functor `Cᵒᵖ' ⥤ Cat` sending `y` to the category of copresheaves on `(Over y)ᵒᵖ'`.

For a morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is `h : y' ⟶ y` as a C-morphism),
the induced functor is precomposition with `(Over.map h).op' : (Over y')ᵒᵖ' ⥤ (Over y)ᵒᵖ'`,
giving `((Over y)ᵒᵖ' ⥤ Type v) ⥤ ((Over y')ᵒᵖ' ⥤ Type v)`.
-/
def overOpCopresheafFunctor : Cᵒᵖ' ⥤ Cat :=
  Functor.op' (overOpMapFunctor C) ⋙ copresheafConstruction

end OverOpFunctors

end GebLean
