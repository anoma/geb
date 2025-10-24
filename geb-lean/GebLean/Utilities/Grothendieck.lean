import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
import GebLean.Utilities.Opposites

/-!
# The contravariant Grothendieck construction

Given a functor `F : Cᵒᵖ ⥤ Cat`, the objects of `GrothendieckContra F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj (op b)`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : f ⟶ (F.map (op β)).obj f'`.

This is the dual of the covariant Grothendieck construction in
`Mathlib.CategoryTheory.Grothendieck`, where morphisms consist of
`β : b ⟶ b'` and `φ : (F.map β).obj f ⟶ f'`.

## Implementation notes

This file dualizes `Mathlib.CategoryTheory.Grothendieck`, providing the
contravariant version of each construction. We try to adhere to mathlib
names, while placing them in the `GrothendieckContra` namespace.

To avoid issues with definitional equality of opposite categories, we
convert functors `F : Cᵒᵖ ⥤ Cat` to functors `F' : Cᵒᵖ' ⥤ Cat` using our
alternative opposite category construction `op'`, which provides
definitional equality `op' (op' C) = C`.

## References

* https://ncatlab.org/nlab/show/Grothendieck+construction#Definition

-/

universe w u v u₁ v₁ u₂ v₂

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]

/--
The contravariant Grothendieck construction for a functor `F' : Cᵒᵖ' ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F'.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`
-/
structure GrothendieckContra' (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F'.obj base

namespace GrothendieckContra'

variable {F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}}

/-- A morphism in the contravariant Grothendieck category `F' : Cᵒᵖ' ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`.
-/
structure Hom (X Y : GrothendieckContra' F') where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the source fiber object to the pullback of the target fiber object. -/
  fiber : X.fiber ⟶ (F'.map base).obj Y.fiber

@[ext (iff := false)]
theorem ext {X Y : GrothendieckContra' F'} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber ≫ eqToHom (by rw [w_base]) = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

/-- The identity morphism in the contravariant Grothendieck category.
-/
def id (X : GrothendieckContra' F') : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (fObjEq (F'.map_id X.base).symm X.fiber)

instance (X : GrothendieckContra' F') : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the contravariant Grothendieck category.
-/
def comp {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F'.map f.base).map g.fiber ≫
    eqToHom (symm <| fObjEq (F'.map_comp g.base f.base) Z.fiber)

attribute [local simp] eqToHom_map Functor.map_id

instance : Category (GrothendieckContra' F') where
  Hom X Y := GrothendieckContra'.Hom X Y
  id X := GrothendieckContra'.id X
  comp f g := GrothendieckContra'.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      simp
  id_comp {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      slice_lhs 1 3 => erw [fMapEq (F'.map_id X.base) f.fiber]
      simp
  assoc f g h := by
    ext
    · simp [comp]
    · dsimp [comp]
      slice_lhs 2 4 => erw [fMapEq (F'.map_comp g.base f.base) h.fiber]
      simp

@[simp]
theorem id_base (X : GrothendieckContra' F') : (id X).base = 𝟙 X.base := rfl

@[simp]
theorem id_fiber (X : GrothendieckContra' F') :
    (id X).fiber = eqToHom (fObjEq (F'.map_id X.base).symm X.fiber) := rfl

@[simp]
theorem comp_base {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := rfl

@[simp]
theorem comp_fiber {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fiber = f.fiber ≫ (F'.map f.base).map g.fiber ≫
      eqToHom (symm <| fObjEq (F'.map_comp g.base f.base) Z.fiber) := rfl

/--
The forgetful functor from `GrothendieckContra' F'` to `C`.
-/
@[simps]
def forget : GrothendieckContra' F' ⥤ C where
  obj X := X.base
  map f := f.base

end GrothendieckContra'

end GebLean
