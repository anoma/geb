import GebLean.Utilities.Opposites
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Presheaf and Copresheaf Construction Functors

This module defines functors that send a category to its category of presheaves
or copresheaves.

## Main definitions

* `Copresheaf C` - The type of copresheaves on `C`, i.e., functors `C ⥤ Type v`
* `Presheaf C` - The type of presheaves on `C`, i.e., functors `Cᵒᵖ' ⥤ Type v`
* `copresheafConstruction` - Functor `Catᵒᵖ' ⥤ Cat` sending `C` to `C ⥤ Type v`
* `presheafConstruction` - Functor `Catᵒᵖ' ⥤ Cat` sending `C` to `Cᵒᵖ' ⥤ Type v`

Both constructions are contravariant because for a functor `F : C ⥤ D`,
precomposition induces functors in the opposite direction:
- The induced functor on copresheaves is `(D ⥤ Type v) ⥤ (C ⥤ Type v)` via
  precomposition with `F`.
- The induced functor on presheaves is `(Dᵒᵖ' ⥤ Type v) ⥤ (Cᵒᵖ' ⥤ Type v)` via
  precomposition with `F.op'`.
-/

universe v u

namespace GebLean

open CategoryTheory

/--
The copresheaf category of a category `C`: functors `C ⥤ Type v`.
-/
abbrev Copresheaf (C : Type u) [Category.{v} C] := C ⥤ Type v

/--
The presheaf category of a category `C`: functors `Cᵒᵖ' ⥤ Type v`.
-/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ' ⥤ Type v

/--
The map component of `copresheafConstruction`. For a functor `F : C ⥤ D`,
returns the precomposition functor `(D ⥤ Type v) ⥤ (C ⥤ Type v)`.
-/
def copresheafConstructionMap {C D : Cat.{v, u}} :
    (C ⥤ D) ⥤ (Cat.of (↑D ⥤ Type v) ⥤ Cat.of (↑C ⥤ Type v)) :=
  Functor.whiskeringLeft (↑C) (↑D) (Type v)

/--
The copresheaf construction functor (contravariant).

For a category `C`, this returns the category of copresheaves `C ⥤ Type v`.
For a functor `F : D ⥤ C` (which is a morphism `C ⟶ D` in `Catᵒᵖ'`), this
returns the precomposition functor `(C ⥤ Type v) ⥤ (D ⥤ Type v)` given by
`G ↦ F ⋙ G`.

This is contravariant: the induced functor on copresheaves goes in the opposite
direction to the original functor.
-/
def copresheafConstruction :
    Cat.{v, u}ᵒᵖ' ⥤ Cat.{max u v, max u v (v + 1)} where
  obj (C : Cat.{v, u}) := Cat.of (↑C ⥤ Type v)
  map {C D : Cat.{v, u}} (F : @Quiver.Hom Cat.{v, u}ᵒᵖ' _ C D) :=
    ((Functor.whiskeringLeft (↑D : Type u) (↑C : Type u) (Type v)).obj
      F.toFunctor).toCatHom
  map_id _ := by
    apply Cat.Hom.ext
    rfl
  map_comp _ _ := by
    apply Cat.Hom.ext
    rfl

/--
The map component of `presheafConstruction`. For a functor `F : C ⥤ D`,
returns the precomposition functor `(Dᵒᵖ' ⥤ Type v) ⥤ (Cᵒᵖ' ⥤ Type v)`.

Since `F : C ⥤ D` gives `F.op' : Cᵒᵖ' ⥤ Dᵒᵖ'`, precomposition with `F.op'`
maps presheaves on `D` to presheaves on `C`.
-/
def presheafConstructionMap {C D : Cat.{v, u}} :
    (C ⥤ D)ᵒᵖ' ⥤
    (Cat.of ((↑D : Type u)ᵒᵖ' ⥤ Type v) ⥤ Cat.of ((↑C : Type u)ᵒᵖ' ⥤ Type v)) :=
  Functor.opHom' (C := ↑C) (D := ↑D) ⋙
  Functor.whiskeringLeft (↑C : Type u)ᵒᵖ' (↑D : Type u)ᵒᵖ' (Type v)

/--
The presheaf construction functor (contravariant).

For a category `C`, this returns the category of presheaves `Cᵒᵖ' ⥤ Type v`.
For a functor `F : D ⥤ C` (which is a morphism `C ⟶ D` in `Catᵒᵖ'`), this
returns the precomposition functor `(Cᵒᵖ' ⥤ Type v) ⥤ (Dᵒᵖ' ⥤ Type v)` given
by `G ↦ F.op' ⋙ G`.

This is contravariant: the induced functor on presheaves goes in the opposite
direction to the original functor.
-/
def presheafConstruction :
    Cat.{v, u}ᵒᵖ' ⥤ Cat.{max u v, max u v (v + 1)} where
  obj (C : Cat.{v, u}) := Cat.of ((↑C : Type u)ᵒᵖ' ⥤ Type v)
  map {C D : Cat.{v, u}} (F : @Quiver.Hom Cat.{v, u}ᵒᵖ' _ C D) :=
    ((Functor.whiskeringLeft (↑D : Type u)ᵒᵖ' (↑C : Type u)ᵒᵖ' (Type v)).obj
      (Functor.op' F.toFunctor)).toCatHom
  map_id _ := by
    apply Cat.Hom.ext
    rfl
  map_comp _ _ := by
    apply Cat.Hom.ext
    rfl

/-! ### Pullbacks of presheaf morphisms

Computable pullback cone for morphisms in functor
categories `C ⥤ Type w`, constructed pointwise from
`Types.pullbackLimitCone` via
`PullbackCone.combine`.  At each object `T`, the
fiber is `{ (a, b) : F(T) × G(T) | f(a) = g(b) }`.
-/

section PresheafPullback

open Limits

universe w

variable {C : Type u} [Category.{v} C]
  {F G H : C ⥤ Type w}

/-- The pullback cone for two presheaf morphisms with
common target, obtained by combining the pointwise
pullback cones in `Type w`. -/
def presheafPullbackCone
    (f : F ⟶ H) (g : G ⟶ H) :
    PullbackCone f g :=
  PullbackCone.combine f g
    (fun X =>
      Types.pullbackCone (f.app X) (g.app X))
    (fun X =>
      (Types.pullbackLimitCone
        (f.app X) (g.app X)).isLimit)

/-- The presheaf pullback cone is a limit. -/
def presheafPullbackIsLimit
    (f : F ⟶ H) (g : G ⟶ H) :
    IsLimit (presheafPullbackCone f g) :=
  PullbackCone.combineIsLimit f g
    (fun X =>
      Types.pullbackCone (f.app X) (g.app X))
    (fun X =>
      (Types.pullbackLimitCone
        (f.app X) (g.app X)).isLimit)

/-- The pullback object of two presheaf morphisms. -/
abbrev presheafPullback
    (f : F ⟶ H) (g : G ⟶ H) : C ⥤ Type w :=
  (presheafPullbackCone f g).pt

/-- First projection from the presheaf pullback. -/
abbrev presheafPullbackFst
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullback f g ⟶ F :=
  (presheafPullbackCone f g).fst

/-- Second projection from the presheaf pullback. -/
abbrev presheafPullbackSnd
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullback f g ⟶ G :=
  (presheafPullbackCone f g).snd

end PresheafPullback

end GebLean
