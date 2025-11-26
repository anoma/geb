import GebLean.Utilities.Elements
import GebLean.Utilities.TwistedArrow

/-!
# Functor categories on twisted arrow categories

This module defines functor categories from the four twisted arrow category
variants to `Type v`:

- `TwArrCopresheaf C` = `TwistedArrow' C ⥤ Type v` (copresheaves on Tw)
- `TwArrPresheaf C` = `OpTwistedArrow' C ⥤ Type v` (presheaves on Tw)
- `TwArrOpCopresheaf C` = `TwistedArrowOp' C ⥤ Type v` (copresheaves on TwOp)
- `TwArrOpPresheaf C` = `CoTwistedArrow C ⥤ Type v` (presheaves on TwOp)

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, functors from `OpTwistedArrow'`
are presheaves on `TwistedArrow'`. Similarly, since
`CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, functors from `CoTwistedArrow`
are presheaves on `TwistedArrowOp'`.

Two of these have direct slice equivalences via `sliceEquivCopresheaf`:
- `Over hom' ≌ TwArrCopresheaf C`
- `Over homOp' ≌ TwArrOpCopresheaf C`
-/

universe v u

namespace GebLean

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
Copresheaves on the twisted arrow category: covariant functors from
`TwistedArrow' C` to `Type v`.
-/
def TwArrCopresheaf := TwistedArrow' C ⥤ Type v

instance : Category (TwArrCopresheaf C) := by
  unfold TwArrCopresheaf
  infer_instance

/--
The slice category over `hom'` is equivalent to the category of copresheaves
on the twisted arrow category.
-/
def sliceEquivTwArrCopresheaf : Over (hom' (C := C)) ≌ TwArrCopresheaf C :=
  sliceEquivCopresheaf (hom' (C := C))

/--
Presheaves on the twisted arrow category: covariant functors from
`OpTwistedArrow' C` to `Type v`.

Since `OpTwistedArrow' C ≅ (TwistedArrow' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrow' C`, i.e., presheaves.
-/
def TwArrPresheaf := OpTwistedArrow' C ⥤ Type v

instance : Category (TwArrPresheaf C) := by
  unfold TwArrPresheaf
  infer_instance

/--
Copresheaves on the opposite-variant twisted arrow category: covariant functors
from `TwistedArrowOp' C` to `Type v`.
-/
def TwArrOpCopresheaf := TwistedArrowOp' C ⥤ Type v

instance : Category (TwArrOpCopresheaf C) := by
  unfold TwArrOpCopresheaf
  infer_instance

/--
The slice category over `homOp'` is equivalent to the category of copresheaves
on the opposite-variant twisted arrow category.
-/
def sliceEquivTwArrOpCopresheaf : Over (homOp' (C := C)) ≌ TwArrOpCopresheaf C :=
  sliceEquivCopresheaf (homOp' (C := C))

/--
Presheaves on the opposite-variant twisted arrow category: covariant functors
from `CoTwistedArrow C` to `Type v`.

Since `CoTwistedArrow C ≅ (TwistedArrowOp' C)ᵒᵖ'`, these are contravariant
functors on `TwistedArrowOp' C`, i.e., presheaves.
-/
def TwArrOpPresheaf := CoTwistedArrow C ⥤ Type v

instance : Category (TwArrOpPresheaf C) := by
  unfold TwArrOpPresheaf
  infer_instance

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

end GebLean
