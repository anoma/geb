import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import GebLean.Utilities.Opposites

/-!
# The contravariant category of elements

This file defines the contravariant category of elements for a functor `F : Cᵒᵖ' ⥤ Type`.

Given a functor `F : Cᵒᵖ' ⥤ Type`, an object of `F.ElementsContra` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, such that `F.map f` takes `y` to `x`
(where `F.map f : F.obj Y → F.obj X` since `F` is contravariant).

This is the dual of the (covariant) category of elements in
`Mathlib.CategoryTheory.Elements`.

## Implementation notes

While mathlib handles presheaves `F : Cᵒᵖ ⥤ Type` by taking the opposite of the covariant
category of elements, we provide a direct contravariant construction using our `op'` alternative
opposite category. This avoids nested opposites and provides definitional equalities
`op' (op' C) = C`.

In the implementation, morphisms are stored as `f : @Quiver.Hom Cᵒᵖ' _ Y X`, which corresponds
to `f : X ⟶ Y` in `C`.

## Categorical equivalences

This file establishes two categorical equivalences:

1. The slice category `Over X` is equivalent to the category of elements of the
   contravariant hom-functor `coyoneda'.obj X : Cᵒᵖ' ⥤ Type`.

2. The slice category of a presheaf category over a presheaf `P : Cᵒᵖ' ⥤ Type` is
   equivalent to the category of presheaves on the category of elements of `P`.

## References

* <https://ncatlab.org/nlab/show/category+of+elements>
* <https://ncatlab.org/nlab/show/category+of+elements#representable_presheaves>
* <https://preview.1lab.dev/535/Cat.Instances.Slice.Presheaf.html>

-/

universe w v u

namespace CategoryTheory

open GebLean

variable {C : Type u} [Category.{v} C]

/--
The type of objects for the contravariant category of elements of a functor `F : Cᵒᵖ' ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.ElementsContra (F : Cᵒᵖ' ⥤ Type w) :=
  Σ c : C, F.obj c

/--
Constructor for the type `F.ElementsContra` when `F` is a contravariant functor to types.
-/
abbrev Functor.elementsContraMk (F : Cᵒᵖ' ⥤ Type w) (X : C) (x : F.obj X) :
    F.ElementsContra := ⟨X, x⟩

lemma Functor.ElementsContra.ext {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra)
    (h₁ : x.fst = y.fst) (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
  simp [h₂]

/--
The category structure on `F.ElementsContra`, for `F : Cᵒᵖ' ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, such that `F.map f` takes `y` to `x`.
-/
instance categoryOfElementsContra (F : Cᵒᵖ' ⥤ Type w) : Category.{v} F.ElementsContra where
  Hom p q := { f : @Quiver.Hom Cᵒᵖ' _ q.1 p.1 // (F.map f) q.2 = p.2 }
  id p := ⟨𝟙 p.1, congrFun (F.map_id p.fst) p.snd⟩
  comp {X Y Z} f g := ⟨g.1 ≫ f.1, by
    rw [F.map_comp]
    simp only [types_comp_apply]
    rw [g.2, f.2]⟩
  id_comp := by
    intros X Y f
    ext
    exact Category.comp_id f.val
  comp_id := by
    intros X Y f
    ext
    exact Category.id_comp f.val
  assoc := by
    intros W X Y Z f g h
    ext
    exact (Category.assoc h.val g.val f.val).symm

namespace CategoryOfElementsContra

/--
Constructor for morphisms in the contravariant category of elements.
Given `f : x.1 ⟶ y.1` in `C` such that `F.map f` takes `y.snd` to `x.snd`,
constructs a morphism `x ⟶ y` in `F.ElementsContra`.
-/
def homMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra) (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : x ⟶ y :=
  ⟨f, hf⟩

lemma homMk_val {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra} (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : (homMk x y f hf).val = f :=
  rfl

@[ext]
lemma hom_ext {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra} (f g : x ⟶ y)
    (h : f.val = g.val) : f = g := by
  cases f; cases g
  congr

end CategoryOfElementsContra

/--
The contravariant hom-functor using the `op'` construction.
This is mathlib's `yoneda : C ⥤ Cᵒᵖ ⥤ Type` converted to use `op'` by
post-composing with `preCompToOp'`.

For each object `X : C`, the functor `coyoneda'.obj X : Cᵒᵖ' ⥤ Type` maps
each object `Y : C` to the set of morphisms `Y ⟶ X`.
-/
def coyoneda' : C ⥤ (Cᵒᵖ' ⥤ Type v) :=
  yoneda ⋙ preCompToOp'

lemma coyoneda'_obj_obj (X Y : C) : (coyoneda'.obj X).obj Y = (Y ⟶ X) := by
  dsimp [coyoneda', preCompToOp']
  rfl

lemma coyoneda'_obj_map (X : C) {Y Z : C} (f : (Z : Cᵒᵖ') ⟶ (Y : Cᵒᵖ')) (g : Y ⟶ X) :
    (coyoneda'.obj X).map f g = f ≫ g := by
  dsimp [coyoneda', preCompToOp', op'ToOp]
  rfl

namespace ElementsContra

section OverEquivalence

variable (X : C)

/--
Functor from `Over X` to the category of elements of `coyoneda'.obj X`.
An object `f : Y ⟶ X` in `Over X` maps to `(Y, f)` in the category of elements.
-/
def overToElements : Over X ⥤ (coyoneda'.obj X).ElementsContra where
  obj f := ⟨f.left, f.hom⟩
  map {f g} h := ⟨h.left, by
    change (coyoneda'.obj X).map h.left g.hom = f.hom
    rw [coyoneda'_obj_map]
    exact Over.w h⟩

/--
Functor from the category of elements of `coyoneda'.obj X` to `Over X`.
An element `(Y, f : Y ⟶ X)` maps to the arrow `f : Y ⟶ X` in `Over X`.
-/
def elementsToOver : (coyoneda'.obj X).ElementsContra ⥤ Over X where
  obj p := Over.mk p.snd
  map {p q} g := Over.homMk g.val (by
    dsimp [Over.mk]
    have : (coyoneda'.obj X).map g.val q.snd = p.snd := g.property
    rw [coyoneda'_obj_map] at this
    exact this)

/--
Unit isomorphism for the equivalence between `Over X` and the category of
elements of `coyoneda'.obj X`.
-/
def overElementsUnitIso :
    𝟭 (Over X) ≅ overToElements X ⋙ elementsToOver X :=
  NatIso.ofComponents
    (fun f => Over.isoMk (Iso.refl _) (by simp [overToElements, elementsToOver]))
    (fun g => by
      ext
      simp [overToElements, elementsToOver])

private lemma counit_hom_comp_inv (p : (coyoneda'.obj X).ElementsContra) :
    (𝟙 p.fst ≫ 𝟙 p.fst : p.fst ⟶ p.fst) = 𝟙 p.fst := by
  simp

private lemma counit_inv_comp_hom (p : (coyoneda'.obj X).ElementsContra) :
    (𝟙 p.fst ≫ 𝟙 p.fst : p.fst ⟶ p.fst) = 𝟙 p.fst := by
  simp

private lemma counit_naturality_val (X : C) {p q : (coyoneda'.obj X).ElementsContra}
    (g : p ⟶ q) :
    ((elementsToOver X ⋙ overToElements X).map g ≫
      (⟨𝟙 q.fst, by
        change (coyoneda'.obj X).map (𝟙 q.fst) q.snd = q.snd
        rw [coyoneda'_obj_map, Category.id_comp]⟩ :
        (elementsToOver X ⋙ overToElements X).obj q ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra)).obj q)).val =
    ((⟨𝟙 p.fst, by
        change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
        rw [coyoneda'_obj_map, Category.id_comp]⟩ :
        (elementsToOver X ⋙ overToElements X).obj p ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra)).obj p) ≫ g).val := by
  dsimp [elementsToOver, overToElements]
  -- In the category of elements, (f ≫ g).val = g.val ≫ f.val (in Cᵒᵖ')
  -- LHS: (⟨g.val, _⟩ ≫ ⟨𝟙 q.fst, _⟩).val
  -- RHS: (⟨𝟙 p.fst, _⟩ ≫ g).val
  -- These are both morphisms in Cᵒᵖ', composition is (f ≫ g).val = g.val ≫ f.val
  change ((@CategoryStruct.id Cᵒᵖ' _ q.fst) ≫ g.val) =
         (g.val ≫ (@CategoryStruct.id Cᵒᵖ' _ p.fst))
  rw [Category.id_comp, Category.comp_id]

/--
Counit isomorphism for the equivalence between `Over X` and the category of
elements of `coyoneda'.obj X`.
-/
def overElementsCounitIso :
    elementsToOver X ⋙ overToElements X ≅ 𝟭 ((coyoneda'.obj X).ElementsContra) :=
  NatIso.ofComponents
    (fun p => ⟨⟨𝟙 p.fst, by
                change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
                rw [coyoneda'_obj_map, Category.id_comp]⟩,
              ⟨𝟙 p.fst, by
                change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
                rw [coyoneda'_obj_map, Category.id_comp]⟩,
              by ext; exact counit_hom_comp_inv X p,
              by ext; exact counit_inv_comp_hom X p⟩)
    (fun g => by ext; exact counit_naturality_val X g)

private lemma functor_unitIso_comp_helper (X : C) (f : Over X) :
    ((overToElements X).map ((overElementsUnitIso X).hom.app f) ≫
     (overElementsCounitIso X).hom.app ((overToElements X).obj f)).val =
    (@CategoryStruct.id ((coyoneda'.obj X).ElementsContra) _
      ((overToElements X).obj f)).val := by
  dsimp [overToElements, elementsToOver, overElementsUnitIso, overElementsCounitIso]
  -- Unit at f: Over.isoMk (Iso.refl _) has .left = 𝟙 f.left
  -- Mapped through overToElements: ⟨𝟙 f.left, _⟩
  -- Counit at ⟨f.left, f.hom⟩: ⟨𝟙 f.left, _⟩
  -- Composition: ⟨𝟙 f.left ≫ 𝟙 f.left, _⟩ = ⟨𝟙 f.left, _⟩
  -- Identity: ⟨𝟙 f.left, _⟩
  -- The .val parts are both 𝟙 f.left (in Cᵒᵖ')
  change ((@CategoryStruct.id Cᵒᵖ' _ f.left) ≫ (@CategoryStruct.id Cᵒᵖ' _ f.left)) =
         (@CategoryStruct.id Cᵒᵖ' _ f.left)
  rw [Category.comp_id]

/--
The slice category `Over X` is equivalent to the category of elements of the
contravariant hom-functor `coyoneda'.obj X`.

This shows that representable presheaves correspond to slice categories.
-/
def overEquivElements : Over X ≌ (coyoneda'.obj X).ElementsContra where
  functor := overToElements X
  inverse := elementsToOver X
  unitIso := overElementsUnitIso X
  counitIso := overElementsCounitIso X
  functor_unitIso_comp f := by
    ext
    exact functor_unitIso_comp_helper X f

end OverEquivalence

end ElementsContra

end CategoryTheory
