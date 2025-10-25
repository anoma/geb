import Mathlib.CategoryTheory.Elements
import GebLean.Utilities.Opposites

/-!
# The contravariant category of elements

This file defines the contravariant category of elements for a functor `F : Cᵒᵖ' ⥤ Type`.

Given a functor `F : Cᵒᵖ' ⥤ Type`, an object of `F.ElementsContra` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : Y ⟶ X` in `C` (note the direction reversal),
such that `F.map f` takes `y` to `x`.

This is the dual of the (covariant) category of elements in
`Mathlib.CategoryTheory.Elements`.

## Implementation notes

While mathlib handles presheaves `F : Cᵒᵖ ⥤ Type` by taking the opposite of the covariant
category of elements, we provide a direct contravariant construction using our `op'` alternative
opposite category. This avoids nested opposites and provides definitional equalities
`op' (op' C) = C`.

## References

* <https://ncatlab.org/nlab/show/category+of+elements>

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
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`,
such that `F.map f` takes `y` to `x` (since `F` is contravariant, `F.map f : F.obj Y → F.obj X`).
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
Constructor for morphisms in the contravariant category of elements of a functor to types.
-/
def homMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra) (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : x ⟶ y :=
  ⟨f, hf⟩

lemma homMk_val {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra} (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : (homMk x y f hf).val = f :=
  rfl

end CategoryOfElementsContra

end CategoryTheory
