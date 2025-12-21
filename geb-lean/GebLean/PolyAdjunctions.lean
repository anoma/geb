import GebLean.Polynomial

/-!
# Adjunctions Involving Polynomial Functors

This module defines adjunctions between categories of polynomial functors
and related categories (such as `Type` and slice categories).

## Adjunctions

The following adjunctions are implemented:

* Free/forgetful adjunction between polynomial functors and `Type`
* Cofree/forgetful adjunction (dual construction)
* Slice-based adjunctions relating `PolyFunctorBetweenCat X Y` to slices

These adjunctions capture the sense in which polynomial functors arise as
free constructions and have forgetful functors with both left and right
adjoints.

## References

* https://ncatlab.org/nlab/show/polynomial+functor
-/

namespace GebLean

open CategoryTheory

universe u v w

/-! ## Position Functor

The position functor extracts the "position" (index type) from a polynomial
functor. For a polynomial `P = (I, F)` where `I : Type` and `F : I → C`,
the position is `I`.

This is the forgetful functor from `CoprodCovarRepCat C` to `Type`, which
arises from the Grothendieck construction structure.
-/

section PositionFunctor

variable (C : Type u) [Category.{v} C]

/--
The position functor from `CoprodCovarRepCat C` to `Type`.

For a polynomial `P = (I, F)` where `I : Type` and `F : I → C`, this functor
returns `I`. For a morphism, it returns the reindexing function.

This is an alias for `GrothendieckContra'.forget` specialized to
`familyFunctor C ⋙ Cat.opFunctor'`.
-/
def ccrPosFunctor : CoprodCovarRepCat.{u, v, w} C ⥤ Type w :=
  GrothendieckContra'.forget (familyFunctor.{u, v, w} C ⋙ Cat.opFunctor')

@[simp]
lemma ccrPosFunctor_obj (P : CoprodCovarRepCat.{u, v, w} C) :
    (ccrPosFunctor C).obj P = ccrIndex P :=
  rfl

@[simp]
lemma ccrPosFunctor_map {P Q : CoprodCovarRepCat.{u, v, w} C} (f : P ⟶ Q) :
    (ccrPosFunctor C).map f = ccrReindex f :=
  rfl

end PositionFunctor

/-! ## Monomial Functor

For a fixed object `c : C`, the monomial functor sends a type `A` to the
polynomial functor with positions `A` and constant fiber `c` at every position.
This represents the polynomial `A · y^c` in the notation of polynomial functors.
-/

section MonomialFunctor

variable {C : Type u} [Category.{v} C]

/--
The object map of the monomial functor: sends `A : Type` to the polynomial
`(A, fun _ => c)`.
-/
def ccrMonomialObj (c : C) (A : Type w) : CoprodCovarRepCat.{u, v, w} C :=
  ccrObjMk (fun _ : A => c)

/--
The morphism map of the monomial functor: for `f : A → B`, constructs a
morphism from `(A, const c)` to `(B, const c)` using `f` as the reindexing
and identity morphisms on the fibers.
-/
def ccrMonomialMap (c : C) {A B : Type w} (f : A → B) :
    ccrMonomialObj c A ⟶ ccrMonomialObj c B :=
  ccrHomMk f (fun _ => 𝟙 c)

@[simp]
lemma ccrMonomialMap_reindex (c : C) {A B : Type w} (f : A → B) :
    ccrReindex (ccrMonomialMap c f) = f :=
  rfl

@[simp]
lemma ccrMonomialMap_fiberMor (c : C) {A B : Type w} (f : A → B) (i : A) :
    ccrFiberMor (ccrMonomialMap c f) i = 𝟙 c :=
  rfl

lemma ccrMonomialMap_id (c : C) (A : Type w) :
    ccrMonomialMap c (id : A → A) = 𝟙 (ccrMonomialObj c A) := by
  unfold ccrMonomialMap ccrMonomialObj ccrHomMk ccrObjMk
  congr 1

lemma ccrMonomialMap_comp (c : C) {A B D : Type w} (f : A → B) (g : B → D) :
    ccrMonomialMap c (g ∘ f) = ccrMonomialMap c f ≫ ccrMonomialMap c g := by
  simp only [ccrMonomialMap, ccrComp_mk]
  congr 1
  funext _
  exact (Category.id_comp (𝟙 c)).symm

/--
The monomial functor from `Type` to `CoprodCovarRepCat C` at a fixed object
`c : C`. Sends `A` to the polynomial `(A, fun _ => c)` representing `A · y^c`.
-/
def ccrMonomialFunctor (c : C) : Type w ⥤ CoprodCovarRepCat.{u, v, w} C where
  obj := ccrMonomialObj c
  map := ccrMonomialMap c
  map_id A := ccrMonomialMap_id c A
  map_comp f g := ccrMonomialMap_comp c f g

@[simp]
lemma ccrMonomialFunctor_obj (c : C) (A : Type w) :
    (ccrMonomialFunctor c).obj A = ccrMonomialObj c A :=
  rfl

@[simp]
lemma ccrMonomialFunctor_map (c : C) {A B : Type w} (f : A → B) :
    (ccrMonomialFunctor c).map f = ccrMonomialMap c f :=
  rfl

end MonomialFunctor

end GebLean
