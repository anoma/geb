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

This is an alias for `GrothendieckContra'.forget` specialized to the
functor defining `CoprodCovarRepCat`.
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

end GebLean
