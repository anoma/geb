import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Products.Basic
import GebLean.Utilities.Equalities
import GebLean.Utilities.Elements
import GebLean.Utilities.Opposites

/-!
# Twisted arrow categories

This module defines twisted arrow categories and their variants.

The twisted arrow category of a category C is the category of elements of
the hom functor `hom : Cᵒᵖ × C ⥤ Type`. Objects are triples (X, Y, f) where
f : X ⟶ Y, and morphisms consist of pairs of morphisms going in opposite
directions (backwards on domain, forwards on codomain) making the resulting
square (with three morphisms composing parallel to one) commute.

We define four variants:
- `Tw(C)` = `Elements(hom)` - twisted arrow category
- `Tw(Cᵒᵖ')` = `Elements(homOp')` - twisted arrow of opposite
- `Tw^op'(C)` = `ElementsContra'(hom')` - opposite of twisted arrow
- `Tw^co` = `Tw^op'(Cᵒᵖ')` - opposite of twisted arrow of opposite
-                            (which we shall call "co-twisted")
-/

universe v u w

namespace GebLean

open CategoryTheory

abbrev opProd (C D : Type u) [Category C] [Category D] := Cᵒᵖ × D

abbrev opProdSym (C : Type u) [Category C] := opProd C C

abbrev opProd' (C D : Type u) [Category C] [Category D] := Cᵒᵖ' × D

abbrev opProdSym' (C : Type u) [Category C] := opProd' C C

def opProdEquiv (C D : Type u) [Category C] [Category D] :
    opProd C D ≌ opProd' C D :=
  Equivalence.prod opEquivOp' CategoryTheory.Equivalence.refl

def opOpProdEquiv (C D : Type u) [Category C] [Category D] :
    Cᵒᵖᵒᵖ × D ≌ C × D :=
  Equivalence.prod (opOpEquivalence C) CategoryTheory.Equivalence.refl

def opOpProdEquiv' (C D : Type u) [Category C] [Category D] :
    (Cᵒᵖ'ᵒᵖ' × D) ≌ (C × D) :=
  Equivalence.prod CategoryTheory.Equivalence.refl CategoryTheory.Equivalence.refl

abbrev prodOp (C D : Type u) [Category C] [Category D] := C × Dᵒᵖ

abbrev prodOp' (C D : Type u) [Category C] [Category D] := C × Dᵒᵖ'

def prodOpProdOp'Equiv (C D : Type u) [Category C] [Category D] :
    prodOp C D ≌ prodOp' C D :=
  Equivalence.prod CategoryTheory.Equivalence.refl opEquivOp'

def opProdProdOpEquiv (C : Type u) [Category C] :
    opProd C C ≌ prodOp C C :=
  CategoryTheory.Prod.braiding Cᵒᵖ C

def opProdProdOpEquiv' (C : Type u) [Category C] :
    opProd' C C ≌ prodOp' C C :=
  CategoryTheory.Prod.braiding Cᵒᵖ' C

def opProdSymSelfDual (C : Type u) [Category C] :
    (opProd C C)ᵒᵖ ≌ (opProd C C) :=
  CategoryTheory.Equivalence.trans
    (CategoryTheory.prodOpEquiv Cᵒᵖ)
    (CategoryTheory.Equivalence.trans
      (opOpProdEquiv C Cᵒᵖ)
      (opProdProdOpEquiv C).symm)

def opProdSymSelfDual' (C : Type u) [Category C] :
    (opProd' C C)ᵒᵖ' ≌ (opProd' C C) :=
  CategoryTheory.Equivalence.trans
    (prodOpEquiv' (C := Cᵒᵖ') (D := C))
    (opProdProdOpEquiv' C).symm

section HomVariants

variable {C : Type u} [Category.{v} C]

def hom' : opProdSym' C ⥤ Type v :=
  (opProdEquiv C C).inverse ⋙ Functor.hom C

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ' × C)`.
-/
def homOp' : (opProdSym' C)ᵒᵖ' ⥤ Type v :=
  (opProdSymSelfDual' C).functor ⋙ hom'

end HomVariants

section TwistedArrowCategories

/--
The twisted arrow category of `C`, defined as the category of elements of
the hom functor.
-/
@[simp]
def TwistedArrow (C : Type u) [Category.{v} C] :=
  (Functor.hom C).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrow C) := by
  unfold TwistedArrow
  infer_instance

notation "Tw(" C ")" => @TwistedArrow C _

/--
The twisted arrow category of `Cᵒᵖ'`, defined as the category of elements
of `homOp'`.
-/
@[simp]
def TwistedArrowOp' (C : Type u) [Category.{v} C] :=
  (homOp' (C := C)).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrowOp' C) := by
  unfold TwistedArrowOp'
  infer_instance

/--
The opposite of the twisted arrow category, defined as `(TwistedArrow C)ᵒᵖ'`.
-/
@[simp]
def TwistedArrowOpposite' (C : Type u) [Category.{v} C] :=
  (TwistedArrow C)ᵒᵖ'

instance (C : Type u) [Category.{v} C] : Category (TwistedArrowOpposite' C) := by
  unfold TwistedArrowOpposite'
  infer_instance

/--
The double opposite (cotwisted) arrow category, defined as `(TwistedArrowOp' C)ᵒᵖ'`.
This is equivalent to `Tw^op'(Cᵒᵖ')`.
-/
@[simp]
def TwistedArrowCo (C : Type u) [Category.{v} C] :=
  (TwistedArrowOp' C)ᵒᵖ'

instance (C : Type u) [Category.{v} C] : Category (TwistedArrowCo C) := by
  unfold TwistedArrowCo
  infer_instance

end TwistedArrowCategories

end GebLean
