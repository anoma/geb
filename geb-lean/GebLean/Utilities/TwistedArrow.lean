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

instance OpProdInst' (C D : Type u) [Category C] [Category D] :
  Category (opProd' C D) := inferInstance

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

/--
The hom functor using our `ᵒᵖ'` instead of mathlib's `ᵒᵖ`.
-/
def hom' : opProdSym' C ⥤ Type v :=
  (opProdEquiv C C).inverse ⋙ Functor.hom C

/--
The hom functor viewed as the hom-functor of `Cᵒᵖ`.
-/
def homOp : opProdSym Cᵒᵖ ⥤ Type v :=
  (opOpProdEquiv C Cᵒᵖ).functor
  ⋙ CategoryTheory.Prod.swap C Cᵒᵖ
  ⋙ Functor.hom C

/--
The hom functor viewed as the hom-functor of `Cᵒᵖ'`.
-/
def homOp' : opProdSym' Cᵒᵖ' ⥤ Type v :=
  (opOpProdEquiv' C Cᵒᵖ').functor
  ⋙ CategoryTheory.Prod.swap C Cᵒᵖ'
  ⋙ hom'

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ × C)`.
-/
def homPre : (opProdSym C)ᵒᵖ ⥤ Type v :=
  (opProdSymSelfDual C).functor ⋙ Functor.hom C

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ' × C)`.
-/
def homPre' : (opProdSym' C)ᵒᵖ' ⥤ Type v :=
  (opProdSymSelfDual' C).functor ⋙ hom'

/--
The hom functor viewed as a presheaf on `(Cᵒᵖᵒᵖ × Cᵒᵖ)`.
-/
def homPreOp : (opProdSym Cᵒᵖ)ᵒᵖ ⥤ Type v :=
  homPre (C := Cᵒᵖ)

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ'ᵒᵖ' × Cᵒᵖ')`.
-/
def homPreOp' : (opProdSym' Cᵒᵖ')ᵒᵖ' ⥤ Type v :=
  homPre' (C := Cᵒᵖ')

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

@[simp]
def TwistedArrow' (C : Type u) [Category.{v} C] :=
  (hom' (C := C)).Elements

instance (C : Type u) [Category.{v} C] : Category (TwistedArrow' C) := by
  unfold TwistedArrow'
  infer_instance

abbrev Tw := TwistedArrow

abbrev Tw' := TwistedArrow'

variable {C : Type u} [Category.{v} C]

section TwistedArrow'Helpers

/--
Construct an object of `TwistedArrow' C` from domain, codomain, and arrow.
-/
def twObjMk' {dom cod : C} (arr : dom ⟶ cod) : TwistedArrow' C :=
  ⟨(dom, cod), arr⟩

/--
Extract the domain from an object of `TwistedArrow' C`.
-/
def twDom' (x : TwistedArrow' C) : C := x.fst.1

/--
Extract the codomain from an object of `TwistedArrow' C`.
-/
def twCod' (x : TwistedArrow' C) : C := x.fst.2

/--
Extract the arrow from an object of `TwistedArrow' C`.
-/
def twArr' (x : TwistedArrow' C) : twDom' x ⟶ twCod' x := x.snd

lemma twObjMk'_dom {dom cod : C} (arr : dom ⟶ cod) :
    twDom' (twObjMk' arr) = dom := rfl

lemma twObjMk'_cod {dom cod : C} (arr : dom ⟶ cod) :
    twCod' (twObjMk' arr) = cod := rfl

lemma twObjMk'_arr {dom cod : C} (arr : dom ⟶ cod) :
    twArr' (twObjMk' arr) = arr := rfl

/--
Construct a morphism in `TwistedArrow' C` from morphisms on domains and
codomains.

A morphism from `(X, Y, f)` to `(X', Y', f')` consists of:
- `domArr : X' ⟶ X` (morphism between domains, going backwards)
- `codArr : Y ⟶ Y'` (morphism between codomains, going forwards)
such that the square commutes: `domArr ≫ f ≫ codArr = f'`.

Note: The domain arrow goes backwards because the first component of the
product is in `Cᵒᵖ'`.
-/
def twHomMk' {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) : x ⟶ y :=
  CategoryOfElements.homMk x y (domArr, codArr) comm

/--
Extract the domain arrow from a morphism in `TwistedArrow' C`.
Note: This goes backwards (from codomain to domain) because the first component
is in `Cᵒᵖ'`.
-/
def twDomArr' {x y : TwistedArrow' C} (f : x ⟶ y) : twDom' y ⟶ twDom' x :=
  f.val.1

/--
Extract the codomain arrow from a morphism in `TwistedArrow' C`.
-/
def twCodArr' {x y : TwistedArrow' C} (f : x ⟶ y) : twCod' x ⟶ twCod' y :=
  f.val.2

lemma twHomMk'_domArr {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) :
    twDomArr' (twHomMk' domArr codArr comm) = domArr := rfl

lemma twHomMk'_codArr {x y : TwistedArrow' C}
    (domArr : twDom' y ⟶ twDom' x)
    (codArr : twCod' x ⟶ twCod' y)
    (comm : domArr ≫ twArr' x ≫ codArr = twArr' y) :
    twCodArr' (twHomMk' domArr codArr comm) = codArr := rfl

@[ext]
lemma twHom'_ext {x y : TwistedArrow' C} (f g : x ⟶ y)
    (hdom : twDomArr' f = twDomArr' g)
    (hcod : twCodArr' f = twCodArr' g) : f = g := by
  cases f; cases g
  congr
  exact Prod.ext hdom hcod

end TwistedArrow'Helpers

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
The opposite of the twisted arrow category, defined as a contravariant
category of elements.
-/
@[simp]
def OpTwistedArrow' (C : Type u) [Category.{v} C] :=
  (homPre' (C := C)).ElementsContra'

instance (C : Type u) [Category.{v} C] : Category (OpTwistedArrow' C) := by
  unfold OpTwistedArrow'
  infer_instance

/--
The opposite of the twisted arrow category of `Cᵒᵖ'`, which we
are calling the co-twisted arrow category of `C`.
-/
@[simp]
def CoTwistedArrow (C : Type u) [Category.{v} C] :=
  (homPreOp' (C := C)).ElementsContra'

instance (C : Type u) [Category.{v} C] : Category (CoTwistedArrow C) := by
  unfold CoTwistedArrow
  infer_instance

end TwistedArrowCategories

end GebLean
