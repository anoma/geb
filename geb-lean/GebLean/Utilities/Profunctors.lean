import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Products.Basic
import GebLean.Utilities.Opposites

/-!
# Profunctors

This module defines profunctors and their variants, using both mathlib's `ᵒᵖ`
and our `ᵒᵖ'` opposite category constructions.

A profunctor from C to D is a functor `Cᵒᵖ × D ⥤ Type`. This module provides
general machinery for viewing profunctors in different forms via
precomposition with equivalences, and then specializes to the hom functor
`Hom : Cᵒᵖ × C ⥤ Type`.
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

section ProfunctorVariants

variable {C : Type u} [Category.{v} C]

/--
Convert a profunctor using mathlib's `ᵒᵖ` to one using our `ᵒᵖ'`.
-/
def profunctorToOp' (P : opProdSym C ⥤ Type v) : opProdSym' C ⥤ Type v :=
  (opProdEquiv C C).inverse ⋙ P

/--
View a profunctor on `C` as a profunctor on `Cᵒᵖ`.
-/
def profunctorOp (P : opProdSym C ⥤ Type v) : opProdSym Cᵒᵖ ⥤ Type v :=
  (opOpProdEquiv C Cᵒᵖ).functor
  ⋙ CategoryTheory.Prod.swap C Cᵒᵖ
  ⋙ P

/--
View a profunctor on `C` (using `ᵒᵖ'`) as a profunctor on `Cᵒᵖ'`.
-/
def profunctorOp' (P : opProdSym' C ⥤ Type v) : opProdSym' Cᵒᵖ' ⥤ Type v :=
  (opOpProdEquiv' C Cᵒᵖ').functor
  ⋙ CategoryTheory.Prod.swap C Cᵒᵖ'
  ⋙ P

/--
View a profunctor as a presheaf on `(Cᵒᵖ × C)`.
-/
def profunctorPre (P : opProdSym C ⥤ Type v) : (opProdSym C)ᵒᵖ ⥤ Type v :=
  (opProdSymSelfDual C).functor ⋙ P

/--
View a profunctor (using `ᵒᵖ'`) as a presheaf on `(Cᵒᵖ' × C)`.
-/
def profunctorPre' (P : opProdSym' C ⥤ Type v) : (opProdSym' C)ᵒᵖ' ⥤ Type v :=
  (opProdSymSelfDual' C).functor ⋙ P

/--
View a profunctor as a presheaf on `(Cᵒᵖᵒᵖ × Cᵒᵖ)`.
-/
def profunctorPreOp (P : opProdSym C ⥤ Type v) : (opProdSym Cᵒᵖ)ᵒᵖ ⥤ Type v :=
  profunctorPre (C := Cᵒᵖ) (profunctorOp (C := C) P)

/--
View a profunctor (using `ᵒᵖ'`) as a presheaf on `(Cᵒᵖ'ᵒᵖ' × Cᵒᵖ')`.
-/
def profunctorPreOp' (P : opProdSym' C ⥤ Type v) :
    (opProdSym' Cᵒᵖ')ᵒᵖ' ⥤ Type v :=
  profunctorPre' (C := Cᵒᵖ') (profunctorOp' (C := C) P)

end ProfunctorVariants

section HomVariants

variable {C : Type u} [Category.{v} C]

/--
The hom functor using our `ᵒᵖ'` instead of mathlib's `ᵒᵖ`.
-/
def hom' : opProdSym' C ⥤ Type v :=
  profunctorToOp' (C := C) (Functor.hom C)

/--
The hom functor viewed as the hom-functor of `Cᵒᵖ`.
-/
def homOp : opProdSym Cᵒᵖ ⥤ Type v :=
  profunctorOp (C := C) (Functor.hom C)

/--
The hom functor viewed as the hom-functor of `Cᵒᵖ'`.
-/
def homOp' : opProdSym' Cᵒᵖ' ⥤ Type v :=
  profunctorOp' (C := C) hom'

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ × C)`.
-/
def homPre : (opProdSym C)ᵒᵖ ⥤ Type v :=
  profunctorPre (C := C) (Functor.hom C)

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ' × C)`.
-/
def homPre' : (opProdSym' C)ᵒᵖ' ⥤ Type v :=
  profunctorPre' (C := C) hom'

/--
The hom functor viewed as a presheaf on `(Cᵒᵖᵒᵖ × Cᵒᵖ)`.
-/
def homPreOp : (opProdSym Cᵒᵖ)ᵒᵖ ⥤ Type v :=
  profunctorPreOp (C := C) (Functor.hom C)

/--
The hom functor viewed as a presheaf on `(Cᵒᵖ'ᵒᵖ' × Cᵒᵖ')`.
-/
def homPreOp' : (opProdSym' Cᵒᵖ')ᵒᵖ' ⥤ Type v :=
  profunctorPreOp' (C := C) hom'

end HomVariants

end GebLean
