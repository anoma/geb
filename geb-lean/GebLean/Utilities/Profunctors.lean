import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Whiskering
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

universe v u w w'

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

section Endodifunctors

variable {C : Type u} [Category.{v} C]

/-- The identity endodifunctor on `C`, sending `(A, B)` to `B` (via the
identity functor `𝟭 C`).

This is constant in the first (contravariant) argument and identity in the
second (covariant) argument. For `C = Type v`, a diagonal element at `A` is
a point of `A`, making `DiagElem IdProf` equivalent to pointed types. -/
abbrev IdProf : Cᵒᵖ ⥤ C ⥤ C :=
  (Functor.const Cᵒᵖ).obj (𝟭 C)

end Endodifunctors

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

@[simp]
theorem homPre_obj {k : Cᵒᵖ × C} :
    homPre.obj (Opposite.op k) = (k.2 ⟶ k.1.unop) :=
  rfl

@[simp]
theorem homPre_map {k₁ k₂ : Cᵒᵖ × C}
    (g : k₁ ⟶ k₂)
    (w : homPre.obj (Opposite.op k₂)) :
    homPre.map g.op w = g.2 ≫ w ≫ g.1.unop := rfl

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

variable {J : Type*} [Category J]

/--
The bifunctor `(J ⥤ C) ⥤ Cᵒᵖ ⥤ J ⥤ Type v` sending `(D, Xᵒᵖ)` to
`Hom(X, D(-)) : J ⥤ Type v`. Built from whiskering and coyoneda.
-/
def homFromFunctorBifunctor : (J ⥤ C) ⥤ Cᵒᵖ ⥤ J ⥤ Type v :=
  (coyoneda ⋙ Functor.whiskeringRight J C (Type v)).flip

/--
The functor `Hom(X, D(-)) : J ⥤ Type v` for a diagram `D : J ⥤ C` and
fixed object `X : C`. Obtained from `homFromFunctorBifunctor`.
-/
abbrev homFromFunctor (D : J ⥤ C) (X : C) : J ⥤ Type v :=
  (homFromFunctorBifunctor.obj D).obj (Opposite.op X)

/--
The bifunctor `(J ⥤ C)ᵒᵖ ⥤ C ⥤ Jᵒᵖ ⥤ Type v` sending `(Dᵒᵖ, X)` to
`Hom(D(-), X) : Jᵒᵖ ⥤ Type v`. Built from opHom, whiskering, and yoneda.
-/
def homToFunctorBifunctor : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Jᵒᵖ ⥤ Type v :=
  Functor.opHom J C ⋙ (yoneda ⋙ Functor.whiskeringRight Jᵒᵖ Cᵒᵖ (Type v)).flip

/--
The functor `Hom(D(-), X) : Jᵒᵖ ⥤ Type v` for a diagram `D : J ⥤ C` and
fixed object `X : C`. Obtained from `homToFunctorBifunctor`.
-/
abbrev homToFunctor (D : J ⥤ C) (X : C) : Jᵒᵖ ⥤ Type v :=
  (homToFunctorBifunctor.obj (Opposite.op D)).obj X

end HomVariants

section HomPreOpComputation

/-!
### Computing `homPreOp.obj`

The functor `homPreOp : (Cᵒᵖᵒᵖ × Cᵒᵖ)ᵒᵖ ⥤ Type v` is defined through a chain
of equivalences. This section provides lemmas to convert between
`homPreOp.obj (op (op (op dom), op cod))` and the hom set `cod ⟶ dom`.
-/

variable {C : Type u} [Category.{v} C]

/--
For the input `op (op (op dom), op cod)`, `homPreOp.obj` gives a type
that is definitionally related to the hom set `cod ⟶ dom`.

This lemma computes the intermediate type by unfolding the equivalence chain.
-/
lemma homPreOp_obj_eq {dom cod : C} :
    homPreOp.obj (Opposite.op (Opposite.op (Opposite.op dom), Opposite.op cod))
    = (Functor.hom C).obj
        ((CategoryTheory.Prod.swap C Cᵒᵖ).obj
          ((opOpProdEquiv C Cᵒᵖ).functor.obj
            ((opProdSymSelfDual Cᵒᵖ).functor.obj
              (Opposite.op (Opposite.op (Opposite.op dom), Opposite.op cod))))) := by
  rfl

/--
Complete computation showing that `homPreOp.obj (op (op (op dom), op cod)) = (cod ⟶ dom)`.
-/
@[simp]
lemma homPreOp_obj_hom {dom cod : C} :
    homPreOp.obj (Opposite.op (Opposite.op (Opposite.op dom), Opposite.op cod))
    = (dom ⟶ cod) := by
  simp only [homPreOp, profunctorPreOp, profunctorPre, profunctorOp,
    Functor.comp_obj]
  simp only [opProdSymSelfDual, Equivalence.trans_functor, Functor.comp_obj]
  simp only [prodOpEquiv_functor_obj]
  simp only [opOpProdEquiv, Equivalence.prod_functor, Functor.prod_obj,
    opOpEquivalence, Equivalence.refl_functor, Functor.id_obj]
  simp only [opProdProdOpEquiv, Equivalence.symm_functor,
    CategoryTheory.Prod.braiding_inverse, CategoryTheory.Prod.swap_obj]
  simp only [Functor.hom_obj, unopUnop_obj]

/--
Convert from `dom ⟶ cod` to `homPreOp.obj (op (op (op dom), op cod))`.
-/
def homPreOpObjIn {dom cod : C} (f : dom ⟶ cod) :
    homPreOp.obj (Opposite.op (Opposite.op (Opposite.op dom), Opposite.op cod)) :=
  homPreOp_obj_hom (C := C) (dom := dom) (cod := cod) ▸ f

/--
Convert from `homPreOp.obj (op (op (op dom), op cod))` to `dom ⟶ cod`.
-/
def homPreOpObjOut {dom cod : C}
    (f : homPreOp.obj (Opposite.op (Opposite.op (Opposite.op dom), Opposite.op cod))) :
    dom ⟶ cod :=
  homPreOp_obj_hom (C := C) (dom := dom) (cod := cod) ▸ f

end HomPreOpComputation

section ProfunctorMaps

/-!
### Bifunctor partial maps

For a bifunctor `P : Cᵒᵖ × C ⥤ D`, we define:
- `Prof.map₁`: apply `P` to a morphism in the first
  (contravariant) argument
- `Prof.map₂`: apply `P` to a morphism in the second
  (covariant) argument

These are the two "partial applications" of a bifunctor, and
they satisfy composition laws and commute with each other
(bifunctor naturality).
-/

variable {C : Type u} [Category.{v} C]
  {D : Type w} [Category.{w'} D]

/-- Apply a bifunctor to a morphism in the first
(contravariant) argument. -/
abbrev Prof.map₁ (P : Cᵒᵖ × C ⥤ D) {c c' d : C}
    (f : c ⟶ c') :
    P.obj (Opposite.op c', d) ⟶
      P.obj (Opposite.op c, d) :=
  P.map (f.op, 𝟙 d)

/-- Apply a bifunctor to a morphism in the second
(covariant) argument. -/
abbrev Prof.map₂ (P : Cᵒᵖ × C ⥤ D) {c d d' : C}
    (g : d ⟶ d') :
    P.obj (Opposite.op c, d) ⟶
      P.obj (Opposite.op c, d') :=
  P.map (𝟙 (Opposite.op c), g)

/-- Composition law for `Prof.map₁`
(contravariant, so reverses). -/
@[simp]
theorem Prof.map₁_comp (P : Cᵒᵖ × C ⥤ D)
    {a b c : C} (d : C) (f : a ⟶ b) (g : b ⟶ c) :
    Prof.map₁ P g ≫ Prof.map₁ P f =
      Prof.map₁ P (d := d) (f ≫ g) := by
  simp only [Prof.map₁, ← P.map_comp, prod_comp,
    Category.id_comp, op_comp]

/-- Composition law for `Prof.map₂` (covariant). -/
@[simp]
theorem Prof.map₂_comp (P : Cᵒᵖ × C ⥤ D)
    {b c d : C} (a : C) (f : b ⟶ c) (g : c ⟶ d) :
    Prof.map₂ P f ≫ Prof.map₂ P g =
      Prof.map₂ P (c := a) (f ≫ g) := by
  simp only [Prof.map₂, ← P.map_comp, prod_comp,
    Category.id_comp]

/-- Bifunctor naturality: `Prof.map₁` and `Prof.map₂`
commute. -/
theorem Prof.map_comm (P : Cᵒᵖ × C ⥤ D)
    {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) :
    Prof.map₁ P f ≫ Prof.map₂ P g =
      Prof.map₂ P g ≫ Prof.map₁ P f := by
  simp only [Prof.map₁, Prof.map₂, ← P.map_comp,
    prod_comp, Category.id_comp, Category.comp_id]

end ProfunctorMaps

section ProjectionProfunctor

/-!
### Projection profunctor

For a functor `F : C ⥤ Type w`, we define the projection profunctor
`ProjProf D F : Dᵒᵖ × C ⥤ Type w` by `ProjProf D F (d, c) = F.obj c`.

This ignores the contravariant argument and is the precomposition of `F`
with the second projection functor `Prod.snd Dᵒᵖ C : Dᵒᵖ × C ⥤ C`.

When `D = C`, this gives an endo-profunctor on `C`.
-/

variable {C : Type u} [Category.{v} C]
variable {D : Type*} [Category D]

/-- The projection profunctor derived from a functor `F : C ⥤ Type w`.
`ProjProf D F (d, c) = F.obj c`, ignoring the contravariant argument from `D`. -/
def ProjProf (D : Type*) [Category D] (F : C ⥤ Type w) : Dᵒᵖ × C ⥤ Type w :=
  CategoryTheory.Prod.snd Dᵒᵖ C ⋙ F

@[simp]
theorem ProjProf_obj (F : C ⥤ Type w) (p : Dᵒᵖ × C) :
    (ProjProf D F).obj p = F.obj p.2 := rfl

@[simp]
theorem ProjProf_map (F : C ⥤ Type w) {p q : Dᵒᵖ × C} (f : p ⟶ q) :
    (ProjProf D F).map f = F.map f.2 := rfl

end ProjectionProfunctor

section ProjectionProfunctorEndo

/-!
### Endo-profunctor lemmas for ProjProf

When `D = C`, we can state additional lemmas about the partial maps.
-/

variable {C : Type u} [Category.{v} C]

/-- The contravariant action on `ProjProf C F` is the identity. -/
@[simp]
theorem ProjProf_map₁ (F : C ⥤ Type w) {a b c : C} (f : a ⟶ b)
    (x : (ProjProf C F).obj (Opposite.op b, c)) :
    Prof.map₁ (ProjProf C F) f x = x := by
  simp only [Prof.map₁, ProjProf_map, F.map_id, types_id_apply]

/-- The covariant action on `ProjProf C F` is `F.map`. -/
@[simp]
theorem ProjProf_map₂ (F : C ⥤ Type w) {a b c : C} (g : b ⟶ c)
    (x : (ProjProf C F).obj (Opposite.op a, b)) :
    Prof.map₂ (ProjProf C F) g x = F.map g x := by
  simp only [Prof.map₂, ProjProf_map]

end ProjectionProfunctorEndo

section ConstantProfunctors

/-!
### Constant Profunctors

The constant profunctor returns a fixed type for all inputs.
The terminal profunctor is the special case where that type is `PUnit`.
-/

variable {C : Type u} [Category.{v} C]

/-- The constant profunctor that returns a fixed type `T` for all inputs.
This is `(const Cᵒᵖ).obj ((const C).obj T)`. -/
abbrev constProfunctor (T : Type v) : Cᵒᵖ ⥤ C ⥤ Type v :=
  (Functor.const Cᵒᵖ).obj ((Functor.const C).obj T)

@[simp]
lemma constProfunctor_obj_obj (T : Type v) (A B : C) :
    ((constProfunctor (C := C) T).obj (Opposite.op A)).obj B = T := rfl

/-- The terminal profunctor returns `PUnit` for all inputs.
This is the weight profunctor for ordinary (unweighted) ends and coends. -/
abbrev terminalProfunctor : Cᵒᵖ ⥤ C ⥤ Type v :=
  constProfunctor PUnit.{v + 1}

@[simp]
lemma terminalProfunctor_obj_obj (A B : C) :
    ((terminalProfunctor (C := C)).obj (Opposite.op A)).obj B = PUnit.{v + 1} := rfl

end ConstantProfunctors

section ForgetfulProfunctors

/-!
### Forgetful Profunctors

Utilities for converting functors to profunctors that ignore one argument.

- `covProfunctor F` for `F : C ⥤ Type v` gives profunctor `(I, J) ↦ F(J)`,
  ignoring the contravariant argument.
- `contravProfunctor F` for `F : Cᵒᵖ ⥤ Type v` gives profunctor `(I, J) ↦ F(I)`,
  ignoring the covariant argument.
-/

variable {C : Type u} [Category.{v} C]

/-- A profunctor built from a covariant functor `F : C ⥤ Type v`.
The result ignores the contravariant argument:
`(covProfunctor F).obj I = F` for all `I : Cᵒᵖ`. -/
abbrev covProfunctor (F : C ⥤ Type v) : Cᵒᵖ ⥤ C ⥤ Type v :=
  (Functor.const Cᵒᵖ).obj F

@[simp]
theorem covProfunctor_obj (F : C ⥤ Type v) (I : Cᵒᵖ) :
    (covProfunctor F).obj I = F := rfl

@[simp]
theorem covProfunctor_obj_obj (F : C ⥤ Type v) (I : Cᵒᵖ) (J : C) :
    ((covProfunctor F).obj I).obj J = F.obj J := rfl

@[simp]
theorem covProfunctor_obj_map (F : C ⥤ Type v) (I : Cᵒᵖ) {J J' : C} (g : J ⟶ J') :
    ((covProfunctor F).obj I).map g = F.map g := rfl

@[simp]
theorem covProfunctor_map (F : C ⥤ Type v) {I I' : Cᵒᵖ} (f : I ⟶ I') :
    (covProfunctor F).map f = 𝟙 F := rfl

/-- A profunctor built from a contravariant functor `F : Cᵒᵖ ⥤ Type v`.
The result ignores the covariant argument:
`((contravProfunctor F).obj I).obj J = F.obj I` for all `J : C`. -/
abbrev contravProfunctor (F : Cᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ C ⥤ Type v :=
  F ⋙ (Functor.const C)

@[simp]
theorem contravProfunctor_obj_obj (F : Cᵒᵖ ⥤ Type v) (I : Cᵒᵖ) (J : C) :
    ((contravProfunctor F).obj I).obj J = F.obj I := rfl

@[simp]
theorem contravProfunctor_obj_map (F : Cᵒᵖ ⥤ Type v) (I : Cᵒᵖ) {J J' : C} (g : J ⟶ J') :
    ((contravProfunctor F).obj I).map g = id := rfl

@[simp]
theorem contravProfunctor_map_app (F : Cᵒᵖ ⥤ Type v) {I I' : Cᵒᵖ} (f : I ⟶ I') (J : C) :
    ((contravProfunctor F).map f).app J = F.map f := rfl

end ForgetfulProfunctors

section Collage

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The collage (or cograph) of a profunctor
`P : Cᵒᵖ × D ⥤ Type w`.  Objects are the
disjoint union `C ⊕ D`; morphisms within `C`
and within `D` are inherited, cross-morphisms
from `C` to `D` are elements of `P`, and there
are no morphisms from `D` to `C`. -/
structure Collage
    (P : Cᵒᵖ × D ⥤ Type w) where
  val : C ⊕ D

/-- Inject a `C`-object into the collage. -/
def Collage.inl
    {P : Cᵒᵖ × D ⥤ Type w}
    (c : C) : Collage P :=
  ⟨.inl c⟩

/-- Inject a `D`-object into the collage. -/
def Collage.inr
    {P : Cᵒᵖ × D ⥤ Type w}
    (d : D) : Collage P :=
  ⟨.inr d⟩

/-- Morphisms in the collage of `P`.  Within each
component, morphisms are inherited from `C` or `D`;
cross-morphisms from `C` to `D` are elements of `P`;
there are no morphisms from `D` to `C`.  All branches
are `ULift`ed to a common universe. -/
def Collage.Hom
    (P : Cᵒᵖ × D ⥤ Type w) :
    Collage P → Collage P →
    Type (max v₁ v₂ w) :=
  fun X Y =>
    match X.val, Y.val with
    | .inl c₁, .inl c₂ =>
      ULift.{max v₁ v₂ w} (c₁ ⟶ c₂)
    | .inr d₁, .inr d₂ =>
      ULift.{max v₁ v₂ w} (d₁ ⟶ d₂)
    | .inl c, .inr d =>
      ULift.{max v₁ v₂ w}
        (P.obj (Opposite.op c, d))
    | .inr _, .inl _ => PEmpty

variable (P : Cᵒᵖ × D ⥤ Type w) in
/-- Identity morphism in the collage. -/
def Collage.Hom.id :
    (X : Collage P) → Collage.Hom P X X :=
  fun X =>
    match X with
    | ⟨.inl c⟩ => ⟨𝟙 c⟩
    | ⟨.inr d⟩ => ⟨𝟙 d⟩

variable (P : Cᵒᵖ × D ⥤ Type w) in
/-- Composition of morphisms in the collage. -/
def Collage.Hom.comp :
    {X Y Z : Collage P} →
    Collage.Hom P X Y →
    Collage.Hom P Y Z →
    Collage.Hom P X Z :=
  fun {X Y Z} f g =>
    match X, Y, Z, f, g with
    | ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inl _⟩,
      f, g => ⟨f.down ≫ g.down⟩
    | ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inr d⟩,
      f, h =>
        ⟨P.map (f.down.op, 𝟙 d) h.down⟩
    | ⟨.inl c⟩, ⟨.inr _⟩, ⟨.inr _⟩,
      h, g =>
        ⟨P.map
          (𝟙 (Opposite.op c), g.down)
          h.down⟩
    | ⟨.inr _⟩, ⟨.inr _⟩, ⟨.inr _⟩,
      f, g => ⟨f.down ≫ g.down⟩
    | ⟨.inr _⟩, ⟨.inl _⟩, _,
      f, _ => f.elim
    | ⟨.inl _⟩, ⟨.inr _⟩, ⟨.inl _⟩,
      _, g => g.elim
    | ⟨.inr _⟩, ⟨.inr _⟩, ⟨.inl _⟩,
      _, g => g.elim

variable (P : Cᵒᵖ × D ⥤ Type w) in
instance : CategoryStruct (Collage P) where
  Hom := Collage.Hom P
  id := Collage.Hom.id P
  comp := Collage.Hom.comp P

variable (P : Cᵒᵖ × D ⥤ Type w) in
theorem Collage.Hom.id_comp
    {X Y : Collage P}
    (f : Collage.Hom P X Y) :
    Collage.Hom.comp P
      (Collage.Hom.id P X) f = f := by
  match X, Y, f with
  | ⟨.inl _⟩, ⟨.inl _⟩, f =>
    exact ULift.ext _ _ (Category.id_comp _)
  | ⟨.inl c⟩, ⟨.inr d⟩, h =>
    apply ULift.ext
    change P.map
      (𝟙 (Opposite.op c, d)) h.down =
      h.down
    exact congr_fun (P.map_id _) h.down
  | ⟨.inr _⟩, ⟨.inr _⟩, f =>
    exact ULift.ext _ _ (Category.id_comp _)
  | ⟨.inr _⟩, ⟨.inl _⟩, f => exact f.elim

variable (P : Cᵒᵖ × D ⥤ Type w) in
theorem Collage.Hom.comp_id
    {X Y : Collage P}
    (f : Collage.Hom P X Y) :
    Collage.Hom.comp P f
      (Collage.Hom.id P Y) = f := by
  match X, Y, f with
  | ⟨.inl _⟩, ⟨.inl _⟩, f =>
    exact ULift.ext _ _ (Category.comp_id _)
  | ⟨.inl c⟩, ⟨.inr d⟩, h =>
    apply ULift.ext
    change P.map
      (𝟙 (Opposite.op c, d)) h.down =
      h.down
    exact congr_fun (P.map_id _) h.down
  | ⟨.inr _⟩, ⟨.inr _⟩, f =>
    exact ULift.ext _ _ (Category.comp_id _)
  | ⟨.inr _⟩, ⟨.inl _⟩, f => exact f.elim

variable (P : Cᵒᵖ × D ⥤ Type w) in
theorem Collage.Hom.assoc
    {W X Y Z : Collage P}
    (f : Collage.Hom P W X)
    (g : Collage.Hom P X Y)
    (h : Collage.Hom P Y Z) :
    Collage.Hom.comp P
      (Collage.Hom.comp P f g) h =
    Collage.Hom.comp P f
      (Collage.Hom.comp P g h) := by
  match W, X, Y, Z, f, g, h with
  | ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inl _⟩,
    f, g, h =>
    exact ULift.ext _ _
      (Category.assoc _ _ _)
  | ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inr _⟩,
    f, g, h =>
    apply ULift.ext
    simp only [Collage.Hom.comp, op_comp,
      ← FunctorToTypes.map_comp_apply,
      prod_comp]; simp
  | ⟨.inl _⟩, ⟨.inl _⟩, ⟨.inr _⟩, ⟨.inr _⟩,
    f, h, g =>
    apply ULift.ext
    simp only [Collage.Hom.comp,
      ← FunctorToTypes.map_comp_apply,
      prod_comp]; simp
  | ⟨.inl _⟩, ⟨.inr _⟩, ⟨.inr _⟩, ⟨.inr _⟩,
    h, g₁, g₂ =>
    apply ULift.ext
    simp only [Collage.Hom.comp,
      ← FunctorToTypes.map_comp_apply,
      prod_comp]; simp
  | ⟨.inr _⟩, ⟨.inr _⟩, ⟨.inr _⟩, ⟨.inr _⟩,
    f, g, h =>
    exact ULift.ext _ _
      (Category.assoc _ _ _)
  | ⟨.inr _⟩, ⟨.inl _⟩, _, _, f, _, _ =>
    exact f.elim
  | _, _, ⟨.inr _⟩, ⟨.inl _⟩, _, _, h =>
    exact h.elim
  | ⟨.inl _⟩, ⟨.inr _⟩, ⟨.inl _⟩, _, _, g, _ =>
    exact g.elim

variable (P : Cᵒᵖ × D ⥤ Type w) in
instance : Category.{max v₁ v₂ w}
    (Collage P) where
  id_comp := Collage.Hom.id_comp P
  comp_id := Collage.Hom.comp_id P
  assoc := Collage.Hom.assoc P

/-- The inclusion functor from `C` into the
collage, sending `c` to `Collage.inl c`. -/
def Collage.inlFunctor
    (P : Cᵒᵖ × D ⥤ Type w) :
    C ⥤ Collage P where
  obj c := Collage.inl c
  map f := ⟨f⟩
  map_id _ := ULift.ext _ _ rfl
  map_comp _ _ := ULift.ext _ _ rfl

/-- The inclusion functor from `D` into the
collage, sending `d` to `Collage.inr d`. -/
def Collage.inrFunctor
    (P : Cᵒᵖ × D ⥤ Type w) :
    D ⥤ Collage P where
  obj d := Collage.inr d
  map f := ⟨f⟩
  map_id _ := ULift.ext _ _ rfl
  map_comp _ _ := ULift.ext _ _ rfl

end Collage

end GebLean
