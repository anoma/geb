import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
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

section ProfunctorMaps

/-!
### Profunctor partial maps

For a profunctor `P : Cᵒᵖ × C ⥤ Type w`, we define:
- `Prof.map₁`: apply `P` to a morphism in the first (contravariant) argument
- `Prof.map₂`: apply `P` to a morphism in the second (covariant) argument

These are the two "partial applications" of a bifunctor, and they satisfy
composition laws and commute with each other (bifunctor naturality).
-/

variable {C : Type u} [Category.{v} C]

/-- Apply a profunctor to a morphism in the first (contravariant) argument. -/
abbrev Prof.map₁ (P : Cᵒᵖ × C ⥤ Type w) {c c' d : C} (f : c ⟶ c') :
    P.obj (Opposite.op c', d) → P.obj (Opposite.op c, d) :=
  P.map (f.op, 𝟙 d)

/-- Apply a profunctor to a morphism in the second (covariant) argument. -/
abbrev Prof.map₂ (P : Cᵒᵖ × C ⥤ Type w) {c d d' : C} (g : d ⟶ d') :
    P.obj (Opposite.op c, d) → P.obj (Opposite.op c, d') :=
  P.map (𝟙 (Opposite.op c), g)

/-- Composition law for Prof.map₁ (contravariant, so reverses). -/
@[simp]
theorem Prof.map₁_comp (P : Cᵒᵖ × C ⥤ Type w) {a b c d : C} (f : a ⟶ b) (g : b ⟶ c)
    (p : P.obj (Opposite.op c, d)) :
    Prof.map₁ P f (Prof.map₁ P g p) = Prof.map₁ P (f ≫ g) p := by
  simp only [Prof.map₁, ← FunctorToTypes.map_comp_apply, prod_comp,
    Category.id_comp, op_comp]

/-- Composition law for Prof.map₂ (covariant). -/
@[simp]
theorem Prof.map₂_comp (P : Cᵒᵖ × C ⥤ Type w) {a b c d : C} (f : b ⟶ c) (g : c ⟶ d)
    (p : P.obj (Opposite.op a, b)) :
    Prof.map₂ P g (Prof.map₂ P f p) = Prof.map₂ P (f ≫ g) p := by
  simp only [Prof.map₂, ← FunctorToTypes.map_comp_apply, prod_comp, Category.id_comp]

/-- Profunctor naturality: Prof.map₁ and Prof.map₂ commute. -/
theorem Prof.map_comm (P : Cᵒᵖ × C ⥤ Type w) {a b c d : C} (f : a ⟶ b) (g : c ⟶ d)
    (p : P.obj (Opposite.op b, c)) :
    Prof.map₂ P g (Prof.map₁ P f p) = Prof.map₁ P f (Prof.map₂ P g p) := by
  simp only [Prof.map₁, Prof.map₂]
  let m₁ : (Opposite.op b, c) ⟶ (Opposite.op a, c) := (f.op, 𝟙 c)
  let m₂ : (Opposite.op a, c) ⟶ (Opposite.op a, d) := (𝟙 (Opposite.op a), g)
  let n₁ : (Opposite.op b, c) ⟶ (Opposite.op b, d) := (𝟙 (Opposite.op b), g)
  let n₂ : (Opposite.op b, d) ⟶ (Opposite.op a, d) := (f.op, 𝟙 d)
  change P.map m₂ (P.map m₁ p) = P.map n₂ (P.map n₁ p)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
  simp only [m₁, m₂, n₁, n₂, prod_comp, Category.id_comp, Category.comp_id]

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

end GebLean
