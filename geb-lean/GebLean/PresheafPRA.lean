import GebLean.Polynomial
import GebLean.Utilities.Presheaf
import GebLean.Utilities.Elements
import GebLean.Utilities.Families
import Mathlib.CategoryTheory.Opposites

/-!
# Polynomial Functors Between Presheaf Categories

This module defines polynomial functors (parametric right
adjoints) between presheaf categories using the formula:

```
P(Z)(j) = ∐_{a ∈ A(j)} Hom_{PSh(I)}(E_j(a), Z)
```

A presheaf PRA `PSh(I) → PSh(J)` is represented as a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.  At each
`j : J`, this gives a polynomial `(A(j), E_j)` from
`CoprodCovarRepCat`, and the functor action provides the
restriction maps that make the evaluation a presheaf on `J`.

## References

* <https://ncatlab.org/nlab/show/parametric+right+adjoint>
-/

namespace GebLean

open CategoryTheory

universe u_I v_I u_J v_J w_I w'

variable (I : Type u_I) [Category.{v_I} I]
variable (J : Type u_J) [Category.{v_J} J]

/-! ## The Category of Presheaf PRAs -/

section PresheafPRADef

/--
The category of presheaf polynomial functors (parametric right
adjoints) from `Iᵒᵖ ⥤ Type w_I` to a presheaf category on
`J`.

An object is a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.
At each `j : Jᵒᵖ`, this gives a polynomial
`(A(j), E_j : A(j) → (Iᵒᵖ ⥤ Type w_I))`.  The functor
action on morphisms in `Jᵒᵖ` provides reindexing on
positions and precomposition maps on directions.
-/
def PresheafPRACat : Cat :=
  Cat.of
    (Jᵒᵖ ⥤
      CoprodCovarRepCat.{max v_I u_I (w_I + 1),
        max u_I w_I, w'}
        (Iᵒᵖ ⥤ Type w_I))

end PresheafPRADef

/-! ## Accessors -/

section PresheafPRAAccessors

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The type of positions at stage `j`.
-/
def praPositions (j : Jᵒᵖ) : Type w' :=
  ccrIndex (P.obj j)

/--
The directions presheaf at position `a` at stage `j`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  ccrFamily (P.obj j) a

end PresheafPRAAccessors

/-! ## Pointwise Evaluation -/

section PresheafPRAEvalAt

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Pointwise evaluation of a presheaf PRA at a presheaf `Z` and
stage `j`.  The result is
`Σ_{a : praPositions P j} (praDirectionsAt P j a ⟶ Z)`.
-/
def praEvalAt (j : Jᵒᵖ) :
    Type (max w' u_I w_I) :=
  ccrEval (P.obj j) Z

/--
Extract the position index from an evaluation element.
-/
def praEvalAt_index {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praPositions I J P j :=
  ccrEvalIndex x

/--
Extract the natural transformation from an evaluation element.
-/
def praEvalAt_mor {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praDirectionsAt I J P j
      (praEvalAt_index I J P Z x) ⟶ Z :=
  ccrEvalMor x

/--
Construct an evaluation element from a position and a natural
transformation.
-/
def praEvalAt_mk (j : Jᵒᵖ)
    (a : praPositions I J P j)
    (η : praDirectionsAt I J P j a ⟶ Z) :
    praEvalAt I J P Z j :=
  ccrEvalMk a η

end PresheafPRAEvalAt

/-! ## Evaluation of CoprodCovarRepCat Morphisms

Given a morphism `f : P ⟶ Q` in `CoprodCovarRepCat D`, the
induced map on evaluations sends `⟨i, η⟩ : ccrEval P Z` to
`⟨ccrReindex f i, ccrFiberMor f i ≫ η⟩ : ccrEval Q Z`.
This is the contravariant functorial action of `ccrEval _ Z`
on morphisms of `CoprodCovarRepCat D`.
-/

section CcrMorphEval

universe u_D v_D w_D

variable {D : Type u_D} [Category.{v_D} D]

/--
Evaluate a morphism `f : P ⟶ Q` in `CoprodCovarRepCat D` on
a `ccrEval P Z` element, producing a `ccrEval Q Z` element.
-/
def ccrMorphEval
    {P Q : CoprodCovarRepCat.{u_D, v_D, w_D} D}
    (f : P ⟶ Q) (Z : D) :
    ccrEval P Z → ccrEval Q Z :=
  fun ⟨i, η⟩ =>
    ⟨ccrReindex f i, ccrFiberMor f i ≫ η⟩

@[simp]
lemma ccrMorphEval_id
    (P : CoprodCovarRepCat.{u_D, v_D, w_D} D)
    (Z : D) :
    ccrMorphEval (𝟙 P) Z = id := by
  funext ⟨i, η⟩
  change (⟨ccrReindex (𝟙 P) i,
    ccrFiberMor (𝟙 P) i ≫ η⟩ : ccrEval P Z) =
    ⟨i, η⟩
  exact Sigma.ext rfl
    (heq_of_eq (Category.id_comp η))

@[simp]
lemma ccrMorphEval_comp
    {P Q R : CoprodCovarRepCat.{u_D, v_D, w_D} D}
    (f : P ⟶ Q) (g : Q ⟶ R)
    (Z : D) :
    ccrMorphEval (f ≫ g) Z =
      ccrMorphEval g Z ∘ ccrMorphEval f Z := by
  funext ⟨i, η⟩
  change (⟨ccrReindex (f ≫ g) i,
    ccrFiberMor (f ≫ g) i ≫ η⟩ : ccrEval R Z) =
    ⟨ccrReindex g (ccrReindex f i),
      ccrFiberMor g (ccrReindex f i) ≫
        (ccrFiberMor f i ≫ η)⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  rw [ccrComp_fiberMor, Category.assoc]

end CcrMorphEval

/-! ## Restriction Maps -/

section PresheafPRARestrict

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Restriction map along a morphism `g : j₁ ⟶ j₂` in `Jᵒᵖ`.
Sends `⟨a, η⟩` to
`⟨ccrReindex (P.map g) a, ccrFiberMor (P.map g) a ≫ η⟩`.
-/
def praRestrict {j₁ j₂ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) :
    praEvalAt I J P Z j₁ → praEvalAt I J P Z j₂ :=
  ccrMorphEval (P.map g) Z

@[simp]
lemma praRestrict_id (j : Jᵒᵖ) :
    praRestrict I J P Z (𝟙 j) =
      id := by
  change ccrMorphEval (P.map (𝟙 j)) Z = id
  rw [P.map_id, ccrMorphEval_id]

@[simp]
lemma praRestrict_comp {j₁ j₂ j₃ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃) :
    praRestrict I J P Z (g ≫ h) =
      praRestrict I J P Z h ∘
        praRestrict I J P Z g := by
  change ccrMorphEval (P.map (g ≫ h)) Z =
    ccrMorphEval (P.map h) Z ∘
      ccrMorphEval (P.map g) Z
  rw [P.map_comp, ccrMorphEval_comp]

end PresheafPRARestrict

/-! ## Evaluation as a Presheaf on J -/

section PresheafPRAEvalObj

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Evaluation of a presheaf PRA at `Z`, producing a presheaf on
`J`.  At stage `j`, the presheaf value is
`Σ_{a : A(j)} (E_j(a) ⟶ Z)`.
-/
def praEvalObj : Jᵒᵖ ⥤ Type (max w' u_I w_I) where
  obj j := praEvalAt I J P Z j
  map g := praRestrict I J P Z g
  map_id j := praRestrict_id I J P Z j
  map_comp g h := praRestrict_comp I J P Z g h

end PresheafPRAEvalObj

/-! ## Functorial Action on Domain Morphisms -/

section PresheafPRAEvalMap

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The action of `praEvalObj P` on a morphism `f : Z₁ ⟶ Z₂` in
the domain presheaf category.  At each stage `j`, this
postcomposes each natural transformation component:
`⟨a, η⟩ ↦ ⟨a, η ≫ f⟩`.
-/
def praEvalMap {Z₁ Z₂ : Iᵒᵖ ⥤ Type w_I}
    (f : Z₁ ⟶ Z₂) :
    praEvalObj I J P Z₁ ⟶ praEvalObj I J P Z₂ where
  app j := ccrEvalMap f
  naturality j₁ j₂ g := by
    ext ⟨a, η⟩
    simp [praEvalObj, praRestrict, ccrMorphEval,
      ccrEvalMap, Category.assoc]

@[simp]
lemma praEvalMap_id (Z : Iᵒᵖ ⥤ Type w_I) :
    praEvalMap I J P (𝟙 Z) =
      𝟙 (praEvalObj I J P Z) := by
  ext j ⟨a, η⟩
  simp [praEvalMap, praEvalObj]

@[simp]
lemma praEvalMap_comp {Z₁ Z₂ Z₃ : Iᵒᵖ ⥤ Type w_I}
    (f : Z₁ ⟶ Z₂) (g : Z₂ ⟶ Z₃) :
    praEvalMap I J P (f ≫ g) =
      praEvalMap I J P f ≫ praEvalMap I J P g := by
  ext j ⟨a, η⟩
  simp [praEvalMap, ccrEvalMap, Category.assoc]

end PresheafPRAEvalMap

/-! ## Evaluation Functor -/

section PresheafPRAEvalFunctor

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The evaluation functor of a presheaf PRA `P`:
`(Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _)`.
-/
def praEvalFunctor :
    (Iᵒᵖ ⥤ Type w_I) ⥤
      (Jᵒᵖ ⥤ Type (max w' u_I w_I)) where
  obj Z := praEvalObj I J P Z
  map f := praEvalMap I J P f
  map_id Z := praEvalMap_id I J P Z
  map_comp f g := praEvalMap_comp I J P f g

end PresheafPRAEvalFunctor

/-! ## Morphism Evaluation and Category-Level Functor -/

section PresheafPRAMorphEval

/--
Given a morphism `α : P ⟶ Q` in `PresheafPRACat I J`
(a natural transformation) and a presheaf `Z`,
produce a natural transformation
`praEvalObj P Z ⟶ praEvalObj Q Z`.
At each `j`, the component `α.app j` is a morphism in
`CoprodCovarRepCat`, and `ccrMorphEval` applies it to
each evaluation element.
-/
def praMorphEval
    {P Q : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J}
    (α : P ⟶ Q) (Z : Iᵒᵖ ⥤ Type w_I) :
    praEvalObj I J P Z ⟶ praEvalObj I J Q Z where
  app j := ccrMorphEval (α.app j) Z
  naturality j₁ j₂ g := by
    have h : ccrMorphEval (α.app j₂) Z ∘
        ccrMorphEval (P.map g) Z =
      ccrMorphEval (Q.map g) Z ∘
        ccrMorphEval (α.app j₁) Z := by
      rw [← ccrMorphEval_comp,
          ← ccrMorphEval_comp, α.naturality]
    ext x
    exact congrFun h x

@[simp]
lemma praMorphEval_id
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    praMorphEval I J (𝟙 P) Z =
      𝟙 (praEvalObj I J P Z) := by
  ext j ⟨a, η⟩
  change ccrMorphEval (𝟙 (P.obj j)) Z ⟨a, η⟩ =
    ⟨a, η⟩
  rw [ccrMorphEval_id]; rfl

@[simp]
lemma praMorphEval_comp
    {P Q R : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J}
    (α : P ⟶ Q) (β : Q ⟶ R)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    praMorphEval I J (α ≫ β) Z =
      praMorphEval I J α Z ≫
        praMorphEval I J β Z := by
  ext j ⟨a, η⟩
  change ccrMorphEval ((α ≫ β).app j) Z ⟨a, η⟩ =
    ccrMorphEval (β.app j) Z
      (ccrMorphEval (α.app j) Z ⟨a, η⟩)
  rw [NatTrans.comp_app, ccrMorphEval_comp]; rfl

end PresheafPRAMorphEval

/-! ## Category-Level Evaluation Functor -/

section PresheafPRAEvalCatFunctor

/--
The functor lifting PRAs to functors between presheaf
categories:
`PresheafPRACat I J ⥤
  ((Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _))`.
-/
def praEvalCatFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
      ((Iᵒᵖ ⥤ Type w_I) ⥤
        (Jᵒᵖ ⥤ Type (max w' u_I w_I))) where
  obj P := praEvalFunctor I J P
  map α :=
    { app := fun Z => praMorphEval I J α Z
      naturality := fun Z₁ Z₂ f => by
        ext j ⟨a, η⟩
        simp [praMorphEval, praEvalFunctor,
          praEvalMap, ccrMorphEval, ccrEvalMap,
          Category.assoc] }
  map_id P := by
    ext Z j ⟨a, η⟩
    change ccrMorphEval (NatTrans.app (𝟙 P) j) Z
      ⟨a, η⟩ = ⟨a, η⟩
    rw [NatTrans.id_app, ccrMorphEval_id]; rfl
  map_comp α β := by
    ext Z j ⟨a, η⟩
    change ccrMorphEval ((α ≫ β).app j) Z ⟨a, η⟩ =
      ccrMorphEval (β.app j) Z
        (ccrMorphEval (α.app j) Z ⟨a, η⟩)
    rw [NatTrans.comp_app, ccrMorphEval_comp]; rfl

end PresheafPRAEvalCatFunctor

end GebLean
