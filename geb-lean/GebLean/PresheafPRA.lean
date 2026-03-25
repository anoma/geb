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

/-! ## Presheaf Category Functor -/

/--
The functor `Catᵒᵖ ⥤ Cat` sending `C` to the presheaf
category `C ⥤ Type w_I`.  Obtained by flipping
`catHomProfunctor` and applying `Cat.of (Type w_I)`.
-/
def presheafCatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  catContraHomFunctor.{v_I, u_I, w_I, w_I + 1}
    (Cat.of (Type w_I))

/--
The presheaf category `Iᵒᵖ ⥤ Type w_I` as an object of
`Cat`, obtained by applying `presheafCatFunctor` at
`Iᵒᵖ`.
-/
def presheafCat : Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  presheafCatFunctor.{u_I, v_I, w_I}.obj
    (Opposite.op (Cat.of Iᵒᵖ))

/-! ## CoprodCovarRepCat of the Presheaf Category -/

/--
The functor `Catᵒᵖ ⥤ Cat` sending `C` to
`CoprodCovarRepCat (C ⥤ Type w_I)`.  Defined as
`presheafCatFunctor` composed with
`coprodCovarRepFunctor`.
-/
def ccrPresheafCatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
    Cat.{max w' u_I w_I, max (w' + 1) (w_I + 1) v_I u_I} :=
  presheafCatFunctor.{u_I, v_I, w_I} ⋙
    coprodCovarRepFunctor.{max v_I (w_I + 1) u_I,
      max u_I w_I, w'}

/--
The category of coproducts of covariant representables on
the presheaf category of `I`, as an object of `Cat`.
-/
def ccrPresheafCat :
    Cat.{max w' u_I w_I, max (w' + 1) (w_I + 1) v_I u_I} :=
  ccrPresheafCatFunctor.{u_I, v_I, w_I, w'}.obj
    (Opposite.op (Cat.of Iᵒᵖ))

/-! ## The Category of Presheaf PRAs -/

section PresheafPRADef

/--
Precomposition with `ccrPresheafCatFunctor`: turns a
functor `Cat ⥤ Cat` into a functor `Catᵒᵖ ⥤ Cat` by
precomposing with the `I ↦ CoprodCovarRepCat(Iᵒᵖ ⥤ Type w_I)`
construction.
-/
def ccrPresheafWhiskerLeft :
    (Cat.{max w' u_I w_I,
        max (w' + 1) (w_I + 1) v_I u_I} ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) ⥤
    (Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  (Functor.whiskeringLeft _ _ _).obj
    ccrPresheafCatFunctor.{u_I, v_I, w_I, w'}

/--
The profunctor sending `(J, I)` to the presheaf PRA
category `Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.
Defined as `catHomProfunctor` composed with
`ccrPresheafWhiskerLeft`.  No free category parameters.
-/
def presheafPRACatProfunctor :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      (Cat.{v_I, u_I}ᵒᵖ ⥤
        Cat.{max u_I u_J w_I w',
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  catHomProfunctor.{v_J, u_J,
      max w' u_I w_I,
      max (w' + 1) (w_I + 1) v_I u_I} ⋙
    ccrPresheafWhiskerLeft.{u_I, v_I, u_J, v_J, w_I, w'}

/--
The functor `Catᵒᵖ ⥤ Cat` sending `I` to the category
of presheaf PRAs from `Iᵒᵖ ⥤ Type w_I` to a presheaf
category on `J`.  Defined as `presheafPRACatProfunctor`
applied at `Jᵒᵖ`.
-/
def presheafPRACatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
    Cat.{max u_I u_J w_I w', max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (presheafPRACatProfunctor.{u_I, v_I, u_J, v_J, w_I, w'}).obj
    (Opposite.op (Cat.of Jᵒᵖ))

/--
The category of presheaf polynomial functors (parametric
right adjoints) from `Iᵒᵖ ⥤ Type w_I` to a presheaf
category on `J`.

An object is a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.
At each `j : Jᵒᵖ`, this gives a polynomial
`(A(j), E_j : A(j) → (Iᵒᵖ ⥤ Type w_I))`.  The functor
action on morphisms in `Jᵒᵖ` provides reindexing on
positions and precomposition maps on directions.

Defined as `presheafPRACatFunctor` applied at `Iᵒᵖ`.
-/
def PresheafPRACat :
    Cat.{max u_I u_J w_I w', max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (presheafPRACatFunctor.{u_I, v_I, u_J, v_J, w_I, w'} (J := J)).obj
    (Opposite.op (Cat.of Iᵒᵖ))

end PresheafPRADef

/-! ## Accessors -/

section PresheafPRAAccessors

/--
The positions functor: sends a PRA `P` to the presheaf
on `J` of position types.  Defined as postcomposition
of `P` with `ccrNewIndexFunctor`.
-/
def praPositionsFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J ⥤ (Jᵒᵖ ⥤ Type w') :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The type of positions at stage `j`.
-/
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsFunctor I J).obj P |>.obj j

/--
The directions functor: for a fixed PRA `P`, sends an
element `(j, a)` of the positions presheaf to
`op (praDirectionsAt P j a)`.  Defined as
`ccrNewFamilyFunctor` composed with the induced map
on Elements categories.
-/
def praDirectionsAtFunctor :
    ((praPositionsFunctor I J).obj P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
  elementsPrecomp P ⋙
    ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))

/--
The directions presheaf at position `a` at stage `j`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  ((praDirectionsAtFunctor I J P).obj ⟨j, a⟩).unop

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
def praEvalAt (j : Jᵒᵖ) : Type (max w' u_I w_I) :=
  ccrNewEval (P.obj j) Z

/--
Extract the position index from an evaluation element.
-/
def praEvalAt_index {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praPositions I J P j :=
  x.1

/--
Extract the natural transformation from an evaluation
element.
-/
def praEvalAt_mor {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praDirectionsAt I J P j
      (praEvalAt_index I J P Z x) ⟶ Z :=
  x.2

/--
Construct an evaluation element from a position and a
natural transformation.
-/
def praEvalAt_mk (j : Jᵒᵖ)
    (a : praPositions I J P j)
    (η : praDirectionsAt I J P j a ⟶ Z) :
    praEvalAt I J P Z j :=
  ⟨a, η⟩

end PresheafPRAEvalAt

/-! ## Restriction Maps -/

section PresheafPRARestrict

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Restriction map along a morphism `g : j₁ ⟶ j₂` in `Jᵒᵖ`.
Sends `⟨a, η⟩` to
`⟨ccrNewReindex (P.map g) a, ccrNewFiberMor (P.map g) a ≫ η⟩`.
-/
def praRestrict {j₁ j₂ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) :
    praEvalAt I J P Z j₁ → praEvalAt I J P Z j₂ :=
  ccrNewMorphEval (P.map g) Z

@[simp]
lemma praRestrict_id (j : Jᵒᵖ) :
    praRestrict I J P Z (𝟙 j) =
      id := by
  change ccrNewMorphEval (P.map (𝟙 j)) Z = id
  rw [P.map_id, ccrNewMorphEval_id]

@[simp]
lemma praRestrict_comp {j₁ j₂ j₃ : Jᵒᵖ}
    (g : j₁ ⟶ j₂) (h : j₂ ⟶ j₃) :
    praRestrict I J P Z (g ≫ h) =
      praRestrict I J P Z h ∘
        praRestrict I J P Z g := by
  change ccrNewMorphEval (P.map (g ≫ h)) Z =
    ccrNewMorphEval (P.map h) Z ∘
      ccrNewMorphEval (P.map g) Z
  rw [P.map_comp, ccrNewMorphEval_comp]

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
  app j := ccrNewEvalMap f
  naturality j₁ j₂ g := by
    ext ⟨a, η⟩
    simp [praEvalObj, praRestrict, ccrNewMorphEval,
      ccrNewEvalMap, Category.assoc]

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
  simp [praEvalMap, ccrNewEvalMap, Category.assoc]

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
`CoprodCovarRepCat`, and `ccrNewMorphEval` applies it to
each evaluation element.
-/
def praMorphEval
    {P Q : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J}
    (α : P ⟶ Q) (Z : Iᵒᵖ ⥤ Type w_I) :
    praEvalObj I J P Z ⟶ praEvalObj I J Q Z where
  app j := ccrNewMorphEval (α.app j) Z
  naturality j₁ j₂ g := by
    have h : ccrNewMorphEval (α.app j₂) Z ∘
        ccrNewMorphEval (P.map g) Z =
      ccrNewMorphEval (Q.map g) Z ∘
        ccrNewMorphEval (α.app j₁) Z := by
      rw [← ccrNewMorphEval_comp,
          ← ccrNewMorphEval_comp, α.naturality]
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
  change ccrNewMorphEval (𝟙 (P.obj j)) Z ⟨a, η⟩ =
    ⟨a, η⟩
  rw [ccrNewMorphEval_id]; rfl

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
  change ccrNewMorphEval ((α ≫ β).app j) Z ⟨a, η⟩ =
    ccrNewMorphEval (β.app j) Z
      (ccrNewMorphEval (α.app j) Z ⟨a, η⟩)
  rw [NatTrans.comp_app, ccrNewMorphEval_comp]; rfl

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
          praEvalMap, ccrNewMorphEval, ccrNewEvalMap,
          Category.assoc] }
  map_id P := by
    ext Z j ⟨a, η⟩
    change ccrNewMorphEval (NatTrans.app (𝟙 P) j) Z
      ⟨a, η⟩ = ⟨a, η⟩
    rw [NatTrans.id_app, ccrNewMorphEval_id]; rfl
  map_comp α β := by
    ext Z j ⟨a, η⟩
    change ccrNewMorphEval ((α ≫ β).app j) Z ⟨a, η⟩ =
      ccrNewMorphEval (β.app j) Z
        (ccrNewMorphEval (α.app j) Z ⟨a, η⟩)
    rw [NatTrans.comp_app, ccrNewMorphEval_comp]; rfl

end PresheafPRAEvalCatFunctor

end GebLean
