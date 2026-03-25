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
The directions functor into `PSh(I)ᵒᵖ`: for a fixed
PRA `P`, sends an element `(j, a)` of the positions
presheaf to `op (E_T(j,a))`.  Defined as
`ccrNewFamilyFunctor` composed with the induced map
on Elements categories.
-/
def praDirectionsAtFunctorOp :
    ((praPositionsFunctor I J).obj P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
  elementsPrecomp P ⋙
    ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))

/--
The directions functor `E_T` from the nLab PRA
formula: sends an element `(j, a)` of the opposite
of the positions presheaf to the directions presheaf
`E_T(j,a) : Iᵒᵖ ⥤ Type w_I`.  Defined as the
opposite of `praDirectionsAtFunctorOp` composed with
`unopUnop`.
-/
def praDirectionsAtFunctor :
    ((praPositionsFunctor I J).obj P).ElementsPre ⥤
      (Iᵒᵖ ⥤ Type w_I) :=
  (praDirectionsAtFunctorOp I J P).op ⋙
    unopUnop _

/--
The directions presheaf at position `a` at stage `j`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsAtFunctor I J P).obj
    (Opposite.op ⟨j, a⟩)

end PresheafPRAAccessors

/-! ## Pointwise Evaluation -/

section PresheafPRAEvalAt

/--
The evaluation functor varying in `P`: sends a PRA `P`
to the functor `Jᵒᵖ ⥤ (PSh(I) ⥤ Type _)` that at
each `j` evaluates the polynomial `P(j)`.  Defined as
postcomposition of `P` with `ccrNewEvalCatFunctor`.
-/
def praEvalAtFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J ⥤
    (Jᵒᵖ ⥤ ((Iᵒᵖ ⥤ Type w_I) ⥤
      Type (max w' u_I w_I))) :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewEvalCatFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Pointwise evaluation of a presheaf PRA at a presheaf `Z` and
stage `j`.  The result is
`Σ_{a : praPositions P j} (praDirectionsAt P j a ⟶ Z)`.
-/
def praEvalAt (j : Jᵒᵖ) : Type (max w' u_I w_I) :=
  ((praEvalAtFunctor I J).obj P).obj j |>.obj Z

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

end GebLean
