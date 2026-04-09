import GebLean.Polynomial
import GebLean.Utilities.Presheaf
import GebLean.Utilities.Elements
import GebLean.Utilities.Families
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.Currying

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
category `C ⥤ Type w_I`.
-/
def presheafCatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  catContraHomFunctor.{v_I, u_I, w_I, w_I + 1}
    (Cat.of (Type w_I))

/--
The presheaf category `Iᵒᵖ ⥤ Type w_I` as an object of `Cat`.
-/
def presheafCat : Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  presheafCatFunctor.{u_I, v_I, w_I}.obj
    (Opposite.op (Cat.of Iᵒᵖ))

/-! ## CoprodCovarRepCat of the Presheaf Category -/

/--
The functor `Catᵒᵖ ⥤ Cat` sending `C` to
`CoprodCovarRepCat (C ⥤ Type w_I)`.
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
functor `Cat ⥤ Cat` into a functor `Catᵒᵖ ⥤ Cat`.
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
category on `J`.
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
on `J` of position types.
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
presheaf to `op (E_T(j,a))`.
-/
def praDirectionsAtFunctorOp :
    ((praPositionsFunctor I J).obj P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
  CategoryTheory.elementsPrecomp P ⋙
    ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))

/--
The directions functor `E_T` from the nLab PRA
formula: sends an element `(j, a)` of the opposite
of the positions presheaf to the directions presheaf
`E_T(j,a) : Iᵒᵖ ⥤ Type w_I`.
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
The evaluation profunctor: sends a PRA `P` to the
functor `Jᵒᵖ ⥤ (PSh(I) ⥤ Type _)` that at each `j`
evaluates the polynomial `P(j)`.
-/
def praEvalAtProfunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
    Jᵒᵖ ⥤ (Iᵒᵖ ⥤ Type w_I) ⥤ Type (max w' u_I w_I) :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewEvalCatFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))

/--
The evaluation functor: sends a PRA `P` to the functor
`PSh(I) ⥤ PSh(J)` (in the `Type _` form
`(Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _)`).
-/
def praEvalAtFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
    (Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type (max w' u_I w_I)) :=
  praEvalAtProfunctor I J ⋙
    Functor.flipping.functor

/--
`praEvalAtProfunctor` is fully faithful: every natural
transformation between evaluation profunctors arises
from a unique PRA morphism.
-/
def praEvalAtProfunctorFullyFaithful :
    (praEvalAtProfunctor I J).FullyFaithful :=
  Functor.FullyFaithful.whiskeringRight
    (ccrNewEvalCatFullyFaithful.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))
    Jᵒᵖ

/--
`praEvalAtFunctor` is fully faithful: every natural
transformation between PRA evaluation functors
`PSh(I) ⥤ PSh(J)` arises from a unique PRA morphism.
-/
def praEvalAtFunctorFullyFaithful :
    (praEvalAtFunctor I J).FullyFaithful :=
  (praEvalAtProfunctorFullyFaithful I J).comp
    Functor.flipping.fullyFaithfulFunctor

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Pointwise evaluation of a presheaf PRA at a presheaf `Z` and
stage `j`.  The result is
`Σ_{a : praPositions P j} (praDirectionsAt P j a ⟶ Z)`.
-/
def praEvalAt (j : Jᵒᵖ) : Type (max w' u_I w_I) :=
  ((praEvalAtProfunctor I J).obj P).obj j |>.obj Z

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
