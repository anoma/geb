import GebLean.Polynomial
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Algebras of Polynomial Endofunctors

This module defines algebras of polynomial endofunctors on slice categories
of `Type`, building on the polynomial functor infrastructure in `Polynomial.lean`.

## Main definitions

* `PolyEndo X` - Polynomial endofunctors on `Over X` (via Grothendieck)
* `WTypeEndo X` - Polynomial endofunctors on `Over X` (via W-type diagrams)
* `polyEndoFunctor` - Convert polynomial representation to actual functor
* `wTypeEndoFunctor` - Convert W-type representation to actual functor
* `PolyAlg` - Algebras of a polynomial endofunctor (using mathlib's Algebra)
* `PolyFix` - Fixed point (initial algebra carrier) of a polynomial endofunctor
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Polynomial Endofunctors

A polynomial endofunctor on `Over X` is a polynomial functor `Over X → Over X`,
i.e., a `PolyFunctorBetweenCat X X` or equivalently a `WTypeDiagram X X`.
-/

section PolyEndo

variable (X : Type u)

/--
Polynomial endofunctors on `Over X`, represented via coproducts of
covariant representables (Grothendieck construction style).

An object is an `X`-indexed family of polynomial functors `Over X → Type`.
-/
abbrev PolyEndo : Cat := PolyFunctorBetweenCat X X

/--
Polynomial endofunctors on `Over X`, represented via W-type diagrams.

A W-type diagram `X ← E → B → X` where both the source and target maps
land in `X`.
-/
abbrev WTypeEndo : Cat := WTypeDiagramCat X X

/--
The equivalence between the two representations of polynomial endofunctors.
-/
def polyEndoEquiv : WTypeEndo X ≌ PolyEndo X := wTypePolyBetweenEquiv

/--
Convert a polynomial endofunctor representation to an actual endofunctor.
-/
def polyEndoFunctor (P : PolyEndo X) : Over X ⥤ Over X :=
  polyBetweenEvalFunctor X X P

/--
Convert a W-type endofunctor representation to an actual endofunctor.
-/
def wTypeEndoFunctor (W : WTypeEndo X) : Over X ⥤ Over X :=
  W.evalFunctor X X

end PolyEndo

/-! ## Algebras of Polynomial Endofunctors

An algebra of a polynomial endofunctor `P : Over X → Over X` consists of:
- A carrier object `A : Over X`
- A structure map `str : P(A) → A` (as a morphism in `Over X`)

We use mathlib's `Endofunctor.Algebra` to get the category structure for free.
-/

section PolyAlgebra

variable {X : Type u}

/--
An algebra of a polynomial endofunctor `P` on `Over X`.

This is mathlib's `Endofunctor.Algebra` applied to the functor represented by `P`.
The carrier is an object `A : Over X`, and the structure map is a morphism
`P(carrier) ⟶ carrier` in `Over X`.
-/
abbrev PolyAlg (P : PolyEndo X) := Endofunctor.Algebra (polyEndoFunctor X P)

/--
An algebra of a W-type endofunctor `W` on `Over X`.

This is mathlib's `Endofunctor.Algebra` applied to the functor represented by `W`.
-/
abbrev WTypeAlg (W : WTypeEndo X) := Endofunctor.Algebra (wTypeEndoFunctor X W)

/--
The category of algebras for a polynomial endofunctor.
This is inherited automatically from mathlib's `Endofunctor.Algebra.instCategory`.
-/
instance (P : PolyEndo X) : Category (PolyAlg P) :=
  Endofunctor.Algebra.instCategory (polyEndoFunctor X P)

/--
The category of algebras for a W-type endofunctor.
-/
instance (W : WTypeEndo X) : Category (WTypeAlg W) :=
  Endofunctor.Algebra.instCategory (wTypeEndoFunctor X W)

/--
The forgetful functor from polynomial algebras to `Over X`.
-/
def PolyAlg.forget (P : PolyEndo X) : PolyAlg P ⥤ Over X :=
  Endofunctor.Algebra.forget (polyEndoFunctor X P)

/--
The forgetful functor from W-type algebras to `Over X`.
-/
def WTypeAlg.forget (W : WTypeEndo X) : WTypeAlg W ⥤ Over X :=
  Endofunctor.Algebra.forget (wTypeEndoFunctor X W)

end PolyAlgebra

/-! ## Fixed Points of Polynomial Endofunctors

For a polynomial endofunctor `P` on `Over X`, we define `PolyFix P` as an
inductive type representing the initial algebra carrier.

The construction is that for a polynomial `P` with:
- Index type `I_x` at each `x : X`
- Family `F_{x,i} : Over X` for each `x : X` and `i : I_x`

An element of the fixed point over `x` consists of:
- An index `i : I_x`
- For each fiber element of `F_{x,i}`, a recursive element of the fixed point
-/

section PolyFix

variable {X : Type u}

/--
The fixed point of a polynomial endofunctor on `Over X`.

For `P : PolyEndo X` and `x : X`, `PolyFix P x` is the type of well-founded
trees whose nodes at position `x` are labeled by indices `i : polyBetweenIndex P x`
and whose children are determined by the fibers of the polynomial at that index.

This is analogous to `PFunctor.W` and `QPF.Fix` but for polynomial functors
between slice categories.
-/
inductive PolyFix (P : PolyEndo X) : X → Type u where
  | mk (x : X) (i : polyBetweenIndex X X P x)
       (children : ∀ (e : (polyBetweenFamily X X P x i).left),
         PolyFix P ((polyBetweenFamily X X P x i).hom e)) :
       PolyFix P x

/--
Extract the index from a PolyFix node.
-/
def PolyFix.index {P : PolyEndo X} {x : X} : PolyFix P x → polyBetweenIndex X X P x
  | mk _ i _ => i

/--
Extract the children function from a PolyFix node.
-/
def PolyFix.getChildren {P : PolyEndo X} {x : X} (t : PolyFix P x) :
    ∀ (e : (polyBetweenFamily X X P x t.index).left),
      PolyFix P ((polyBetweenFamily X X P x t.index).hom e) :=
  match t with
  | mk _ _ f => f

end PolyFix

end GebLean
