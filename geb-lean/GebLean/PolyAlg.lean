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

/-! ## PolyFix as an Algebra

We show that `PolyFix P` is the carrier of an algebra for `P`, and that this
algebra is initial.
-/

section PolyFixAlgebra

variable {X : Type u}

/--
The carrier of the initial algebra: `PolyFix P` viewed as an object of `Over X`.
-/
def polyFixCarrier (P : PolyEndo X) : Over X :=
  (familySliceForward X).obj (PolyFix P)

/--
Extract a child from a morphism `h : family ⟶ polyFixCarrier P` at position `e`.
Uses the commutativity condition to transport the result to the correct fiber.
-/
def polyFixChildAt {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyFixCarrier P)
    (e : (polyBetweenFamily X X P x i).left) :
    PolyFix P ((polyBetweenFamily X X P x i).hom e) :=
  let result := h.left e
  have heq : result.1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  heq ▸ result.2

/--
The family-level structure map: given an index and children, produce a tree.
-/
def polyFixStrFamily (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyFixCarrier P) x) : PolyFix P x :=
  PolyFix.mk x elem.1 (polyFixChildAt elem.1 elem.2)

/--
The underlying function of the structure map.
-/
def polyFixStrLeft (P : PolyEndo X) :
    ((polyEndoFunctor X P).obj (polyFixCarrier P)).left → (polyFixCarrier P).left :=
  fun ⟨x, elem⟩ => ⟨x, polyFixStrFamily P x elem⟩

/--
The structure map commutes with projections to X.
-/
lemma polyFixStr_comm (P : PolyEndo X) :
    polyFixStrLeft P ≫ (polyFixCarrier P).hom =
    ((polyEndoFunctor X P).obj (polyFixCarrier P)).hom := rfl

/--
The structure map for the initial algebra.
-/
def polyFixStr (P : PolyEndo X) :
    (polyEndoFunctor X P).obj (polyFixCarrier P) ⟶ polyFixCarrier P :=
  Over.homMk (polyFixStrLeft P) (polyFixStr_comm P)

/--
The initial algebra of a polynomial endofunctor.
-/
def polyFixAlg (P : PolyEndo X) : PolyAlg P where
  a := polyFixCarrier P
  str := polyFixStr P

/-! ### Catamorphism (Fold) -/

/--
The underlying function of the fold at a specific fiber, defined by recursion
on the tree structure.

For a tree `PolyFix.mk x i children`, we:
1. Recursively fold each child to get elements of `α.a.left`
2. Package these into a morphism `family ⟶ α.a`
3. Apply the target algebra's structure map

Returns the folded value along with a proof it lands in the correct fiber.
-/
def polyFixFoldAtWithProof (P : PolyEndo X) (α : PolyAlg P) (x : X) :
    (t : PolyFix P x) → { y : α.a.left // α.a.hom y = x }
  | PolyFix.mk _ i children =>
    let childrenLeft : (polyBetweenFamily X X P x i).left → α.a.left :=
      fun e => (polyFixFoldAtWithProof P α _ (children e)).val
    have childrenComm : childrenLeft ≫ α.a.hom =
        (polyBetweenFamily X X P x i).hom := by
      funext e
      exact (polyFixFoldAtWithProof P α _ (children e)).property
    let childrenMor : polyBetweenFamily X X P x i ⟶ α.a :=
      Over.homMk childrenLeft childrenComm
    let elem : polyBetweenEvalFamily X X P α.a x := ⟨i, childrenMor⟩
    have hstr : α.a.hom (α.str.left ⟨x, elem⟩) = x :=
      congrFun (Over.w α.str) ⟨x, elem⟩
    ⟨α.str.left ⟨x, elem⟩, hstr⟩

/--
The underlying function of the fold.
-/
def polyFixFoldLeft (P : PolyEndo X) (α : PolyAlg P) :
    (Σ x, PolyFix P x) → α.a.left :=
  fun ⟨x, t⟩ => (polyFixFoldAtWithProof P α x t).val

/--
The fold commutes with projections: folded elements land in the correct fiber.
-/
lemma polyFixFoldLeft_fiber (P : PolyEndo X) (α : PolyAlg P)
    (t : Σ x, PolyFix P x) : α.a.hom (polyFixFoldLeft P α t) = t.1 :=
  (polyFixFoldAtWithProof P α t.1 t.2).property

/--
The catamorphism from the initial algebra to any algebra.
-/
def polyFixFold (P : PolyEndo X) (α : PolyAlg P) : polyFixCarrier P ⟶ α.a :=
  Over.homMk (polyFixFoldLeft P α) (by
    funext ⟨x, t⟩
    exact polyFixFoldLeft_fiber P α ⟨x, t⟩)

/-! ### Fold as Algebra Homomorphism -/

/--
Helper: the functor map on fold at a point.
-/
lemma polyEndoFunctor_map_at (P : PolyEndo X) (α : PolyAlg P)
    {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyFixCarrier P) :
    ((polyEndoFunctor X P).map (polyFixFold P α)).left ⟨x, ⟨i, h⟩⟩ =
    ⟨x, ⟨i, h ≫ polyFixFold P α⟩⟩ := by
  simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left]

/--
Helper: folding with transport preserves the result.
This shows that the fold value is independent of the specific proof path.
-/
lemma polyFixFoldAtWithProof_transport (P : PolyEndo X) (α : PolyAlg P)
    {x y : X} (t : PolyFix P x) (heq : x = y) :
    (polyFixFoldAtWithProof P α y (heq ▸ t)).val =
    (polyFixFoldAtWithProof P α x t).val := by
  subst heq
  rfl

/--
Helper: morphism composition with fold gives the expected result.
-/
lemma fold_comp_morphism_eq (P : PolyEndo X) (α : PolyAlg P)
    {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyFixCarrier P) :
    h ≫ polyFixFold P α =
    Over.homMk (fun e => (polyFixFoldAtWithProof P α _ (polyFixChildAt i h e)).val)
      (by funext e; exact (polyFixFoldAtWithProof P α _ (polyFixChildAt i h e)).property)
      := by
  apply Over.OverMorphism.ext
  funext e
  simp only [Over.comp_left, types_comp_apply, Over.homMk_left]
  simp only [polyFixFold, polyFixFoldLeft, Over.homMk_left]
  simp only [polyFixChildAt]
  have heq : (h.left e).1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  exact (polyFixFoldAtWithProof_transport P α (h.left e).2 heq).symm

/--
The fold satisfies the algebra homomorphism condition: mapping by fold and then
applying the target structure equals applying the source structure and then
folding.
-/
lemma polyFixFold_comm (P : PolyEndo X) (α : PolyAlg P) :
    (polyEndoFunctor X P).map (polyFixFold P α) ≫ α.str =
    polyFixStr P ≫ polyFixFold P α := by
  apply Over.OverMorphism.ext
  funext ⟨x, elem⟩
  simp only [types_comp_apply, Over.comp_left]
  obtain ⟨i, h⟩ := elem
  rw [polyEndoFunctor_map_at P α i h]
  simp only [polyFixStr, polyFixStrLeft, polyFixStrFamily, Over.homMk_left]
  simp only [polyFixFold, polyFixFoldLeft, Over.homMk_left]
  simp only [polyFixFoldAtWithProof]
  have hmor := fold_comp_morphism_eq P α i h
  simp only [polyFixFold] at hmor
  rw [hmor]

/--
The fold as an algebra homomorphism from the initial algebra to any algebra.
-/
def polyFixFoldHom (P : PolyEndo X) (α : PolyAlg P) :
    polyFixAlg P ⟶ α :=
  Endofunctor.Algebra.Hom.mk (polyFixFold P α) (polyFixFold_comm P α)

/-! ### Uniqueness of the Catamorphism -/

/--
When the childrenMor is built from children with rfl proof, polyFixChildAt
recovers the original children.
-/
lemma polyFixChildAt_rfl {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (children : ∀ e : (polyBetweenFamily X X P x i).left,
      PolyFix P ((polyBetweenFamily X X P x i).hom e))
    (e : (polyBetweenFamily X X P x i).left) :
    polyFixChildAt i
      (Over.homMk (fun e => ⟨(polyBetweenFamily X X P x i).hom e, children e⟩) rfl) e =
    children e := rfl

/--
Helper: any algebra homomorphism applied to a tree equals the fold.
Proved by structural recursion on the tree.
-/
def polyFixFoldUnique_at (P : PolyEndo X) (α : PolyAlg P)
    (f : polyFixAlg P ⟶ α) (x : X) (t : PolyFix P x) :
    f.f.left ⟨x, t⟩ = (polyFixFoldAtWithProof P α x t).val := by
  match t with
  | PolyFix.mk _ i children =>
    have hf := f.h
    have hf_at : ∀ (pt : ((polyEndoFunctor X P).obj (polyFixCarrier P)).left),
        α.str.left (((polyEndoFunctor X P).map f.f).left pt) =
        f.f.left ((polyFixStr P).left pt) := by
      intro pt
      exact congrFun (congrArg CommaMorphism.left hf) pt
    let childrenMor : polyBetweenFamily X X P x i ⟶ polyFixCarrier P :=
      Over.homMk (fun e => ⟨(polyBetweenFamily X X P x i).hom e, children e⟩) rfl
    have happ := hf_at ⟨x, ⟨i, childrenMor⟩⟩
    simp only [polyFixStr, polyFixStrLeft, polyFixStrFamily, Over.homMk_left] at happ
    simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
      polyToOverEvalMap, familySliceForward, familySliceForwardMap,
      polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left] at happ
    have hrhs : (fun e => polyFixChildAt i childrenMor e) = children := by
      funext e
      exact polyFixChildAt_rfl i children e
    simp only [hrhs] at happ
    have hIH : ∀ e, f.f.left (childrenMor.left e) =
        (polyFixFoldAtWithProof P α _ (children e)).val := by
      intro e
      simp only [childrenMor, Over.homMk_left]
      exact polyFixFoldUnique_at P α f _ (children e)
    rw [happ.symm]
    simp only [polyFixFoldAtWithProof]
    have heq_mor : (childrenMor ≫ f.f) = Over.homMk
        (fun e => (polyFixFoldAtWithProof P α _ (children e)).val)
        (by funext e; exact (polyFixFoldAtWithProof P α _ (children e)).property) := by
      apply Over.OverMorphism.ext
      funext e
      simp only [Over.comp_left, types_comp_apply, Over.homMk_left, childrenMor]
      exact hIH e
    rw [heq_mor]

/--
Uniqueness: any algebra homomorphism from the initial algebra equals the fold.
-/
lemma polyFixFoldHom_unique (P : PolyEndo X) (α : PolyAlg P)
    (f : polyFixAlg P ⟶ α) : f = polyFixFoldHom P α := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [polyFixFoldHom, polyFixFold, polyFixFoldLeft, Over.homMk_left]
  exact polyFixFoldUnique_at P α f x t

/-! ### Initial Algebra -/

/--
The initial algebra of a polynomial endofunctor.

This shows that `polyFixAlg P` is initial in the category of P-algebras,
providing the universal property of W-types.
-/
def polyFixAlg_isInitial (P : PolyEndo X) :
    CategoryTheory.Limits.IsInitial (polyFixAlg P) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (polyFixFoldHom P)
    (fun α m => polyFixFoldHom_unique P α m)

end PolyFixAlgebra

end GebLean
