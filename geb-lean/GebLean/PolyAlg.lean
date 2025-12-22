import GebLean.Polynomial
import GebLean.Utilities.Equalities
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

/-! ### Lambek's Lemma for Initial Algebras -/

/--
The children of a `PolyFix` tree as an `Over` morphism.
-/
def polyFixChildrenMor {P : PolyEndo X} {x : X} (t : PolyFix P x) :
    polyBetweenFamily X X P x t.index ⟶ polyFixCarrier P :=
  Over.homMk
    (fun e => ⟨(polyBetweenFamily X X P x t.index).hom e, t.getChildren e⟩)
    rfl

/--
The family-level destructor: extract the index and children morphism.
-/
def polyFixDestFamily (P : PolyEndo X) (x : X) (t : PolyFix P x) :
    polyBetweenEvalFamily X X P (polyFixCarrier P) x :=
  ⟨t.index, polyFixChildrenMor t⟩

/--
The underlying function of the destructor.
-/
def polyFixDestLeft (P : PolyEndo X) :
    (polyFixCarrier P).left → ((polyEndoFunctor X P).obj (polyFixCarrier P)).left :=
  fun ⟨x, t⟩ => ⟨x, polyFixDestFamily P x t⟩

/--
The destructor commutes with projections to X.
-/
lemma polyFixDest_comm (P : PolyEndo X) :
    polyFixDestLeft P ≫ ((polyEndoFunctor X P).obj (polyFixCarrier P)).hom =
    (polyFixCarrier P).hom := rfl

/--
The destructor for the initial algebra: extracts the index and children from
a `PolyFix` tree.
-/
def polyFixDest (P : PolyEndo X) :
    polyFixCarrier P ⟶ (polyEndoFunctor X P).obj (polyFixCarrier P) :=
  Over.homMk (polyFixDestLeft P) (polyFixDest_comm P)

/--
The child extraction from a morphism composed with packaging returns the
original element.
-/
lemma polyFixChildAt_sigma_eq {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyFixCarrier P)
    (e : (polyBetweenFamily X X P x i).left) :
    (⟨(polyBetweenFamily X X P x i).hom e, polyFixChildAt i h e⟩ :
      (Σ y, PolyFix P y)) = h.left e := by
  simp only [polyFixChildAt]
  have heq : (h.left e).1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  conv_rhs => rw [← Sigma.eta (h.left e)]
  congr 1
  · exact heq.symm
  · exact (heq_eqRec_iff_heq.mpr HEq.rfl).symm

/--
The structure map followed by the destructor is the identity on `P(PolyFix)`.
-/
lemma polyFixStr_dest (P : PolyEndo X) :
    polyFixStr P ≫ polyFixDest P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  funext ⟨x, elem⟩
  simp only [Over.comp_left, types_comp_apply, Over.id_left, types_id_apply,
    polyFixStr, Over.homMk_left, polyFixStrLeft, polyFixDest,
    polyFixDestLeft, polyFixDestFamily]
  congr 1
  simp only [polyFixStrFamily, PolyFix.index]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyFixChildrenMor, PolyFix.getChildren]
    apply Over.OverMorphism.ext
    funext e
    simp only [Over.homMk_left]
    exact polyFixChildAt_sigma_eq elem.1 elem.2 e

/--
The destructor followed by the structure map is the identity on `PolyFix`.
-/
lemma polyFixDest_str (P : PolyEndo X) :
    polyFixDest P ≫ polyFixStr P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply, Over.id_left, types_id_apply,
    polyFixDest, Over.homMk_left, polyFixDestLeft, polyFixStr, polyFixStrLeft]
  congr 1
  match t with
  | PolyFix.mk _ i children =>
    simp only [polyFixDestFamily, PolyFix.index, polyFixStrFamily,
      polyFixChildrenMor, PolyFix.getChildren]
    rfl

/--
Lambek's Lemma for the initial algebra: the structure map is an isomorphism.
-/
def polyFixStr_iso (P : PolyEndo X) :
    (polyEndoFunctor X P).obj (polyFixCarrier P) ≅ polyFixCarrier P where
  hom := polyFixStr P
  inv := polyFixDest P
  hom_inv_id := polyFixStr_dest P
  inv_hom_id := polyFixDest_str P

end PolyFixAlgebra

/-! ## Coalgebras of Polynomial Endofunctors

The dual of an algebra: a coalgebra of a polynomial endofunctor `P : Over X →
Over X` consists of:
- A carrier object `A : Over X`
- A structure map `str : A → P(A)` (as a morphism in `Over X`)

We use mathlib's `Endofunctor.Coalgebra` to get the category structure.
-/

section PolyCoalgebra

variable {X : Type u}

/--
A coalgebra of a polynomial endofunctor `P` on `Over X`.

This is mathlib's `Endofunctor.Coalgebra` applied to the functor represented
by `P`. The carrier is an object `A : Over X`, and the structure map is a
morphism `carrier ⟶ P(carrier)` in `Over X`.
-/
abbrev PolyCoalg (P : PolyEndo X) := Endofunctor.Coalgebra (polyEndoFunctor X P)

/--
A coalgebra of a W-type endofunctor `W` on `Over X`.
-/
abbrev WTypeCoalg (W : WTypeEndo X) :=
  Endofunctor.Coalgebra (wTypeEndoFunctor X W)

/--
The category of coalgebras for a polynomial endofunctor.
This is inherited automatically from mathlib's `Endofunctor.Coalgebra`.
-/
instance (P : PolyEndo X) : Category (PolyCoalg P) :=
  Endofunctor.Coalgebra.instCategory (polyEndoFunctor X P)

/--
The category of coalgebras for a W-type endofunctor.
-/
instance (W : WTypeEndo X) : Category (WTypeCoalg W) :=
  Endofunctor.Coalgebra.instCategory (wTypeEndoFunctor X W)

/--
The forgetful functor from polynomial coalgebras to `Over X`.
-/
def PolyCoalg.forget (P : PolyEndo X) : PolyCoalg P ⥤ Over X :=
  Endofunctor.Coalgebra.forget (polyEndoFunctor X P)

/--
The forgetful functor from W-type coalgebras to `Over X`.
-/
def WTypeCoalg.forget (W : WTypeEndo X) : WTypeCoalg W ⥤ Over X :=
  Endofunctor.Coalgebra.forget (wTypeEndoFunctor X W)

end PolyCoalgebra

/-! ## Cofixed Points of Polynomial Endofunctors (M-types)

For a polynomial endofunctor `P` on `Over X`, we define `PolyCofix P` as the
terminal coalgebra carrier, representing potentially infinite trees.

The construction follows mathlib's approach: define approximations at each
depth level, then take the limit of consistent sequences.
-/

section PolyCofixApprox

variable {X : Type u}

/--
Approximations of the cofixed point at depth `n`.

At depth 0, we have no information (just a placeholder).
At depth `n + 1`, we have an index and children at depth `n`.
-/
inductive PolyCofixApprox (P : PolyEndo X) : Nat → X → Type u where
  | continue : (x : X) → PolyCofixApprox P 0 x
  | intro {n : Nat} (x : X) (i : polyBetweenIndex X X P x)
      (children : ∀ (e : (polyBetweenFamily X X P x i).left),
        PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e)) :
      PolyCofixApprox P (n + 1) x

/--
Extract the index from a non-zero depth approximation.
-/
def PolyCofixApprox.getIndex {P : PolyEndo X} {n : Nat} {x : X}
    (a : PolyCofixApprox P (n + 1) x) : polyBetweenIndex X X P x :=
  match a with
  | .intro _ i _ => i

/--
Extract the children function from a non-zero depth approximation.
-/
def PolyCofixApprox.getChildren {P : PolyEndo X} {n : Nat} {x : X}
    (a : PolyCofixApprox P (n + 1) x) :
    ∀ (e : (polyBetweenFamily X X P x a.getIndex).left),
      PolyCofixApprox P n ((polyBetweenFamily X X P x a.getIndex).hom e) :=
  match a with
  | .intro _ _ f => f

/--
Agreement relation between successive approximations.

Two approximations agree if they have the same "shape" at their shared depth:
- Any depth-0 approximation agrees with any depth-1 approximation.
- Two intro nodes agree if they have the same index and all children agree.
-/
inductive PolyCofixAgree (P : PolyEndo X) :
    {n : Nat} → {x : X} →
    PolyCofixApprox P n x → PolyCofixApprox P (n + 1) x → Prop where
  | continue (x : X) (y : PolyCofixApprox P 1 x) :
      PolyCofixAgree P (.continue x) y
  | intro {n : Nat} {x : X} {i : polyBetweenIndex X X P x}
      (f : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e))
      (f' : ∀ e, PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x i).hom e))
      (h : ∀ e, PolyCofixAgree P (f e) (f' e)) :
      PolyCofixAgree P (.intro x i f) (.intro x i f')

lemma PolyCofixApprox.continue_cast {P : PolyEndo X} {x y : X} (h : x = y) :
    h ▸ PolyCofixApprox.continue (P := P) x = PolyCofixApprox.continue y := by
  subst h
  rfl

/--
Variant of `continue_cast` producing equality in the source fiber.
Given `h : x = y`, we have `continue x = h ▸ continue y` in `Approx 0 x`.
-/
lemma PolyCofixApprox.continue_cast' {P : PolyEndo X} {x y : X} (h : x = y) :
    PolyCofixApprox.continue (P := P) x = h ▸ PolyCofixApprox.continue y := by
  subst h
  rfl

/--
Two `.continue` values in the same polynomial functor are HEq when their fibers are equal.
-/
lemma PolyCofixApprox.continue_heq {P : PolyEndo X} {x y : X} (h : x = y) :
    HEq (PolyCofixApprox.continue (P := P) x) (PolyCofixApprox.continue (P := P) y) := by
  subst h
  exact HEq.rfl

lemma PolyCofixApprox.intro_cast_heq {P : PolyEndo X} {n : Nat} {x y : X}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (j : polyBetweenIndex X X P y)
    (hij : HEq i j)
    (f : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e))
    (g : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P y j).hom e))
    (hfg : HEq f g) :
    hxy ▸ PolyCofixApprox.intro x i f = PolyCofixApprox.intro y j g := by
  subst hxy
  have hi : i = j := eq_of_heq hij
  subst hi
  have hf : f = g := eq_of_heq hfg
  subst hf
  rfl

/--
HEq between two transported intros when their components are HEq.
This handles the case where both sides have transports.
-/
lemma PolyCofixApprox.intro_cast_heq' {P : PolyEndo X} {n : Nat}
    {x₁ y₁ x₂ y₂ : X}
    (hxy₁ : x₁ = y₁) (hxy₂ : x₂ = y₂)
    (hy : y₁ = y₂)
    (hx : x₁ = x₂)
    (i₁ : polyBetweenIndex X X P x₁)
    (i₂ : polyBetweenIndex X X P x₂)
    (hij : HEq i₁ i₂)
    (f : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x₁ i₁).hom e))
    (g : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x₂ i₂).hom e))
    (hfg : HEq f g) :
    HEq (hxy₁ ▸ PolyCofixApprox.intro x₁ i₁ f)
        (hxy₂ ▸ PolyCofixApprox.intro x₂ i₂ g) := by
  subst hxy₁ hxy₂ hx
  have hi : i₁ = i₂ := eq_of_heq hij
  subst hi
  have hf : f = g := eq_of_heq hfg
  subst hf
  rfl

lemma PolyCofixApprox.approx_zero_eq_continue {P : PolyEndo X} {x : X}
    (a : PolyCofixApprox P 0 x) : a = PolyCofixApprox.continue x := by
  match a with
  | .continue _ => rfl

/--
Congruence lemma for `PolyCofixApprox.intro`: two intro approximations at the
same fiber are equal if their indices and children functions match.
-/
lemma PolyCofixApprox.intro_congr {P : PolyEndo X} {n : Nat} {x : X}
    {i : polyBetweenIndex X X P x}
    {f1 f2 : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e)}
    (hf : ∀ e, f1 e = f2 e) :
    PolyCofixApprox.intro x i f1 = PolyCofixApprox.intro x i f2 := by
  congr 1
  funext e
  exact hf e

end PolyCofixApprox

/-! ### The M-type as Consistent Sequences -/

section PolyCofix

variable {X : Type u}

/--
The cofixed point (M-type) of a polynomial endofunctor at a fiber.

An element consists of:
- A sequence of approximations at each depth level
- A proof that successive approximations agree
-/
structure PolyCofix (P : PolyEndo X) (x : X) where
  approx : ∀ n, PolyCofixApprox P n x
  consistent : ∀ n, PolyCofixAgree P (approx n) (approx (n + 1))

/--
Get the head (index) of a cofixed point element.

For any M-type element, we can look at depth 1 to get the index.
-/
def PolyCofix.head {P : PolyEndo X} {x : X} (m : PolyCofix P x) :
    polyBetweenIndex X X P x :=
  (m.approx 1).getIndex

/--
Agreement implies the indices match.

When two approximations agree at depth n and n+1, if both are intro nodes,
they must have the same index.
-/
lemma PolyCofixAgree.index_eq {P : PolyEndo X} {n : Nat} {x : X}
    {a : PolyCofixApprox P (n + 1) x} {b : PolyCofixApprox P (n + 2) x}
    (h : PolyCofixAgree P a b) :
    a.getIndex = b.getIndex := by
  cases h with
  | intro f f' hch => rfl

/--
The index at depth n+1 equals the head (index at depth 1) for any consistent
sequence.
-/
lemma PolyCofix.index_eq_head {P : PolyEndo X} {x : X} (m : PolyCofix P x)
    (n : Nat) : (m.approx (n + 1)).getIndex = m.head := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := (m.consistent (n + 1)).index_eq
    rw [← ih, h]

/--
Extract the children at depth 0 (always continue).
-/
def PolyCofix.childApproxAt_zero {P : PolyEndo X} {x : X}
    (_m : PolyCofix P x) (y : X) :
    PolyCofixApprox P 0 y :=
  .continue y

/--
Extract the children at depth n+1 from an approximation at depth n+2.

Given an approximation `.intro x i children` at depth n+2, the index `i` may differ
from the head `head` (which is the index at depth 1), but they are propositionally
equal. This function extracts children and casts to the target type.
-/
def PolyCofix.childApproxAt_succ_aux {P : PolyEndo X} {x : X} {n : Nat}
    (head : polyBetweenIndex X X P x)
    (a : PolyCofixApprox P (n + 2) x)
    (heq : a.getIndex = head)
    (e : (polyBetweenFamily X X P x head).left) :
    PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x head).hom e) :=
  match a with
  | .intro _ i children =>
    Eq.recOn (motive := fun j _ =>
        (e : (polyBetweenFamily X X P x j).left) →
          PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x j).hom e))
      (heq : i = head) children e

/--
Extract the children at depth n+1.
-/
def PolyCofix.childApproxAt_succ {P : PolyEndo X} {x : X}
    (m : PolyCofix P x) (e : (polyBetweenFamily X X P x m.head).left) (n : Nat) :
    PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x m.head).hom e) :=
  childApproxAt_succ_aux m.head (m.approx (n + 2)) (m.index_eq_head (n + 1)) e

/--
Extract the children at a specific depth level.
-/
def PolyCofix.childApproxAt {P : PolyEndo X} {x : X} (m : PolyCofix P x)
    (e : (polyBetweenFamily X X P x m.head).left) (n : Nat) :
    PolyCofixApprox P n ((polyBetweenFamily X X P x m.head).hom e) :=
  match n with
  | 0 => m.childApproxAt_zero _
  | n + 1 => m.childApproxAt_succ e n

/--
Helper to extract the agree relation on children given the parent agree.
-/
lemma PolyCofixAgree.children_agree {P : PolyEndo X} {n : Nat} {x : X}
    {i : polyBetweenIndex X X P x}
    {f : ∀ e, PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x i).hom e)}
    {f' : ∀ e, PolyCofixApprox P (n + 2) ((polyBetweenFamily X X P x i).hom e)}
    (h : PolyCofixAgree P (.intro x i f) (.intro x i f'))
    (e : (polyBetweenFamily X X P x i).left) :
    PolyCofixAgree P (f e) (f' e) := by
  cases h with
  | intro _ _ hch => exact hch e

/--
The child approximations form a consistent sequence at depth 0.
-/
lemma PolyCofix.childApprox_consistent_zero {P : PolyEndo X} {x : X}
    (m : PolyCofix P x) (e : (polyBetweenFamily X X P x m.head).left) :
    PolyCofixAgree P (m.childApproxAt e 0) (m.childApproxAt e 1) := by
  simp only [childApproxAt, childApproxAt_zero, childApproxAt_succ]
  exact .continue _ _

/--
Auxiliary lemma: when the approximation is an intro node with the same index as head,
`childApproxAt_succ_aux` simplifies to the children function.
-/
lemma PolyCofix.childApproxAt_succ_aux_intro {P : PolyEndo X} {x : X} {n : Nat}
    (head : polyBetweenIndex X X P x)
    (f : ∀ e, PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x head).hom e))
    (e : (polyBetweenFamily X X P x head).left) :
    childApproxAt_succ_aux head (.intro x head f) rfl e = f e := rfl

/--
Extracting children from a transported `.intro` node.

When the approximation is `hxy ▸ .intro x i f` in fiber `y`, extracting children at
position `e` in the transported family gives the original children function applied
to the corresponding position in the original family, then transported.
-/
lemma PolyCofix.childApproxAt_succ_aux_cast {P : PolyEndo X} {x y : X} {n : Nat}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (f : ∀ e, PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x i).hom e))
    (heq : (hxy ▸ PolyCofixApprox.intro x i f).getIndex = hxy ▸ i)
    (e : (polyBetweenFamily X X P y (hxy ▸ i)).left)
    (e' : (polyBetweenFamily X X P x i).left)
    (he : HEq e' e)
    (hfib : (polyBetweenFamily X X P x i).hom e' =
        (polyBetweenFamily X X P y (hxy ▸ i)).hom e) :
    childApproxAt_succ_aux (hxy ▸ i) (hxy ▸ .intro x i f) heq e =
      hfib ▸ f e' := by
  subst hxy
  have he' : e' = e := eq_of_heq he
  subst he'
  rfl

/--
The result of `childApproxAt_succ_aux` is independent of the specific equality proof.
-/
lemma PolyCofix.childApproxAt_succ_aux_proof_irrel {P : PolyEndo X} {x : X} {n : Nat}
    (head : polyBetweenIndex X X P x)
    (a : PolyCofixApprox P (n + 2) x)
    (heq1 heq2 : a.getIndex = head)
    (e : (polyBetweenFamily X X P x head).left) :
    childApproxAt_succ_aux head a heq1 e = childApproxAt_succ_aux head a heq2 e := by
  congr 1

/--
`childApproxAt_succ_aux` preserves heterogeneous equality when all arguments are HEq.
-/
lemma PolyCofix.childApproxAt_succ_aux_heq {P : PolyEndo X} {x1 x2 : X} {n : Nat}
    (hx : x1 = x2)
    (head1 : polyBetweenIndex X X P x1)
    (head2 : polyBetweenIndex X X P x2)
    (hhead : HEq head1 head2)
    (a1 : PolyCofixApprox P (n + 2) x1)
    (a2 : PolyCofixApprox P (n + 2) x2)
    (ha : HEq a1 a2)
    (heq1 : a1.getIndex = head1)
    (heq2 : a2.getIndex = head2)
    (e1 : (polyBetweenFamily X X P x1 head1).left)
    (e2 : (polyBetweenFamily X X P x2 head2).left)
    (he : HEq e1 e2) :
    HEq (childApproxAt_succ_aux head1 a1 heq1 e1)
        (childApproxAt_succ_aux head2 a2 heq2 e2) := by
  subst hx
  cases hhead
  cases ha
  cases he
  exact HEq.rfl

/--
Helper for proving child consistency. When two approximations agree at the intro
level, and we know the indices equal the head, we can extract the child agreement.
-/
lemma PolyCofix.childApprox_consistent_aux {P : PolyEndo X} {x : X} {n : Nat}
    (head : polyBetweenIndex X X P x)
    (i : polyBetweenIndex X X P x)
    (f : ∀ e, PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P x i).hom e))
    (g : ∀ e, PolyCofixApprox P (n + 2) ((polyBetweenFamily X X P x i).hom e))
    (hch : ∀ e, PolyCofixAgree P (f e) (g e))
    (hi : i = head)
    (e : (polyBetweenFamily X X P x head).left) :
    PolyCofixAgree P
      (childApproxAt_succ_aux head (.intro x i f) hi e)
      (childApproxAt_succ_aux head (.intro x i g) hi e) := by
  subst hi
  simp only [childApproxAt_succ_aux]
  exact hch e

/--
The child approximations form a consistent sequence at successor depth.

We prove this by using the fact that successive approximations agree, which means
they're both intro nodes with the same index.
-/
lemma PolyCofix.childApprox_consistent_succ {P : PolyEndo X} {x : X}
    (m : PolyCofix P x) (e : (polyBetweenFamily X X P x m.head).left) (n : Nat) :
    PolyCofixAgree P (m.childApproxAt e (n + 1)) (m.childApproxAt e (n + 2)) := by
  simp only [childApproxAt, childApproxAt_succ]
  have hcons := m.consistent (n + 2)
  have heq1 : (m.approx (n + 2)).getIndex = m.head := m.index_eq_head (n + 1)
  have heq2 : (m.approx (n + 3)).getIndex = m.head := m.index_eq_head (n + 2)
  conv_lhs => rw [childApproxAt_succ_aux_proof_irrel m.head (m.approx (n + 2))
    (m.index_eq_head (n + 1)) heq1 e]
  conv_rhs => rw [childApproxAt_succ_aux_proof_irrel m.head (m.approx (n + 3))
    (m.index_eq_head (n + 2)) heq2 e]
  generalize ha : m.approx (n + 2) = a at hcons heq1
  generalize hb : m.approx (n + 3) = b at hcons heq2
  match a, b, hcons with
  | .intro _ i f, .intro _ _ g, .intro _ _ hch =>
    exact childApprox_consistent_aux m.head i f g hch heq1 e

/--
The child approximations form a consistent sequence.
-/
lemma PolyCofix.childApprox_consistent {P : PolyEndo X} {x : X}
    (m : PolyCofix P x) (e : (polyBetweenFamily X X P x m.head).left) (n : Nat) :
    PolyCofixAgree P (m.childApproxAt e n) (m.childApproxAt e (n + 1)) :=
  match n with
  | 0 => m.childApprox_consistent_zero e
  | n + 1 => m.childApprox_consistent_succ e n

/--
The children of a cofixed point element form cofixed points themselves.

For each position `e` in the family, we extract the subtree by taking the
children at each depth level.
-/
def PolyCofix.children {P : PolyEndo X} {x : X} (m : PolyCofix P x)
    (e : (polyBetweenFamily X X P x m.head).left) :
    PolyCofix P ((polyBetweenFamily X X P x m.head).hom e) where
  approx := m.childApproxAt e
  consistent := m.childApprox_consistent e

/--
Two cofixed points are equal if their approximations are equal at all depths.
-/
@[ext]
lemma PolyCofix.ext {P : PolyEndo X} {x : X} {m₁ m₂ : PolyCofix P x}
    (h : ∀ n, m₁.approx n = m₂.approx n) : m₁ = m₂ := by
  cases m₁
  cases m₂
  simp only [mk.injEq]
  funext n
  exact h n

lemma PolyCofix.approx_cast {P : PolyEndo X} {x y : X}
    (h : x = y) (m : PolyCofix P x) (n : Nat) :
    (h ▸ m).approx n = h ▸ (m.approx n) := by
  subst h
  rfl

/--
HEq of PolyCofix elements implies HEq of their approximations.

Note: The fiber equality `hx` must be provided explicitly since HEq alone does
not allow extracting the fiber equality in dependent type contexts.
-/
lemma PolyCofix.approx_heq {P : PolyEndo X} {x1 x2 : X}
    (hx : x1 = x2)
    {m1 : PolyCofix P x1} {m2 : PolyCofix P x2}
    (hm : HEq m1 m2) (n : Nat) :
    HEq (m1.approx n) (m2.approx n) := by
  subst hx
  rw [eq_of_heq hm]

/--
Two PolyCofix values are HEq if their fibers are equal and all approximations are HEq.
-/
lemma PolyCofix.heq_of_approx_heq {P : PolyEndo X} {x1 x2 : X}
    (hx : x1 = x2)
    {m1 : PolyCofix P x1} {m2 : PolyCofix P x2}
    (happrox : ∀ n, HEq (m1.approx n) (m2.approx n)) :
    HEq m1 m2 := by
  subst hx
  apply heq_of_eq
  apply PolyCofix.ext
  intro n
  exact eq_of_heq (happrox n)

end PolyCofix

/-! ### PolyCofix as Coalgebra Carrier -/

section PolyCofixCoalg

variable {X : Type u}

/--
The carrier of the terminal coalgebra: `PolyCofix P` viewed as an object of `Over X`.
-/
def polyCofixCarrier (P : PolyEndo X) : Over X :=
  (familySliceForward X).obj (PolyCofix P)

/--
Build a morphism from the family at index `i` to `polyCofixCarrier P` from
a function that assigns a cofixed point to each fiber element.
-/
def polyCofixChildrenMor {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (children : ∀ (e : (polyBetweenFamily X X P x i).left),
      PolyCofix P ((polyBetweenFamily X X P x i).hom e)) :
    polyBetweenFamily X X P x i ⟶ polyCofixCarrier P :=
  Over.homMk
    (fun e => ⟨(polyBetweenFamily X X P x i).hom e, children e⟩)
    rfl

/--
Evaluating `polyCofixChildrenMor` at a point gives the corresponding child.
-/
lemma polyCofixChildrenMor_snd {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (children : ∀ (e : (polyBetweenFamily X X P x i).left),
      PolyCofix P ((polyBetweenFamily X X P x i).hom e))
    (e : (polyBetweenFamily X X P x i).left) :
    ((polyCofixChildrenMor i children).left e).snd = children e := rfl

/--
The destructor for `PolyCofix`: extracts the head and children as an element of `P(PolyCofix P)`.

For a cofixed point element `m`, this returns:
- The index `m.head`
- A morphism from the corresponding family to `polyCofixCarrier P` via `m.children`
-/
def polyCofixDestFamily (P : PolyEndo X) (x : X) (m : PolyCofix P x) :
    polyBetweenEvalFamily X X P (polyCofixCarrier P) x :=
  ⟨m.head, polyCofixChildrenMor m.head m.children⟩

/--
The underlying function of the destructor.
-/
def polyCofixDestLeft (P : PolyEndo X) :
    (polyCofixCarrier P).left → ((polyEndoFunctor X P).obj (polyCofixCarrier P)).left :=
  fun ⟨x, m⟩ => ⟨x, polyCofixDestFamily P x m⟩

/--
The destructor commutes with projections to X.
-/
lemma polyCofixDest_comm (P : PolyEndo X) :
    polyCofixDestLeft P ≫ ((polyEndoFunctor X P).obj (polyCofixCarrier P)).hom =
    (polyCofixCarrier P).hom := rfl

/--
The destructor for the terminal coalgebra.
-/
def polyCofixDest (P : PolyEndo X) :
    polyCofixCarrier P ⟶ (polyEndoFunctor X P).obj (polyCofixCarrier P) :=
  Over.homMk (polyCofixDestLeft P) (polyCofixDest_comm P)

end PolyCofixCoalg

/-! ### Constructor for PolyCofix -/

section PolyCofixMk

variable {X : Type u}

/--
Extract a child cofixed point from a morphism to `polyCofixCarrier P`.
-/
def polyCofixChildAt {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyCofixCarrier P)
    (e : (polyBetweenFamily X X P x i).left) :
    PolyCofix P ((polyBetweenFamily X X P x i).hom e) :=
  let result := h.left e
  have heq : result.1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  heq ▸ result.2

/--
Build approximation at depth 0 for the constructor.
-/
def polyCofixMkApprox_zero (P : PolyEndo X) (x : X)
    (_elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) :
    PolyCofixApprox P 0 x :=
  .continue x

/--
Build approximation at depth n+1 for the constructor.
-/
def polyCofixMkApprox_succ (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) (n : Nat) :
    PolyCofixApprox P (n + 1) x :=
  .intro x elem.1 (fun e => (polyCofixChildAt elem.1 elem.2 e).approx n)

/--
Build approximation at depth n for the constructor.
-/
def polyCofixMkApprox (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) (n : Nat) :
    PolyCofixApprox P n x :=
  match n with
  | 0 => polyCofixMkApprox_zero P x elem
  | n + 1 => polyCofixMkApprox_succ P x elem n

/--
The approximations built by the constructor agree at depth 0.
-/
lemma polyCofixMkApprox_consistent_zero (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) :
    PolyCofixAgree P (polyCofixMkApprox P x elem 0) (polyCofixMkApprox P x elem 1) := by
  simp only [polyCofixMkApprox, polyCofixMkApprox_zero, polyCofixMkApprox_succ]
  exact .continue _ _

/--
The approximations built by the constructor agree at successor depth.
-/
lemma polyCofixMkApprox_consistent_succ (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) (n : Nat) :
    PolyCofixAgree P
      (polyCofixMkApprox P x elem (n + 1))
      (polyCofixMkApprox P x elem (n + 2)) := by
  simp only [polyCofixMkApprox, polyCofixMkApprox_succ]
  apply PolyCofixAgree.intro
  intro e
  exact (polyCofixChildAt elem.1 elem.2 e).consistent n

/--
The approximations built by the constructor form a consistent sequence.
-/
lemma polyCofixMkApprox_consistent (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) (n : Nat) :
    PolyCofixAgree P (polyCofixMkApprox P x elem n) (polyCofixMkApprox P x elem (n + 1)) :=
  match n with
  | 0 => polyCofixMkApprox_consistent_zero P x elem
  | n + 1 => polyCofixMkApprox_consistent_succ P x elem n

/--
The constructor for `PolyCofix`: builds a cofixed point from an element of `P(PolyCofix P)`.

This is the inverse of `polyCofixDest`.
-/
def polyCofixMkFamily (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) : PolyCofix P x where
  approx := polyCofixMkApprox P x elem
  consistent := polyCofixMkApprox_consistent P x elem

@[simp]
lemma polyCofixMkFamily_head (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) :
    (polyCofixMkFamily P x elem).head = elem.1 := rfl

@[simp]
lemma polyCofixMkFamily_approx (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x) (n : ℕ) :
    (polyCofixMkFamily P x elem).approx n = polyCofixMkApprox P x elem n := rfl

/--
The underlying function of the constructor.
-/
def polyCofixMkLeft (P : PolyEndo X) :
    ((polyEndoFunctor X P).obj (polyCofixCarrier P)).left → (polyCofixCarrier P).left :=
  fun ⟨x, elem⟩ => ⟨x, polyCofixMkFamily P x elem⟩

/--
The constructor commutes with projections to X.
-/
lemma polyCofixMk_comm (P : PolyEndo X) :
    polyCofixMkLeft P ≫ (polyCofixCarrier P).hom =
    ((polyEndoFunctor X P).obj (polyCofixCarrier P)).hom := rfl

/--
The constructor for the terminal coalgebra.
-/
def polyCofixMk (P : PolyEndo X) :
    (polyEndoFunctor X P).obj (polyCofixCarrier P) ⟶ polyCofixCarrier P :=
  Over.homMk (polyCofixMkLeft P) (polyCofixMk_comm P)

end PolyCofixMk

/-! ### Terminal Coalgebra Structure -/

section PolyCofixTerminal

variable {X : Type u}

/--
The terminal coalgebra of a polynomial endofunctor.

The carrier is `polyCofixCarrier P` (the M-type) and the structure map is
`polyCofixDest P` (the destructor).
-/
def polyCofixCoalg (P : PolyEndo X) : PolyCoalg P where
  V := polyCofixCarrier P
  str := polyCofixDest P

/-! ### Anamorphism (Unfold) -/

/--
Build the approximation at depth n for the anamorphism from a coalgebra element.

This is the cofree construction: at each depth, we apply the coalgebra structure
map to get the index and children, then recursively build approximations for
the children.
-/
def polyCofixUnfoldApprox (P : PolyEndo X) (α : PolyCoalg P) (n : Nat) (x : X)
    (a : {y : α.V.left // α.V.hom y = x}) : PolyCofixApprox P n x :=
  match n with
  | 0 => .continue x
  | n + 1 =>
    let strResult := α.str.left a.val
    have hx : strResult.1 = x := by
      have h := congrFun (Over.w α.str) a.val
      simp only at h
      rw [a.property] at h
      exact h
    let elem : polyBetweenEvalFamily X X P α.V strResult.1 := strResult.2
    let childMor := elem.2
    hx ▸ .intro strResult.1 elem.1 (fun e =>
      let childVal := childMor.left e
      have hChild : α.V.hom childVal =
          (polyBetweenFamily X X P strResult.1 elem.1).hom e :=
        congrFun (Over.w childMor) e
      polyCofixUnfoldApprox P α n _ ⟨childVal, hChild⟩)

/--
Agreement is preserved under transport by equal indices.
-/
lemma PolyCofixAgree.transport {P : PolyEndo X} {n : Nat} {x y : X}
    {a : PolyCofixApprox P n x} {b : PolyCofixApprox P (n + 1) x}
    (h : PolyCofixAgree P a b) (heq : x = y) :
    PolyCofixAgree P (heq ▸ a) (heq ▸ b) := by
  subst heq
  exact h

/--
The approximations built by the anamorphism agree at successive depths.
-/
lemma polyCofixUnfoldApprox_consistent (P : PolyEndo X) (α : PolyCoalg P) (n : Nat)
    (x : X) (a : {y : α.V.left // α.V.hom y = x}) :
    PolyCofixAgree P
      (polyCofixUnfoldApprox P α n x a)
      (polyCofixUnfoldApprox P α (n + 1) x a) := by
  match n with
  | 0 =>
    simp only [polyCofixUnfoldApprox]
    exact .continue _ _
  | n + 1 =>
    simp only [polyCofixUnfoldApprox]
    apply PolyCofixAgree.transport
    apply PolyCofixAgree.intro
    intro e
    exact polyCofixUnfoldApprox_consistent P α n _ _

/--
`polyCofixUnfoldApprox` is proof-independent: it depends only on the underlying
element, not on the specific proof of fiber membership.
-/
lemma polyCofixUnfoldApprox_proof_irrel (P : PolyEndo X) (α : PolyCoalg P) (n : Nat)
    (x : X) (a : α.V.left) (h1 h2 : α.V.hom a = x) :
    polyCofixUnfoldApprox P α n x ⟨a, h1⟩ = polyCofixUnfoldApprox P α n x ⟨a, h2⟩ := by
  congr 1

/--
`polyCofixUnfoldApprox` result can be transported between equal fiber proofs.
-/
lemma polyCofixUnfoldApprox_cast (P : PolyEndo X) (α : PolyCoalg P) (n : Nat)
    (x y : X) (a : α.V.left) (hx : α.V.hom a = x) (hxy : x = y) :
    hxy ▸ polyCofixUnfoldApprox P α n x ⟨a, hx⟩ =
      polyCofixUnfoldApprox P α n y ⟨a, hxy ▸ hx⟩ := by
  subst hxy
  rfl

/--
The anamorphism from a coalgebra to the terminal coalgebra, at a fiber element.

Given a coalgebra element at fiber x, this produces a cofixed point at x
by iteratively unfolding using the coalgebra structure map.
-/
def polyCofixUnfoldAt (P : PolyEndo X) (α : PolyCoalg P) (x : X)
    (a : {y : α.V.left // α.V.hom y = x}) : PolyCofix P x where
  approx n := polyCofixUnfoldApprox P α n x a
  consistent n := polyCofixUnfoldApprox_consistent P α n x a

/--
The underlying function of the anamorphism.
-/
def polyCofixUnfoldLeft (P : PolyEndo X) (α : PolyCoalg P) :
    α.V.left → (polyCofixCarrier P).left :=
  fun a => ⟨α.V.hom a, polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩⟩

/--
The anamorphism commutes with projections to X.
-/
lemma polyCofixUnfold_comm (P : PolyEndo X) (α : PolyCoalg P) :
    polyCofixUnfoldLeft P α ≫ (polyCofixCarrier P).hom = α.V.hom := rfl

/--
The anamorphism from a coalgebra to the terminal coalgebra.

This is the unique coalgebra homomorphism from any coalgebra to `polyCofixCoalg P`.
-/
def polyCofixUnfold (P : PolyEndo X) (α : PolyCoalg P) :
    α.V ⟶ polyCofixCarrier P :=
  Over.homMk (polyCofixUnfoldLeft P α) (polyCofixUnfold_comm P α)

/-! ### Coalgebra Homomorphism Property -/

/--
Intermediate type for the coalgebra homomorphism proof.
This is the type of elements in `(polyEndoFunctor X P).obj (polyCofixCarrier P)`.
-/
abbrev PolyEndoFunctorObjLeft (P : PolyEndo X) :=
  (Σ x : X, polyBetweenEvalFamily X X P (polyCofixCarrier P) x)

/--
The LHS of the coalgebra homomorphism at point `a`:
applying `α.str` then the functor map of `unfold`.
-/
def polyCofixUnfold_coalg_comm_lhs (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) : PolyEndoFunctorObjLeft P :=
  let strResult := α.str.left a
  ⟨strResult.1, strResult.2.1, strResult.2.2 ≫ polyCofixUnfold P α⟩

/--
The RHS of the coalgebra homomorphism at point `a`:
applying `unfold` then `dest`.
-/
def polyCofixUnfold_coalg_comm_rhs (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) : PolyEndoFunctorObjLeft P :=
  let m := polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩
  ⟨α.V.hom a, m.head, polyCofixChildrenMor m.head m.children⟩

/--
The first projection of LHS equals `(α.str.left a).1`.
-/
lemma polyCofixUnfold_coalg_comm_lhs_fst (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    (polyCofixUnfold_coalg_comm_lhs P α a).1 = (α.str.left a).1 := rfl

/--
The first projection of RHS equals `α.V.hom a`.
-/
lemma polyCofixUnfold_coalg_comm_rhs_fst (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    (polyCofixUnfold_coalg_comm_rhs P α a).1 = α.V.hom a := rfl

/--
The structure map commutes with projection: `(α.str.left a).1 = α.V.hom a`.
-/
lemma polyCofixUnfold_coalg_comm_fst_eq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) : (α.str.left a).1 = α.V.hom a :=
  congrFun (Over.w α.str) a

/--
First components of LHS and RHS are equal.
-/
lemma polyCofixUnfold_coalg_comm_fst (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    (polyCofixUnfold_coalg_comm_lhs P α a).1 =
    (polyCofixUnfold_coalg_comm_rhs P α a).1 :=
  polyCofixUnfold_coalg_comm_fst_eq P α a

/--
Index extraction from transported approximation.
-/
lemma PolyCofixApprox.getIndex_cast {P : PolyEndo X} {n : Nat} {x y : X}
    (i : polyBetweenIndex X X P x)
    (f : ∀ e, PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e))
    (heq : x = y) :
    (heq ▸ PolyCofixApprox.intro x i f).getIndex = heq ▸ i := by
  subst heq
  rfl

/--
The head of `polyCofixUnfoldAt` equals the transported index from the structure map.
-/
lemma polyCofixUnfoldAt_head_eq (P : PolyEndo X) (α : PolyCoalg P) (x : X)
    (a : {y : α.V.left // α.V.hom y = x}) :
    (polyCofixUnfoldAt P α x a).head =
    let hx : (α.str.left a.val).1 = x := by
      have h := congrFun (Over.w α.str) a.val
      simp only at h
      rw [a.property] at h
      exact h
    hx ▸ (α.str.left a.val).2.1 := by
  simp only [PolyCofix.head, polyCofixUnfoldAt]
  simp only [polyCofixUnfoldApprox]
  exact PolyCofixApprox.getIndex_cast _ _ _

/--
Specialized version: head of `polyCofixUnfoldAt` at `(α.V.hom a)` with `⟨a, rfl⟩`.
-/
lemma polyCofixUnfoldAt_head_rfl (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    (polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩).head =
    (polyCofixUnfold_coalg_comm_fst_eq P α a) ▸ (α.str.left a).2.1 := by
  rw [polyCofixUnfoldAt_head_eq]

/--
Helper: when two indices in different fibers are related by transport, and
morphisms from those indices agree appropriately, the full sigma types are HEq.
-/
lemma polyBetweenEvalFamily_heq {P : PolyEndo X} {x y : X}
    (heq : x = y)
    (i : polyBetweenIndex X X P x)
    (mor : polyBetweenFamily X X P x i ⟶ polyCofixCarrier P)
    (j : polyBetweenIndex X X P y)
    (mor' : polyBetweenFamily X X P y j ⟶ polyCofixCarrier P)
    (hi : HEq i j)
    (hmor : HEq mor mor') :
    HEq (⟨i, mor⟩ : polyBetweenEvalFamily X X P (polyCofixCarrier P) x)
        (⟨j, mor'⟩ : polyBetweenEvalFamily X X P (polyCofixCarrier P) y) := by
  subst heq
  simp only [heq_eq_eq] at hi hmor
  subst hi hmor
  rfl

/--
General lemma: `x` is heterogeneously equal to its transport by any equality proof.
-/
lemma heq_eqRec {α : Type*} {a b : α} {motive : α → Sort*}
    (h : a = b) (x : motive a) : HEq x (h ▸ x) := by
  subst h
  rfl

/--
The index component of the anamorphism commutation.

The structure map index `(α.str.left a).2.1` is HEq to the head of the unfolded
M-type. We prove this by showing both equal a common transported value.
-/
lemma polyCofixUnfold_coalg_comm_index_heq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    HEq (α.str.left a).2.1
        (polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩).head := by
  have hfst : (α.str.left a).1 = α.V.hom a := polyCofixUnfold_coalg_comm_fst_eq P α a
  have hhead := polyCofixUnfoldAt_head_rfl P α a
  have step1 : HEq (α.str.left a).2.1 (hfst ▸ (α.str.left a).2.1) :=
    heq_eqRec (motive := fun x => polyBetweenIndex X X P x) hfst (α.str.left a).2.1
  have step2 : hfst ▸ (α.str.left a).2.1 =
      (polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩).head := hhead.symm
  exact step1.trans (heq_of_eq step2)

/--
Two morphisms with HEq source/target are HEq when their left components are equal.
-/
lemma polyBetweenFamily_mor_heq {P : PolyEndo X} {x y : X} {C : Over X}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (j : polyBetweenIndex X X P y)
    (hi : HEq i j)
    (f : polyBetweenFamily X X P x i ⟶ C)
    (g : polyBetweenFamily X X P y j ⟶ C)
    (hfg : HEq f.left g.left) :
    HEq f g := by
  subst hxy
  simp only [heq_eq_eq] at hi
  subst hi
  simp only [heq_eq_eq] at hfg
  exact heq_of_eq (Over.OverMorphism.ext hfg)

/--
HEq of polyBetweenFamily when base and index are related by equality/HEq.
-/
lemma polyBetweenFamily_heq {P : PolyEndo X} {x y : X}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (j : polyBetweenIndex X X P y)
    (hij : HEq i j) :
    HEq (polyBetweenFamily X X P x i) (polyBetweenFamily X X P y j) := by
  subst hxy
  simp only [heq_eq_eq] at hij
  subst hij
  rfl

/--
HEq of left types of polyBetweenFamily when indices are HEq.
-/
lemma polyBetweenFamily_left_heq {P : PolyEndo X} {x y : X}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (j : polyBetweenIndex X X P y)
    (hij : HEq i j) :
    HEq (polyBetweenFamily X X P x i).left (polyBetweenFamily X X P y j).left := by
  have h := polyBetweenFamily_heq hxy i j hij
  have heq : polyBetweenFamily X X P x i = polyBetweenFamily X X P y j := eq_of_heq h
  rw [heq]

/--
Equality of polyBetweenFamily hom applications when bases are equal and indices/elements are HEq.
-/
lemma polyBetweenFamily_hom_eq_of_heq {P : PolyEndo X} {x y : X}
    (hxy : x = y)
    (i : polyBetweenIndex X X P x)
    (j : polyBetweenIndex X X P y)
    (hij : i ≍ j)
    (e1 : (polyBetweenFamily X X P x i).left)
    (e2 : (polyBetweenFamily X X P y j).left)
    (he : e1 ≍ e2) :
    (polyBetweenFamily X X P x i).hom e1 =
    (polyBetweenFamily X X P y j).hom e2 := by
  subst hxy
  have hij_eq : i = j := eq_of_heq hij
  subst hij_eq
  have he_eq : e1 = e2 := eq_of_heq he
  subst he_eq
  rfl

/--
Functions with equal domains and codomains are HEq when values at corresponding inputs are HEq.
-/
lemma funext_heq {α β : Type u} {γ δ : Type u}
    (hαβ : α = β) (hγδ : γ = δ)
    (f : α → γ) (g : β → δ)
    (h : ∀ (a : α) (b : β), HEq a b → HEq (f a) (g b)) :
    HEq f g := by
  subst hαβ hγδ
  apply heq_of_eq
  funext x
  have := h x x HEq.rfl
  simp only [heq_eq_eq] at this
  exact this

/--
Dependent functions with equal domains and pointwise HEq return types are HEq
when values at corresponding inputs are HEq.
-/
lemma funext_heq_dep {α β : Type u}
    {γ : α → Type u} {δ : β → Type u}
    (hαβ : α = β)
    (hγδ : ∀ (a : α) (b : β), HEq a b → γ a = δ b)
    (f : (a : α) → γ a) (g : (b : β) → δ b)
    (h : ∀ (a : α) (b : β), HEq a b → HEq (f a) (g b)) :
    HEq f g := by
  subst hαβ
  have hγδ' : γ = δ := funext (fun x => hγδ x x HEq.rfl)
  subst hγδ'
  apply heq_of_eq
  funext x
  have hx := h x x HEq.rfl
  simp only [heq_eq_eq] at hx
  exact hx

/--
The fiber values match when applying the child morphism.

This shows that `α.V.hom` applied to a child element equals the family's hom.
-/
lemma polyCofixUnfold_child_fiber_eq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left)
    (e1 : (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).left) :
    α.V.hom ((α.str.left a).snd.snd.left e1) =
      (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).hom e1 :=
  congrFun (Over.w (α.str.left a).snd.snd) e1

/--
Helper: if two Over Type objects are equal and elements are HEq, then their hom values are equal.
-/
lemma overType_hom_heq {X : Type u} {f g : Over X}
    (hfg : f = g)
    (e1 : f.left) (e2 : g.left) (he : HEq e1 e2) :
    f.hom e1 = g.hom e2 := by
  cases hfg
  simp only [heq_eq_eq] at he
  rw [he]

/--
The fiber equality for comparing LHS and RHS of the coalgebra commutation at children.
-/
lemma polyCofixUnfold_coalg_comm_child_fst_eq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    let _hfst := polyCofixUnfold_coalg_comm_fst_eq P α a
    let m := polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩
    let _hindexHeq := polyCofixUnfold_coalg_comm_index_heq P α a
    ∀ (e1 : (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).left)
      (e2 : (polyBetweenFamily X X P (α.V.hom a) m.head).left)
      (_he : HEq e1 e2),
    α.V.hom ((α.str.left a).snd.snd.left e1) =
      (polyBetweenFamily X X P (α.V.hom a) m.head).hom e2 := by
  intro hfst m hindexHeq e1 e2 he
  have step1 := polyCofixUnfold_child_fiber_eq P α a e1
  have hfamilyHeq := polyBetweenFamily_heq hfst _ _ hindexHeq
  have hfamilyEq : polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst =
      polyBetweenFamily X X P (α.V.hom a) m.head := eq_of_heq hfamilyHeq
  rw [step1]
  exact overType_hom_heq hfamilyEq e1 e2 he

lemma polyCofixUnfold_coalg_comm_mor_heq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    HEq ((α.str.left a).2.2 ≫ polyCofixUnfold P α)
        (polyCofixChildrenMor
          (polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩).head
          (polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩).children) := by
  have hfst : (α.str.left a).1 = α.V.hom a := polyCofixUnfold_coalg_comm_fst_eq P α a
  have hindexHeq := polyCofixUnfold_coalg_comm_index_heq P α a
  have hhead := polyCofixUnfoldAt_head_rfl P α a
  apply polyBetweenFamily_mor_heq hfst _ _ hindexHeq
  simp only [Over.comp_left, polyCofixUnfold, Over.homMk_left]
  simp only [polyCofixChildrenMor, Over.homMk_left]
  have hdomHeq := polyBetweenFamily_left_heq hfst _ _ hindexHeq
  apply funext_heq (eq_of_heq hdomHeq) rfl
  intro e1 e2 he
  simp only [types_comp_apply, polyCofixUnfoldLeft]
  apply heq_of_eq
  rw [Sigma.mk.inj_iff]
  constructor
  · exact polyCofixUnfold_coalg_comm_child_fst_eq P α a e1 e2 he
  · have hfst_eq := polyCofixUnfold_coalg_comm_child_fst_eq P α a e1 e2 he
    let parent := polyCofixUnfoldAt P α (α.V.hom a) ⟨a, rfl⟩
    let child1 := polyCofixUnfoldAt P α
      (α.V.hom ((α.str.left a).snd.snd.left e1))
      ⟨(α.str.left a).snd.snd.left e1, rfl⟩
    let child2 := parent.children e2
    have hfiber1 : α.V.hom ((α.str.left a).snd.snd.left e1) =
        (polyBetweenFamily X X P (α.V.hom a) parent.head).hom e2 := hfst_eq
    have step1 : HEq child1 (hfiber1 ▸ child1) := heq_eqRec hfiber1 child1
    have step2 : hfiber1 ▸ child1 = child2 := by
      apply PolyCofix.ext
      intro n
      show (hfiber1 ▸ child1).approx n = child2.approx n
      cases n with
      | zero =>
        rw [PolyCofix.approx_cast hfiber1 child1 0]
        have h1 : child1.approx 0 = PolyCofixApprox.continue _ := rfl
        have h2 : child2.approx 0 = PolyCofixApprox.continue _ := rfl
        rw [h1, h2]
        exact PolyCofixApprox.continue_cast hfiber1
      | succ n =>
        rw [PolyCofix.approx_cast hfiber1 child1 (n + 1)]
        have h1 : child1.approx (n + 1) =
            polyCofixUnfoldApprox P α (n + 1) _ ⟨(α.str.left a).snd.snd.left e1, rfl⟩ := rfl
        have h2 : child2.approx (n + 1) = parent.childApproxAt e2 (n + 1) := rfl
        rw [h1, h2]
        simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_succ]
        let strResult := α.str.left a
        let childMor := strResult.2.2
        let hx : strResult.1 = α.V.hom a := hfst
        let childrenFun : ∀ (e : (polyBetweenFamily X X P strResult.1 strResult.2.1).left),
            PolyCofixApprox P (n + 1) ((polyBetweenFamily X X P strResult.1 strResult.2.1).hom e) :=
          fun e =>
            let childVal := childMor.left e
            let hChild : α.V.hom childVal =
                (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e :=
              congrFun (Over.w childMor) e
            polyCofixUnfoldApprox P α (n + 1) _ ⟨childVal, hChild⟩
        have happrox_form : parent.approx (n + 2) =
            hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun := rfl
        have hidx_eq : (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun).getIndex
            = hx ▸ strResult.2.1 :=
          PolyCofixApprox.getIndex_cast strResult.2.1 childrenFun hx
        have hhead_eq : parent.head = hx ▸ strResult.2.1 := hhead
        have hidx_eq' : (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun).getIndex
            = hx ▸ strResult.2.1 := hidx_eq
        have hfamilyEq2 : polyBetweenFamily X X P (α.V.hom a) parent.head =
            polyBetweenFamily X X P (α.V.hom a) (hx ▸ strResult.2.1) := by
          rw [hhead_eq]
        let e2' : (polyBetweenFamily X X P (α.V.hom a) (hx ▸ strResult.2.1)).left :=
          hfamilyEq2 ▸ e2
        have he2_heq : HEq e2 e2' := heq_eqRec hfamilyEq2 e2
        have hfamilyEq1 : polyBetweenFamily X X P strResult.1 strResult.2.1 =
            polyBetweenFamily X X P (α.V.hom a) (hx ▸ strResult.2.1) := by
          have hfamilyHeq := polyBetweenFamily_heq hx _ _
            (heq_eqRec (motive := fun y => polyBetweenIndex X X P y) hx strResult.2.1)
          exact eq_of_heq hfamilyHeq
        have he1e2' : HEq e1 e2' := he.trans he2_heq
        have hfib' : (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e1 =
            (polyBetweenFamily X X P (α.V.hom a) (hx ▸ strResult.2.1)).hom e2' :=
          overType_hom_heq hfamilyEq1 e1 e2' he1e2'
        have hcastResult : PolyCofix.childApproxAt_succ_aux (hx ▸ strResult.2.1)
            (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun) hidx_eq' e2' =
            hfib' ▸ childrenFun e1 :=
          PolyCofix.childApproxAt_succ_aux_cast hx strResult.2.1 childrenFun hidx_eq' e2' e1
            he1e2' hfib'
        have hRhsFib : (polyBetweenFamily X X P (α.V.hom a) parent.head).hom e2 =
            (polyBetweenFamily X X P (α.V.hom a) (hx ▸ strResult.2.1)).hom e2' :=
          overType_hom_heq hfamilyEq2 e2 e2' he2_heq
        have hRhsChildApprox_heq : HEq
            (PolyCofix.childApproxAt_succ_aux parent.head (parent.approx (n + 2))
              (parent.index_eq_head (n + 1)) e2)
            (PolyCofix.childApproxAt_succ_aux (hx ▸ strResult.2.1)
              (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun)
              hidx_eq' e2') := by
          have hhead_heq : HEq parent.head (hx ▸ strResult.2.1) :=
            heq_of_eq hhead_eq
          have happrox_heq : HEq (parent.approx (n + 2))
              (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun) :=
            heq_of_eq happrox_form
          exact PolyCofix.childApproxAt_succ_aux_heq rfl _ _ hhead_heq _ _ happrox_heq _ _
            _ _ he2_heq
        let rhs' := PolyCofix.childApproxAt_succ_aux (hx ▸ strResult.2.1)
              (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun) hidx_eq' e2'
        have hRhs'_heq : HEq rhs' (hRhsFib.symm ▸ rhs') := heq_eqRec hRhsFib.symm rhs'
        have hRhsForm : PolyCofix.childApproxAt_succ_aux parent.head (parent.approx (n + 2))
            (parent.index_eq_head (n + 1)) e2 =
            hRhsFib.symm ▸ PolyCofix.childApproxAt_succ_aux (hx ▸ strResult.2.1)
              (hx ▸ PolyCofixApprox.intro strResult.1 strResult.2.1 childrenFun)
              hidx_eq' e2' := by
          apply eq_of_heq
          exact hRhsChildApprox_heq.trans hRhs'_heq
        rw [hRhsForm, hcastResult]
        let hChildProof : α.V.hom (childMor.left e1) =
            (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e1 :=
          congrFun (Over.w childMor) e1
        have hChildrenFunEq : childrenFun e1 =
            hChildProof ▸ polyCofixUnfoldApprox P α (n + 1) (α.V.hom (childMor.left e1))
              ⟨childMor.left e1, rfl⟩ := by
          simp only [childrenFun]
          have hCast := polyCofixUnfoldApprox_cast P α (n + 1) (α.V.hom (childMor.left e1))
            ((polyBetweenFamily X X P strResult.1 strResult.2.1).hom e1) (childMor.left e1)
            rfl hChildProof
          rw [hCast]
        rw [hChildrenFunEq]
        apply eq_of_heq
        let lhsVal := polyCofixUnfoldApprox P α (n + 1) (α.V.hom (childMor.left e1))
              ⟨childMor.left e1, rfl⟩
        have hLhsHeq : HEq (hfiber1 ▸ lhsVal) lhsVal := (heq_eqRec hfiber1 lhsVal).symm
        have hRhsHeq : HEq (hRhsFib.symm ▸ (hfib' ▸ (hChildProof ▸ lhsVal))) lhsVal := by
          have h1 : HEq (hChildProof ▸ lhsVal) lhsVal := (heq_eqRec hChildProof lhsVal).symm
          have h2 : HEq (hfib' ▸ (hChildProof ▸ lhsVal)) lhsVal :=
            HEq.trans (heq_eqRec hfib' _).symm h1
          exact HEq.trans (heq_eqRec hRhsFib.symm _).symm h2
        exact hLhsHeq.trans hRhsHeq.symm
    exact step1.trans (heq_of_eq step2)

/--
Second component (the index and morphism pair) of LHS and RHS are heterogeneously equal.

The strategy: we show both sides represent the same data after accounting for
the fiber transport. The LHS index is `(α.str.left a).2.1` in fiber
`(α.str.left a).1`, while the RHS index is the transported version in fiber
`α.V.hom a`.
-/
lemma polyCofixUnfold_coalg_comm_snd (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    HEq (polyCofixUnfold_coalg_comm_lhs P α a).2
        (polyCofixUnfold_coalg_comm_rhs P α a).2 := by
  simp only [polyCofixUnfold_coalg_comm_lhs, polyCofixUnfold_coalg_comm_rhs]
  have hfst : (α.str.left a).1 = α.V.hom a := polyCofixUnfold_coalg_comm_fst_eq P α a
  apply polyBetweenEvalFamily_heq hfst
  · exact polyCofixUnfold_coalg_comm_index_heq P α a
  · exact polyCofixUnfold_coalg_comm_mor_heq P α a

/--
LHS equals RHS.
-/
lemma polyCofixUnfold_coalg_comm_eq (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    polyCofixUnfold_coalg_comm_lhs P α a = polyCofixUnfold_coalg_comm_rhs P α a :=
  Sigma.ext_iff.mpr ⟨polyCofixUnfold_coalg_comm_fst P α a,
    polyCofixUnfold_coalg_comm_snd P α a⟩

lemma polyCofixUnfold_coalg_comm (P : PolyEndo X) (α : PolyCoalg P) :
    α.str ≫ (polyEndoFunctor X P).map (polyCofixUnfold P α) =
    polyCofixUnfold P α ≫ polyCofixDest P := by
  apply Over.OverMorphism.ext
  funext a
  simp only [types_comp_apply, Over.comp_left]
  simp only [polyCofixUnfold, polyCofixUnfoldLeft, Over.homMk_left]
  simp only [polyCofixDest, polyCofixDestLeft, polyCofixDestFamily, Over.homMk_left]
  simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left]
  exact polyCofixUnfold_coalg_comm_eq P α a

/--
The anamorphism as a coalgebra homomorphism.
-/
def polyCofixUnfoldHom (P : PolyEndo X) (α : PolyCoalg P) :
    α ⟶ polyCofixCoalg P :=
  Endofunctor.Coalgebra.Hom.mk
    (polyCofixUnfold P α)
    (polyCofixUnfold_coalg_comm P α)

/-! ### Uniqueness -/

/--
The coalgebra homomorphism property evaluated at a point.

For any coalgebra homomorphism `f : α ⟶ polyCofixCoalg P` and element `a`,
applying the functor map to `α.str(a)` equals the destruct of `f(a)`.
-/
lemma coalg_hom_at (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left) :
    ((polyEndoFunctor X P).map f.f).left (α.str.left a) =
    (polyCofixDest P).left (f.f.left a) := by
  have hComm := f.h
  have hCommAt := congrFun (congrArg (·.left) hComm) a
  simp only [types_comp_apply, Over.comp_left] at hCommAt
  exact hCommAt

/--
The fiber of the homomorphism output matches the coalgebra structure fiber.
-/
lemma coalg_hom_fiber_eq (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left) :
    (f.f.left a).fst = (α.str.left a).fst := by
  have h := coalg_hom_at P α f a
  simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left] at h
  simp only [polyCofixDest, polyCofixDestLeft, polyCofixDestFamily,
    Over.homMk_left] at h
  exact (congrArg (·.fst) h).symm

/--
Step 1 for coalg_hom_index_heq: Normalize the homomorphism equation to expose
the sigma structure on both sides.
-/
lemma coalg_hom_at_normalized (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left) :
    (⟨(α.str.left a).fst,
      ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩⟩ :
      Σ y : X, Σ i : ccrIndex (P y), ccrFamily (P y) i ⟶ polyCofixCarrier P) =
    ⟨(f.f.left a).fst,
      ⟨(f.f.left a).snd.head,
        polyCofixChildrenMor (f.f.left a).snd.head (f.f.left a).snd.children⟩⟩ := by
  have h := coalg_hom_at P α f a
  simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left] at h
  simp only [polyCofixDest, polyCofixDestLeft, polyCofixDestFamily,
    Over.homMk_left] at h
  exact h

/--
Step 2 for coalg_hom_index_heq: From the normalized equation, extract the HEq
of indices after accounting for fiber equality.
-/
lemma coalg_hom_index_heq_from_normalized (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left)
    (h : (⟨(α.str.left a).fst,
      ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩⟩ :
      Σ y : X, Σ i : ccrIndex (P y), ccrFamily (P y) i ⟶ polyCofixCarrier P) =
    ⟨(f.f.left a).fst,
      ⟨(f.f.left a).snd.head,
        polyCofixChildrenMor (f.f.left a).snd.head (f.f.left a).snd.children⟩⟩) :
    HEq (f.f.left a).snd.head (α.str.left a).snd.fst := by
  rw [Sigma.ext_iff] at h
  obtain ⟨hfst', hsnd_heq⟩ := h
  simp only at hfst' hsnd_heq
  have htype : (Σ i : ccrIndex (P (α.str.left a).fst),
      ccrFamily (P (α.str.left a).fst) i ⟶ polyCofixCarrier P) =
      (Σ i : ccrIndex (P (f.f.left a).fst),
      ccrFamily (P (f.f.left a).fst) i ⟶ polyCofixCarrier P) :=
    congrArg (fun y => Σ i : ccrIndex (P y), ccrFamily (P y) i ⟶ polyCofixCarrier P) hfst'
  have hsnd_eq := eq_of_heq ((cast_heq htype _).trans hsnd_heq)
  rw [Sigma.ext_iff] at hsnd_eq
  obtain ⟨hidx, _⟩ := hsnd_eq
  have hIdxType : ccrIndex (P (α.str.left a).fst) = ccrIndex (P (f.f.left a).fst) :=
    congrArg (fun y => ccrIndex (P y)) hfst'
  have hcast_idx : (cast htype ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩).fst =
      cast hIdxType (α.str.left a).snd.fst :=
    hfst'.rec (motive := fun y h' =>
      (cast (congrArg (fun y => Σ i : ccrIndex (P y), ccrFamily (P y) i ⟶ polyCofixCarrier P) h')
        ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩).fst =
      cast (congrArg (fun y => ccrIndex (P y)) h') (α.str.left a).snd.fst) rfl
  rw [hcast_idx] at hidx
  exact (heq_of_eq hidx.symm).trans (cast_heq hIdxType _)

/--
The index (head) of the homomorphism output matches the coalgebra structure index.

The HEq version is used because the types depend on the fiber equality.
-/
lemma coalg_hom_index_heq (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left) :
    HEq (f.f.left a).snd.head (α.str.left a).snd.fst :=
  coalg_hom_index_heq_from_normalized P α f a (coalg_hom_at_normalized P α f a)

/--
The index (head) of the homomorphism output matches the coalgebra structure index.
-/
lemma coalg_hom_index_eq (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left) :
    (f.f.left a).snd.head = (coalg_hom_fiber_eq P α f a) ▸ (α.str.left a).snd.fst :=
  eq_of_heq ((coalg_hom_index_heq P α f a).trans (heq_eqRec_iff_heq.mpr HEq.rfl))

lemma cast_sigma_snd_heq {I : Type*} {F : I → Type*} {G : ∀ i, F i → Type*}
    {i j : I} (h : i = j) (s : Σ f : F i, G i f) :
    HEq s.snd (cast (congrArg (fun x => Σ f : F x, G x f) h) s).snd := by
  subst h
  rfl

lemma over_mor_left_heq {X : Type u} {A B C : Over X}
    (f : A ⟶ C) (g : B ⟶ C)
    (hAB : A = B)
    (hfg : HEq f g)
    (a : A.left) (b : B.left) (hab : HEq a b) :
    HEq (f.left a) (g.left b) := by
  subst hAB
  simp only [heq_eq_eq] at hfg hab
  rw [hfg, hab]

/--
Relate children evaluation through HEq morphisms.

Given a coalgebra morphism and the normalized form of the coalgebra hom equation,
this relates the children of the M-type result to applying the hom to children
from the coalgebra structure.
-/
lemma coalg_hom_children_heq_core (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left)
    (e1 : (polyBetweenFamily X X P (f.f.left a).fst (f.f.left a).snd.head).left)
    (e2 : (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).left)
    (he : HEq e1 e2)
    (hSigmaType : (Σ i : ccrIndex (P (α.str.left a).fst),
        ccrFamily (P (α.str.left a).fst) i ⟶ polyCofixCarrier P) =
        (Σ i : ccrIndex (P (f.f.left a).fst),
        ccrFamily (P (f.f.left a).fst) i ⟶ polyCofixCarrier P))
    (hmor_heq : HEq (cast hSigmaType
        ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩).snd
        (polyCofixChildrenMor (f.f.left a).snd.head (f.f.left a).snd.children)) :
    HEq ((f.f.left a).snd.children e1)
        (f.f.left ((α.str.left a).snd.snd.left e2)).snd := by
  have hFibEq' : (f.f.left a).fst = (α.str.left a).fst := coalg_hom_fiber_eq P α f a
  have hIdxHeq : HEq (f.f.left a).snd.head (α.str.left a).snd.fst :=
    coalg_hom_index_heq P α f a
  have hDomEq : (polyBetweenFamily X X P (f.f.left a).fst (f.f.left a).snd.head).left =
      (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).left :=
    eq_of_heq (polyBetweenFamily_left_heq hFibEq' _ _ hIdxHeq)
  have he2Cast : e2 = cast hDomEq e1 := by
    apply eq_of_heq
    exact he.symm.trans (cast_heq hDomEq e1).symm
  rw [he2Cast]
  have hLhs : (f.f.left a).snd.children e1 =
      ((polyCofixChildrenMor (f.f.left a).snd.head
        (f.f.left a).snd.children).left e1).snd := (polyCofixChildrenMor_snd _ _ e1).symm
  rw [hLhs]
  have hFamEq := polyBetweenFamily_heq hFibEq' _ _ hIdxHeq
  have hFamEq' : polyBetweenFamily X X P (f.f.left a).fst (f.f.left a).snd.head =
      polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst :=
    eq_of_heq hFamEq
  have hIdxEq : (f.f.left a).snd.head = hFibEq' ▸ (α.str.left a).snd.fst :=
    eq_of_heq (hIdxHeq.trans (heq_eqRec_iff_heq.mpr HEq.rfl))
  have hE1Cast : HEq e1 (cast hDomEq e1) := (cast_heq hDomEq e1).symm
  have hLhs2 : ((polyCofixChildrenMor (f.f.left a).snd.head
      (f.f.left a).snd.children).left e1).snd = (f.f.left a).snd.children e1 :=
    polyCofixChildrenMor_snd _ _ e1
  rw [hLhs2]
  have hCompEval : (f.f.left ((α.str.left a).snd.snd.left (cast hDomEq e1))) =
      ((α.str.left a).snd.snd ≫ f.f).left (cast hDomEq e1) := rfl
  rw [hCompEval]
  have hMorHeq2 : HEq ((α.str.left a).snd.snd ≫ f.f)
      (polyCofixChildrenMor (f.f.left a).snd.head (f.f.left a).snd.children) := by
    apply HEq.trans _ hmor_heq
    have hSigmaTypeFromFib : hSigmaType = congrArg (fun x =>
        Σ i : ccrIndex (P x), ccrFamily (P x) i ⟶ polyCofixCarrier P) hFibEq'.symm := rfl
    rw [hSigmaTypeFromFib]
    exact cast_sigma_snd_heq (F := fun x => ccrIndex (P x))
      (G := fun x i => ccrFamily (P x) i ⟶ polyCofixCarrier P)
      hFibEq'.symm ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩
  have hE1HeqCast : HEq e1 (cast hDomEq e1) := (cast_heq hDomEq e1).symm
  have hLhsChildren : (f.f.left a).snd.children e1 =
      ((polyCofixChildrenMor (f.f.left a).snd.head
        (f.f.left a).snd.children).left e1).snd :=
    (polyCofixChildrenMor_snd _ _ e1).symm
  rw [hLhsChildren]
  have hApplyHeq : HEq (((α.str.left a).snd.snd ≫ f.f).left (cast hDomEq e1))
      ((polyCofixChildrenMor (f.f.left a).snd.head
        (f.f.left a).snd.children).left e1) := by
    exact over_mor_left_heq _ _ hFamEq'.symm hMorHeq2 _ _ (cast_heq hDomEq e1)
  have hApplyEq : (((α.str.left a).snd.snd ≫ f.f).left (cast hDomEq e1)) =
      ((polyCofixChildrenMor (f.f.left a).snd.head
        (f.f.left a).snd.children).left e1) := eq_of_heq hApplyHeq
  have hSndHeq : HEq (((α.str.left a).snd.snd ≫ f.f).left (cast hDomEq e1)).snd
      ((polyCofixChildrenMor (f.f.left a).snd.head
        (f.f.left a).snd.children).left e1).snd := sigma_snd_heq_of_eq hApplyEq
  exact hSndHeq.symm

/--
The children morphism relationship for coalgebra homomorphisms.

For a coalgebra homomorphism `f`, the children of `(f.f.left a).snd` are
related to applying `f.f` to the children elements from the coalgebra structure.
-/
lemma coalg_hom_children_heq (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (a : α.V.left)
    (e1 : (polyBetweenFamily X X P (f.f.left a).fst (f.f.left a).snd.head).left)
    (e2 : (polyBetweenFamily X X P (α.str.left a).fst (α.str.left a).snd.fst).left)
    (he : HEq e1 e2) :
    HEq ((f.f.left a).snd.children e1)
        (f.f.left ((α.str.left a).snd.snd.left e2)).snd := by
  have hFibEq := coalg_hom_fiber_eq P α f a
  have hIdxHeq := coalg_hom_index_heq P α f a
  have hIdxEq : (f.f.left a).snd.head = hFibEq ▸ (α.str.left a).snd.fst :=
    eq_of_heq (hIdxHeq.trans (heq_eqRec_iff_heq.mpr HEq.rfl))
  have hNorm := coalg_hom_at_normalized P α f a
  rw [Sigma.ext_iff] at hNorm
  obtain ⟨hfst, hsnd_heq⟩ := hNorm
  simp only at hfst hsnd_heq
  have hSigmaType : (Σ i : ccrIndex (P (α.str.left a).fst),
      ccrFamily (P (α.str.left a).fst) i ⟶ polyCofixCarrier P) =
      (Σ i : ccrIndex (P (f.f.left a).fst),
      ccrFamily (P (f.f.left a).fst) i ⟶ polyCofixCarrier P) :=
    congrArg (fun y => Σ i : ccrIndex (P y), ccrFamily (P y) i ⟶ polyCofixCarrier P) hfst
  have hsnd_eq : cast hSigmaType
      ⟨(α.str.left a).snd.fst, (α.str.left a).snd.snd ≫ f.f⟩ =
      ⟨(f.f.left a).snd.head,
        polyCofixChildrenMor (f.f.left a).snd.head (f.f.left a).snd.children⟩ :=
    eq_of_heq ((cast_heq hSigmaType _).trans hsnd_heq)
  rw [Sigma.ext_iff] at hsnd_eq
  obtain ⟨_, hmor_heq⟩ := hsnd_eq
  simp only at hmor_heq
  exact coalg_hom_children_heq_core P α f a e1 e2 he hSigmaType hmor_heq

/--
The successor approximation for uniqueness proof.

This lemma relates the (n+1)-th approximation of a homomorphism output to
the corresponding `polyCofixUnfoldApprox` construction.
-/
lemma polyCofixUnfold_unique_approx_succ (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (n : Nat) (x : X) (a : {y : α.V.left // α.V.hom y = x})
    (ih : ∀ (x' : X) (a' : {y : α.V.left // α.V.hom y = x'}),
      let hfst' : (f.f.left a'.val).1 = x' := by
        have := congrFun (Over.w f.f) a'.val
        simp only at this
        rw [a'.property] at this
        exact this
      hfst' ▸ (f.f.left a'.val).2.approx n = polyCofixUnfoldApprox P α n x' a') :
    let hfst : (f.f.left a.val).1 = x := by
      have := congrFun (Over.w f.f) a.val
      simp only at this
      rw [a.property] at this
      exact this
    hfst ▸ (f.f.left a.val).2.approx (n + 1) = polyCofixUnfoldApprox P α (n + 1) x a := by
  intro hfst
  simp only [polyCofixUnfoldApprox]
  let strResult := α.str.left a.val
  have hStrFst : strResult.1 = x := by
    have h := congrFun (Over.w α.str) a.val
    simp only at h
    rw [a.property] at h
    exact h
  let mFib := (f.f.left a.val).fst
  let m := (f.f.left a.val).snd
  have hFiberEq : mFib = strResult.1 := coalg_hom_fiber_eq P α f a.val
  have hHeadHeq : HEq m.head strResult.2.1 := coalg_hom_index_heq P α f a.val
  match happ : m.approx (n + 1) with
  | .intro _ mIdx mChildren =>
    have hIdxEqHead : mIdx = m.head := by
      have h := m.index_eq_head n
      simp only [PolyCofixApprox.getIndex] at h
      rw [happ] at h
      exact h
    have hIdxHeq : HEq mIdx strResult.2.1 := hIdxEqHead ▸ hHeadHeq
    apply eq_of_heq
    let lhsPreTrans := PolyCofixApprox.intro (f.f.left a.val).fst mIdx mChildren
    let rhsPreTrans := PolyCofixApprox.intro strResult.fst strResult.snd.fst
      (fun e => polyCofixUnfoldApprox P α n
        ((polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e)
        ⟨strResult.snd.snd.left e, congrFun (Over.w strResult.snd.snd) e⟩)
    have hLhsHeq : HEq (hfst ▸ lhsPreTrans) lhsPreTrans :=
      (heq_eqRec hfst lhsPreTrans).symm
    have hRhsHeq : HEq (hStrFst ▸ rhsPreTrans) rhsPreTrans :=
      (heq_eqRec hStrFst rhsPreTrans).symm
    have hPreTransHeq : HEq lhsPreTrans rhsPreTrans := by
      have hFibEq' : (f.f.left a.val).fst = strResult.fst := hFiberEq
      have hTransport : HEq lhsPreTrans (hFibEq' ▸ lhsPreTrans) := heq_eqRec hFibEq' _
      have hTransportedEq : hFibEq' ▸ lhsPreTrans = rhsPreTrans := by
        have hIdxEq : hFibEq' ▸ mIdx = strResult.snd.fst := eq_of_heq (
          (heq_eqRec hFibEq' mIdx).symm.trans hIdxHeq)
        let rhsChildren := fun e =>
          polyCofixUnfoldApprox P α n
            ((polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e)
            ⟨strResult.snd.snd.left e, congrFun (Over.w strResult.snd.snd) e⟩
        apply PolyCofixApprox.intro_cast_heq hFibEq' mIdx strResult.snd.fst
          hIdxHeq mChildren rhsChildren
        have hFamEq : polyBetweenFamily X X P (f.f.left a.val).fst mIdx =
            polyBetweenFamily X X P strResult.fst strResult.snd.fst :=
          eq_of_heq (polyBetweenFamily_heq hFibEq' mIdx strResult.snd.fst hIdxHeq)
        have hDomEq : (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).left =
            (polyBetweenFamily X X P strResult.fst strResult.snd.fst).left :=
          congrArg (·.left) hFamEq
        have hCodomEq : ∀ (e1 : (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).left)
            (e2 : (polyBetweenFamily X X P strResult.fst strResult.snd.fst).left),
            HEq e1 e2 →
            (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).hom e1 =
            (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 := by
          intro e1 e2 he
          generalize hg1 :
            polyBetweenFamily X X P (f.f.left a.val).fst mIdx = fam1 at e1 ⊢
          generalize hg2 :
            polyBetweenFamily X X P strResult.fst strResult.snd.fst = fam2 at e2 ⊢
          have hfam : fam1 = fam2 := hg1 ▸ hg2 ▸ hFamEq
          subst hfam
          simp only [heq_eq_eq] at he
          rw [he]
        have hCodTypeEq :
            ∀ (e1 : (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).left)
              (e2 : (polyBetweenFamily X X P strResult.fst strResult.snd.fst).left),
              HEq e1 e2 →
              PolyCofixApprox P n
                ((polyBetweenFamily X X P (f.f.left a.val).fst mIdx).hom e1) =
              PolyCofixApprox P n
                ((polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2) :=
          fun e1 e2 he => congrArg (PolyCofixApprox P n) (hCodomEq e1 e2 he)
        have hChildrenHeq : HEq mChildren rhsChildren := by
          apply funext_heq_dep hDomEq hCodTypeEq
          intro e1 e2 he
          have hFibEq : (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).hom e1 =
              (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 :=
            hCodomEq e1 e2 he
          let childE1 : (polyBetweenFamily X X P strResult.fst
              strResult.snd.fst).left := cast hDomEq e1
          have hChildE1Heq : HEq e1 childE1 := (cast_heq hDomEq e1).symm
          have hChildE1E2 : childE1 = e2 := by
            have he' := eq_of_heq (hChildE1Heq.symm.trans he)
            exact he'
          let childVal := strResult.snd.snd.left e2
          have hChildProof : α.V.hom childVal =
              (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 :=
            congrFun (Over.w strResult.snd.snd) e2
          let childSubtype : { y // α.V.hom y =
              (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 } :=
            ⟨childVal, hChildProof⟩
          have hIhApplied := ih
            ((polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2)
            childSubtype
          have rhsUnfold : rhsChildren e2 = polyCofixUnfoldApprox P α n
              ((polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2)
              childSubtype := rfl
          rw [rhsUnfold]
          have hIhApplied' := heq_of_eq hIhApplied
          let hfst'Ih : (f.f.left childSubtype.val).fst =
              (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 := by
            have := congrFun (Over.w f.f) childSubtype.val
            simp only at this
            rw [childSubtype.property] at this
            exact this
          have hTransportTarget : HEq ((f.f.left childSubtype.val).snd.approx n)
              (hfst'Ih ▸ (f.f.left childSubtype.val).snd.approx n) :=
            heq_eqRec hfst'Ih ((f.f.left childSubtype.val).snd.approx n)
          have hCoalgChildRel : HEq (mChildren e1)
              ((f.f.left childSubtype.val).snd.approx n) := by
            have hIdxAtM : mIdx = m.head := hIdxEqHead
            have hFamAtMIdx : polyBetweenFamily X X P (f.f.left a.val).fst mIdx =
                polyBetweenFamily X X P (f.f.left a.val).fst m.head :=
              congrArg (polyBetweenFamily X X P (f.f.left a.val).fst) hIdxAtM
            let hE1AtHead : (polyBetweenFamily X X P (f.f.left a.val).fst m.head).left :=
              cast (congrArg (·.left) hFamAtMIdx) e1
            have hE1HeE2 : HEq hE1AtHead e2 :=
              (cast_heq (congrArg (·.left) hFamAtMIdx) e1).trans he
            have hCoalgChild := coalg_hom_children_heq P α f a.val hE1AtHead e2 hE1HeE2
            have hMChildApprox : HEq ((m.children hE1AtHead).approx n)
                ((f.f.left childSubtype.val).snd.approx n) := by
              have hLhsFib : (polyBetweenFamily X X P (f.f.left a.val).fst
                  m.head).hom hE1AtHead =
                  (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 := by
                have hHomEq1 : (polyBetweenFamily X X P (f.f.left a.val).fst m.head).hom
                    hE1AtHead = (polyBetweenFamily X X P (f.f.left a.val).fst mIdx).hom
                    e1 := by
                  subst hIdxAtM
                  rfl
                rw [hHomEq1]
                exact hCodomEq e1 e2 he
              have hRhsFib : (f.f.left childSubtype.val).fst =
                  (polyBetweenFamily X X P strResult.fst strResult.snd.fst).hom e2 := by
                have hOverW : (polyCofixCarrier P).hom (f.f.left childSubtype.val) =
                    α.V.hom childSubtype.val :=
                  congrFun (Over.w f.f) childSubtype.val
                have hFstEq : (polyCofixCarrier P).hom (f.f.left childSubtype.val) =
                    (f.f.left childSubtype.val).fst := rfl
                rw [← hFstEq, hOverW, childSubtype.property]
              have hFibEq : (polyBetweenFamily X X P (f.f.left a.val).fst m.head).hom
                  hE1AtHead = (f.f.left childSubtype.val).fst :=
                hLhsFib.trans hRhsFib.symm
              exact PolyCofix.approx_heq hFibEq hCoalgChild n
            have hMChildrenRel : HEq (mChildren e1)
                ((m.children hE1AtHead).approx n) := by
              subst hIdxAtM
              simp only [PolyCofix.children, PolyCofix.childApproxAt]
              cases n with
              | zero =>
                have hL : mChildren e1 = .continue _ :=
                  PolyCofixApprox.approx_zero_eq_continue _
                simp only [PolyCofix.childApproxAt_zero, hL]
                exact HEq.rfl
              | succ k =>
                simp only [PolyCofix.childApproxAt_succ]
                have heq : (m.approx (k + 2)).getIndex = m.head := m.index_eq_head (k + 1)
                rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head (m.approx (k + 2))
                  (m.index_eq_head (k + 1)) heq hE1AtHead]
                generalize ha : m.approx (k + 2) = a at happ heq
                subst happ
                rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head
                  (.intro (f.f.left ↑a).fst m.head mChildren) heq rfl hE1AtHead]
                simp only [PolyCofix.childApproxAt_succ_aux_intro]
                exact HEq.rfl
            exact hMChildrenRel.trans hMChildApprox
          exact hCoalgChildRel.trans (hTransportTarget.trans hIhApplied')
        exact hChildrenHeq
      exact hTransport.trans (heq_of_eq hTransportedEq)
    exact hLhsHeq.trans (hPreTransHeq.trans hRhsHeq.symm)

/--
Any coalgebra homomorphism to the terminal coalgebra produces the same
approximations as the anamorphism at each depth.
-/
lemma polyCofixUnfold_unique_approx (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) (n : Nat) (x : X) (a : {y : α.V.left // α.V.hom y = x}) :
    let hfst : (f.f.left a.val).1 = x := by
      have := congrFun (Over.w f.f) a.val
      simp only at this
      rw [a.property] at this
      exact this
    hfst ▸ (f.f.left a.val).2.approx n = polyCofixUnfoldApprox P α n x a := by
  intro hfst
  induction n generalizing x a with
  | zero =>
    simp only [polyCofixUnfoldApprox]
    rw [PolyCofixApprox.approx_zero_eq_continue ((f.f.left a.val).2.approx 0)]
    exact PolyCofixApprox.continue_cast hfst
  | succ n ih =>
    exact polyCofixUnfold_unique_approx_succ P α f n x a ih

/--
Uniqueness: any coalgebra homomorphism to the terminal coalgebra equals the anamorphism.
-/
lemma polyCofixUnfoldHom_unique (P : PolyEndo X) (α : PolyCoalg P)
    (f : α ⟶ polyCofixCoalg P) : f = polyCofixUnfoldHom P α := by
  apply Endofunctor.Coalgebra.Hom.ext
  apply Over.OverMorphism.ext
  funext a
  simp only [polyCofixUnfoldHom, polyCofixUnfold, polyCofixUnfoldLeft, Over.homMk_left]
  apply Sigma.ext
  · exact congrFun (Over.w f.f) a
  · have hfst : (f.f.left a).fst = α.V.hom a := congrFun (Over.w f.f) a
    have hm_heq : (f.f.left a).snd ≍ (hfst ▸ (f.f.left a).snd) := heq_eqRec hfst _
    apply hm_heq.trans
    apply heq_of_eq
    apply PolyCofix.ext
    intro n
    have := polyCofixUnfold_unique_approx P α f n (α.V.hom a) ⟨a, rfl⟩
    rw [PolyCofix.approx_cast hfst (f.f.left a).snd n]
    exact this

/-! ### Terminal Coalgebra -/

/--
The terminal coalgebra of a polynomial endofunctor.

This shows that `polyCofixCoalg P` is terminal in the category of P-coalgebras,
providing the universal property of M-types.
-/
def polyCofixCoalg_isTerminal (P : PolyEndo X) :
    CategoryTheory.Limits.IsTerminal (polyCofixCoalg P) :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (polyCofixUnfoldHom P)
    (fun α m => polyCofixUnfoldHom_unique P α m)

/-! ### Lambek's Lemma for Terminal Coalgebras -/

/--
The destructor followed by the constructor is the identity on `PolyCofix`.
-/
lemma polyCofixDest_mk (P : PolyEndo X) :
    polyCofixDest P ≫ polyCofixMk P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Over.comp_left, types_comp_apply, Over.id_left, types_id_apply,
    polyCofixDest, Over.homMk_left, polyCofixDestLeft, polyCofixMk,
    polyCofixMkLeft]
  congr 1
  apply PolyCofix.ext
  intro n
  simp only [polyCofixDestFamily, polyCofixMkFamily, polyCofixMkApprox]
  match n with
  | 0 =>
    simp only [polyCofixMkApprox_zero]
    exact (PolyCofixApprox.approx_zero_eq_continue (m.approx 0)).symm
  | n + 1 =>
    simp only [polyCofixMkApprox_succ, polyCofixChildrenMor, polyCofixChildAt,
      PolyCofix.children]
    have hhead : (m.approx (n + 1)).getIndex = m.head := m.index_eq_head n
    generalize ha : m.approx (n + 1) = a
    match a with
    | .intro _ idx children =>
      have hidx : idx = m.head := by rw [ha] at hhead; exact hhead
      subst hidx
      congr 1
      ext e
      match n with
      | 0 =>
        match children e with
        | .continue _ => rfl
      | n + 1 =>
        change m.childApproxAt e (n + 1) = children e
        simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_succ]
        conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
          m.head (m.approx (n + 2)) (m.index_eq_head (n + 1)) (by rw [ha]; rfl) e]
        simp only [ha, PolyCofix.childApproxAt_succ_aux_intro]

/--
The child extraction from a morphism composed with packaging returns the
original element for M-types.
-/
lemma polyCofixChildAt_sigma_eq {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyCofixCarrier P)
    (e : (polyBetweenFamily X X P x i).left) :
    (⟨(polyBetweenFamily X X P x i).hom e, polyCofixChildAt i h e⟩ :
      (Σ y, PolyCofix P y)) = h.left e := by
  simp only [polyCofixChildAt]
  have heq : (h.left e).1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  conv_rhs => rw [← Sigma.eta (h.left e)]
  congr 1
  · exact heq.symm
  · exact (heq_eqRec_iff_heq.mpr HEq.rfl).symm

/--
The M-type children built via polyCofixMkFamily equal the original children.
-/
lemma polyCofixMkFamily_children_eq {P : PolyEndo X} {x : X}
    (elem : polyBetweenEvalFamily X X P (polyCofixCarrier P) x)
    (e : (polyBetweenFamily X X P x elem.1).left) :
    (polyCofixMkFamily P x elem).children e = polyCofixChildAt elem.1 elem.2 e := by
  apply PolyCofix.ext
  intro n
  dsimp only [PolyCofix.children]
  match n with
  | 0 =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_zero,
      polyCofixMkFamily_head]
    simp only [polyCofixChildAt, PolyCofix.approx_cast]
    rw [PolyCofixApprox.approx_zero_eq_continue ((elem.2.left e).2.approx 0)]
    rw [PolyCofixApprox.continue_cast]
  | n + 1 =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_succ,
      polyCofixMkFamily_head, polyCofixMkFamily_approx]
    conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
      elem.fst
      (polyCofixMkApprox P x elem (n + 2))
      _ rfl e]
    simp only [polyCofixMkApprox, polyCofixMkApprox_succ,
      PolyCofix.childApproxAt_succ_aux_intro]

/--
The constructor followed by the destructor is the identity on `P(PolyCofix)`.
-/
lemma polyCofixMk_dest (P : PolyEndo X) :
    polyCofixMk P ≫ polyCofixDest P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  funext ⟨x, elem⟩
  simp only [Over.comp_left, types_comp_apply, Over.id_left, types_id_apply,
    polyCofixMk, Over.homMk_left, polyCofixMkLeft, polyCofixDest,
    polyCofixDestLeft, polyCofixDestFamily, polyCofixMkFamily,
    polyCofixMkApprox, polyCofixMkApprox_succ, PolyCofix.head,
    PolyCofixApprox.getIndex]
  congr 1
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofixChildrenMor, PolyCofix.children]
    apply Over.OverMorphism.ext
    funext e
    simp only [Over.homMk_left]
    change ⟨_, (polyCofixMkFamily P x elem).children e⟩ = elem.2.left e
    rw [polyCofixMkFamily_children_eq]
    exact polyCofixChildAt_sigma_eq elem.1 elem.2 e

/--
Lambek's Lemma for the terminal coalgebra: the structure map is an isomorphism.
-/
def polyCofixDest_iso (P : PolyEndo X) :
    polyCofixCarrier P ≅ (polyEndoFunctor X P).obj (polyCofixCarrier P) where
  hom := polyCofixDest P
  inv := polyCofixMk P
  hom_inv_id := polyCofixDest_mk P
  inv_hom_id := polyCofixMk_dest P

end PolyCofixTerminal

/-! ## Free Monad and Cofree Comonad

The free monad on a polynomial endofunctor P is defined using the initial
algebra of the "translate" functor `A + P(-)`, and the cofree comonad is
defined using the terminal coalgebra of the "scale" functor `A × P(-)`.

These constructions give adjunctions:
- Free ⊣ Forget : Alg(P) → Over X
- Forget ⊣ Cofree : Coalg(P) → Over X
-/

section FreeMonadCofreeComonad

variable {X : Type u}

/-! ### The Translate Polynomial (Coproduct)

Given `A : Over X` and `P : PolyEndo X`, the translate polynomial
`polyTranslate A P` represents the functor `Y ↦ A + P(Y)`.

At each fiber `x : X`:
- Positions: `{ a : A.left | A.hom a = x } + polyBetweenIndex P x`
- Directions at `inl a` (leaf): empty (no children)
- Directions at `inr p` (node): `polyBetweenFamily P x p`
-/

/--
The initial object in `Over X`, representing the empty family.
This is used for leaves in the free monad construction.
-/
def overEmpty (X : Type u) : Over X :=
  Over.mk (f := fun e : PEmpty => PEmpty.elim e)

/--
The index type for the translate polynomial at a fiber.
Elements are either leaves (from A) or nodes (from P).
-/
def polyTranslateIndex (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  { a : A.left // A.hom a = x } ⊕ polyBetweenIndex X X P x

/--
The family function for the translate polynomial.
Leaves have no children (empty family), nodes have children from P.
-/
def polyTranslateFamily (A : Over X) (P : PolyEndo X) (x : X)
    (i : polyTranslateIndex A P x) : Over X :=
  match i with
  | Sum.inl _ => overEmpty X
  | Sum.inr p => polyBetweenFamily X X P x p

/--
The translate polynomial at a specific fiber.
-/
def polyTranslateAt (A : Over X) (P : PolyEndo X) (x : X) :
    CoprodCovarRepCat (Over X) :=
  ccrObjMk (polyTranslateFamily A P x)

/--
The translate polynomial functor `A + P(-)` as a polynomial endofunctor.
-/
def polyTranslate (A : Over X) (P : PolyEndo X) : PolyEndo X :=
  fun x => polyTranslateAt A P x

/-! ### The Scale Polynomial (Product)

Given `A : Over X` and `P : PolyEndo X`, the scale polynomial
`polyScale A P` represents the functor `Y ↦ A × P(Y)`.

At each fiber `x : X`:
- Positions: `{ a : A.left | A.hom a = x } × polyBetweenIndex P x`
- Directions at `(a, p)`: `polyBetweenFamily P x p`
-/

/--
The index type for the scale polynomial at a fiber.
Elements are pairs of labels (from A) and nodes (from P).
-/
def polyScaleIndex (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  { a : A.left // A.hom a = x } × polyBetweenIndex X X P x

/--
The family function for the scale polynomial.
Each position has children from P (the label doesn't affect children).
-/
def polyScaleFamily (A : Over X) (P : PolyEndo X) (x : X)
    (i : polyScaleIndex A P x) : Over X :=
  polyBetweenFamily X X P x i.2

/--
The scale polynomial at a specific fiber.
-/
def polyScaleAt (A : Over X) (P : PolyEndo X) (x : X) :
    CoprodCovarRepCat (Over X) :=
  ccrObjMk (polyScaleFamily A P x)

/--
The scale polynomial functor `A × P(-)` as a polynomial endofunctor.
-/
def polyScale (A : Over X) (P : PolyEndo X) : PolyEndo X :=
  fun x => polyScaleAt A P x

/-! ### Free Monad

The free monad on P is the endofunctor `A ↦ PolyFix (polyTranslate A P)`.
This gives trees with A-labeled leaves and P-shaped internal nodes.
-/

/--
The free monad carrier: W-type of the translate polynomial.
`PolyFreeM A P x` is the type of P-branching trees with A-leaves, at fiber x.
-/
abbrev PolyFreeM (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  PolyFix (polyTranslate A P) x

/--
The free monad carrier as an object of `Over X`.
-/
def polyFreeMCarrier (A : Over X) (P : PolyEndo X) : Over X :=
  polyFixCarrier (polyTranslate A P)

/-! ### Cofree Comonad

The cofree comonad on P is the endofunctor `A ↦ PolyCofix (polyScale A P)`.
This gives M-type trees with A-annotations at each node.
-/

/--
The cofree comonad carrier: M-type of the scale polynomial.
`PolyCofreeM A P x` is the type of P-branching streams with A-annotations.
-/
abbrev PolyCofreeM (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  PolyCofix (polyScale A P) x

/--
The cofree comonad carrier as an object of `Over X`.
-/
def polyCofreeCarrier (A : Over X) (P : PolyEndo X) : Over X :=
  polyCofixCarrier (polyScale A P)

/-! ### Relating W-types and M-types to Free/Cofree

The W-type `PolyFix P` is the free monad applied to the empty object.
The M-type `PolyCofix P` is the cofree comonad applied to the terminal object.
-/

/--
The empty object in `Over X` (initial object).
-/
def overInitial (X : Type u) : Over X := overEmpty X

/--
The terminal object in `Over X` is `X` itself with the identity morphism.
-/
def overTerminal (X : Type u) : Over X :=
  Over.mk (f := @id X)

/-! ### Index Equivalences

When A is the initial object (empty), the translate polynomial index reduces
to just the P index. When A is the terminal object, the scale polynomial
index has exactly one label component per fiber.
-/

/--
The fiber of the initial object is empty (there are no elements to map).
-/
instance overInitialFiberIsEmpty (x : X) :
    IsEmpty { a : (overInitial X).left // (overInitial X).hom a = x } :=
  ⟨fun ⟨e, _⟩ => PEmpty.elim e⟩

/--
The fiber of the initial object over any x is empty.
-/
def overInitialFiberEmpty (x : X) :
    { a : (overInitial X).left // (overInitial X).hom a = x } ≃ PEmpty :=
  Equiv.equivPEmpty _

/--
The fiber of the terminal object over x is a singleton (exactly x).
-/
def overTerminalFiberUnique (x : X) :
    { a : (overTerminal X).left // (overTerminal X).hom a = x } ≃ PUnit := {
  toFun := fun _ => PUnit.unit
  invFun := fun _ => ⟨x, rfl⟩
  left_inv := fun ⟨a, h⟩ => by simp only [Subtype.mk.injEq]; exact h.symm
  right_inv := fun _ => rfl
}

/--
The translate index with initial A reduces to the P index.
-/
def polyTranslateIndexInitialEquiv (P : PolyEndo X) (x : X) :
    polyTranslateIndex (overInitial X) P x ≃ polyBetweenIndex X X P x := {
  toFun := fun i => match i with
    | Sum.inl ⟨e, _⟩ => PEmpty.elim e
    | Sum.inr p => p
  invFun := Sum.inr
  left_inv := fun i => match i with
    | Sum.inl ⟨e, _⟩ => PEmpty.elim e
    | Sum.inr _ => rfl
  right_inv := fun _ => rfl
}

/--
The scale index with terminal A has a unique label component per fiber.
-/
def polyScaleIndexTerminalEquiv (P : PolyEndo X) (x : X) :
    polyScaleIndex (overTerminal X) P x ≃
    polyBetweenIndex X X P x := {
  toFun := fun ⟨_, p⟩ => p
  invFun := fun p => ⟨⟨x, rfl⟩, p⟩
  left_inv := fun ⟨⟨a, h⟩, p⟩ => by
    apply Prod.ext
    · exact Subtype.ext h.symm
    · rfl
  right_inv := fun _ => rfl
}

/--
The translate family with initial A preserves the P family at node positions.
-/
lemma polyTranslateFamilyInitial_eq (P : PolyEndo X) (x : X)
    (p : polyBetweenIndex X X P x) :
    polyTranslateFamily (overInitial X) P x (Sum.inr p) =
    polyBetweenFamily X X P x p := rfl

/--
The scale family with terminal A preserves the P family.
-/
lemma polyScaleFamilyTerminal_eq (P : PolyEndo X) (x : X)
    (p : polyBetweenIndex X X P x) :
    polyScaleFamily (overTerminal X) P x ⟨⟨x, rfl⟩, p⟩ =
    polyBetweenFamily X X P x p := rfl

/-! ### Type Equivalences

The W-type and M-type are instances of free monad and cofree comonad
applied to initial and terminal objects respectively.
-/

/--
Convert a W-type tree to a free monad tree with empty labels.
Maps each node with index i to a node with index Sum.inr i.
-/
def polyFixToPolyFreeM (P : PolyEndo X) (x : X) :
    PolyFix P x → PolyFreeM (overInitial X) P x
  | PolyFix.mk _ i children =>
    PolyFix.mk x (Sum.inr i) (fun e => polyFixToPolyFreeM P _ (children e))

/--
Convert a free monad tree with empty labels to a W-type tree.
The Sum.inl case is impossible since the label type is empty.
-/
def polyFreeMToPolyFix (P : PolyEndo X) (x : X) :
    PolyFreeM (overInitial X) P x → PolyFix P x
  | PolyFix.mk _ i children =>
    match i with
    | Sum.inl ⟨e, _⟩ => PEmpty.elim e
    | Sum.inr p => PolyFix.mk x p (fun e => polyFreeMToPolyFix P _ (children e))

/--
Round-trip from PolyFix through PolyFreeM returns the original tree.
-/
theorem polyFreeMToPolyFix_polyFixToPolyFreeM (P : PolyEndo X) (x : X)
    (t : PolyFix P x) :
    polyFreeMToPolyFix P x (polyFixToPolyFreeM P x t) = t := by
  induction t with
  | mk y i children ih =>
    simp only [polyFixToPolyFreeM, polyFreeMToPolyFix]
    congr 1
    funext e
    exact ih e

/--
Round-trip from PolyFreeM through PolyFix returns the original tree.
-/
theorem polyFixToPolyFreeM_polyFreeMToPolyFix (P : PolyEndo X) (x : X)
    (t : PolyFreeM (overInitial X) P x) :
    polyFixToPolyFreeM P x (polyFreeMToPolyFix P x t) = t := by
  induction t with
  | mk y i children ih =>
    match i with
    | Sum.inl ⟨e, _⟩ => exact PEmpty.elim e
    | Sum.inr p =>
      simp only [polyFreeMToPolyFix, polyFixToPolyFreeM]
      congr 1
      funext e
      exact ih e

/--
The W-type `PolyFix P` is equivalent to the free monad on P applied to
the initial object. When there are no leaf labels (A is empty), trees are
just nodes with P-shaped children.
-/
def polyFixEquivPolyFreeM (P : PolyEndo X) (x : X) :
    PolyFix P x ≃ PolyFreeM (overInitial X) P x := {
  toFun := polyFixToPolyFreeM P x
  invFun := polyFreeMToPolyFix P x
  left_inv := polyFreeMToPolyFix_polyFixToPolyFreeM P x
  right_inv := polyFixToPolyFreeM_polyFreeMToPolyFix P x
}

/-! ### M-type and Cofree Comonad Equivalence

The M-type `PolyCofix P` is equivalent to the cofree comonad on P applied to
the terminal object.
-/

/--
Convert an M-type approximation to a cofree comonad approximation.
-/
def polyCofixApproxToPolyCofreeM (P : PolyEndo X) {n : Nat} {x : X} :
    PolyCofixApprox P n x →
    PolyCofixApprox (polyScale (overTerminal X) P) n x
  | PolyCofixApprox.continue y => PolyCofixApprox.continue y
  | PolyCofixApprox.intro y i children =>
    PolyCofixApprox.intro y ⟨⟨y, rfl⟩, i⟩
      (fun e => polyCofixApproxToPolyCofreeM P (children e))

/--
Convert a cofree comonad approximation to an M-type approximation.
-/
def polyCofreeApproxToPolyCofix (P : PolyEndo X) {n : Nat} {x : X} :
    PolyCofixApprox (polyScale (overTerminal X) P) n x →
    PolyCofixApprox P n x
  | PolyCofixApprox.continue y => PolyCofixApprox.continue y
  | PolyCofixApprox.intro y ⟨_, i⟩ children =>
    PolyCofixApprox.intro y i
      (fun e => polyCofreeApproxToPolyCofix P (children e))

/--
The approximation conversion preserves the agreement relation.
-/
theorem polyCofixApproxToPolyCofreeM_agree (P : PolyEndo X) {n : Nat} {x : X}
    {a : PolyCofixApprox P n x} {b : PolyCofixApprox P (n + 1) x}
    (h : PolyCofixAgree P a b) :
    PolyCofixAgree (polyScale (overTerminal X) P)
      (polyCofixApproxToPolyCofreeM P a)
      (polyCofixApproxToPolyCofreeM P b) := by
  induction h with
  | «continue» x' y' =>
    exact PolyCofixAgree.continue x' (polyCofixApproxToPolyCofreeM P y')
  | intro f f' child_agree ih' =>
    exact PolyCofixAgree.intro _ _ ih'

/--
Convert an M-type to a cofree comonad value.
-/
def polyCofixToPolyCofreeM (P : PolyEndo X) (x : X) :
    PolyCofix P x → PolyCofreeM (overTerminal X) P x := fun m => {
  approx := fun n => polyCofixApproxToPolyCofreeM P (m.approx n)
  consistent := fun n => polyCofixApproxToPolyCofreeM_agree P (m.consistent n)
}

/--
The inverse approximation conversion preserves the agreement relation.
-/
theorem polyCofreeApproxToPolyCofix_agree (P : PolyEndo X) {n : Nat} {x : X}
    {a : PolyCofixApprox (polyScale (overTerminal X) P) n x}
    {b : PolyCofixApprox (polyScale (overTerminal X) P) (n + 1) x}
    (h : PolyCofixAgree (polyScale (overTerminal X) P) a b) :
    PolyCofixAgree P
      (polyCofreeApproxToPolyCofix P a)
      (polyCofreeApproxToPolyCofix P b) := by
  induction h with
  | «continue» x' y' =>
    exact PolyCofixAgree.continue x' (polyCofreeApproxToPolyCofix P y')
  | intro f f' child_agree ih' =>
    exact PolyCofixAgree.intro _ _ ih'

/--
Convert a cofree comonad value to an M-type.
-/
def polyCofreeToPolyCofix (P : PolyEndo X) (x : X) :
    PolyCofreeM (overTerminal X) P x → PolyCofix P x := fun m => {
  approx := fun n => polyCofreeApproxToPolyCofix P (m.approx n)
  consistent := fun n => polyCofreeApproxToPolyCofix_agree P (m.consistent n)
}

/--
Round-trip from PolyCofix through PolyCofreeM returns the original at each
approximation level.
-/
theorem polyCofreeApprox_roundtrip_l (P : PolyEndo X) {n : Nat} {x : X}
    (a : PolyCofixApprox P n x) :
    polyCofreeApproxToPolyCofix P (polyCofixApproxToPolyCofreeM P a) = a := by
  induction a with
  | «continue» y => rfl
  | intro y i children ih =>
    simp only [polyCofixApproxToPolyCofreeM, polyCofreeApproxToPolyCofix]
    congr 1
    funext e
    exact ih e

/--
Round-trip from PolyCofreeM through PolyCofix returns the original at each
approximation level.
-/
theorem polyCofreeApprox_roundtrip_r (P : PolyEndo X) {n : Nat} {x : X}
    (a : PolyCofixApprox (polyScale (overTerminal X) P) n x) :
    polyCofixApproxToPolyCofreeM P (polyCofreeApproxToPolyCofix P a) = a := by
  induction a with
  | «continue» y => rfl
  | intro y idx children ih =>
    obtain ⟨⟨labelVal, labelProof⟩, pIdx⟩ := idx
    simp only [polyCofreeApproxToPolyCofix, polyCofixApproxToPolyCofreeM]
    congr 1
    · apply Prod.ext
      · exact Subtype.ext labelProof.symm
      · rfl
    · funext e
      exact ih e

/--
Round-trip from PolyCofix through PolyCofreeM returns the original.
-/
theorem polyCofix_roundtrip_l (P : PolyEndo X) (x : X) (m : PolyCofix P x) :
    polyCofreeToPolyCofix P x (polyCofixToPolyCofreeM P x m) = m := by
  apply PolyCofix.ext
  intro n
  exact polyCofreeApprox_roundtrip_l P (m.approx n)

/--
Round-trip from PolyCofreeM through PolyCofix returns the original.
-/
theorem polyCofix_roundtrip_r (P : PolyEndo X) (x : X)
    (m : PolyCofreeM (overTerminal X) P x) :
    polyCofixToPolyCofreeM P x (polyCofreeToPolyCofix P x m) = m := by
  apply PolyCofix.ext
  intro n
  exact polyCofreeApprox_roundtrip_r P (m.approx n)

/--
The M-type `PolyCofix P` is equivalent to the cofree comonad on P applied to
the terminal object. When there's exactly one label per fiber, streams are
just nodes with P-shaped children.
-/
def polyCofixEquivPolyCofreeM (P : PolyEndo X) (x : X) :
    PolyCofix P x ≃ PolyCofreeM (overTerminal X) P x := {
  toFun := polyCofixToPolyCofreeM P x
  invFun := polyCofreeToPolyCofix P x
  left_inv := polyCofix_roundtrip_l P x
  right_inv := polyCofix_roundtrip_r P x
}

/-! ### Cofree Comonad at Initial Object

The cofree comonad applied to the initial object is empty. This is because the
scale polynomial `A × P(Y)` has empty positions when A is initial, and an
M-type of a polynomial with empty positions cannot be inhabited.
-/

/--
The scale index with initial A is empty (product with empty is empty).
-/
instance polyScaleIndexInitialIsEmpty (P : PolyEndo X) (x : X) :
    IsEmpty (polyScaleIndex (overInitial X) P x) :=
  ⟨fun ⟨⟨e, _⟩, _⟩ => PEmpty.elim e⟩

/--
Approximations of cofree comonad at initial object at depth 1 or greater are
empty. This is because `PolyCofixApprox.intro` requires an index from the
polynomial, but the scale polynomial with initial A has empty index.
-/
instance polyCofreeApproxInitialIsEmpty (P : PolyEndo X) (n : Nat) (x : X) :
    IsEmpty (PolyCofixApprox (polyScale (overInitial X) P) (n + 1) x) :=
  ⟨fun a => match a with
    | PolyCofixApprox.intro _ ⟨⟨e, _⟩, _⟩ _ => PEmpty.elim e⟩

/--
The cofree comonad applied to the initial object is empty.

An M-type element requires approximations at all depths. At depth 1, we need
a `PolyCofixApprox` which must be `intro` (since `continue` is only for depth
0). But `intro` requires an index from the scale polynomial, which is empty
when A is initial. Therefore no M-type element can exist.
-/
instance polyCofreeMInitialIsEmpty (P : PolyEndo X) (x : X) :
    IsEmpty (PolyCofreeM (overInitial X) P x) :=
  ⟨fun m => IsEmpty.false (m.approx 1)⟩

/--
The cofree comonad applied to the initial object is equivalent to `PEmpty`.
-/
def polyCofreeMInitialEquivPEmpty (P : PolyEndo X) (x : X) :
    PolyCofreeM (overInitial X) P x ≃ PEmpty :=
  Equiv.equivPEmpty _

/-! ### Free Monad at Initial Algebra

The free monad applied to the initial algebra (W-type) forms a
section-retraction pair with the initial algebra. Specifically:

- `polyFixToFreeMAtFix` embeds W-types into the free monad (as internal nodes)
- `polyFreeMAtFixToPolyFix` flattens free monad trees to W-types

The composition `flatten ∘ embed = id` holds (W-type is a retract), but
`embed ∘ flatten ≠ id` in general. This is because `PolyFreeM (polyFixCarrier P)
P` has two representations of the same "logical tree":

1. A leaf containing a W-type tree `t`
2. An internal node structure mirroring `t`'s shape

Flattening both gives the same W-type, but re-embedding produces only the
internal node form (2), not the leaf form (1). Thus the free monad at the
initial algebra is strictly larger than the initial algebra itself, containing
redundant representations.

A quotient identifying leaves-containing-trees with their expanded internal
node structures would yield a true equivalence.
-/

/--
Embed a W-type tree into the free monad at the W-type carrier.
Each internal node becomes an internal node in the free monad.
-/
def polyFixToFreeMAtFix (P : PolyEndo X) {x : X} :
    PolyFix P x → PolyFreeM (polyFixCarrier P) P x
  | PolyFix.mk y i children =>
    PolyFix.mk y (Sum.inr i) fun e =>
      polyFixToFreeMAtFix P (children e)

/--
Flatten a free monad tree with W-type leaves into a W-type tree.
Leaves (containing W-type trees) are replaced with their contents.
Internal nodes are preserved with flattened children.
-/
def polyFreeMAtFixToPolyFix (P : PolyEndo X) {x : X} :
    PolyFreeM (polyFixCarrier P) P x → PolyFix P x
  | PolyFix.mk y idx children =>
    match idx with
    | Sum.inl ⟨⟨_, tree⟩, hfib⟩ => hfib ▸ tree
    | Sum.inr i => PolyFix.mk y i fun e =>
        polyFreeMAtFixToPolyFix P (children e)

/--
Round-trip from PolyFix through PolyFreeM returns the original tree.
This shows that `polyFreeMAtFixToPolyFix` is a left inverse of
`polyFixToFreeMAtFix`, making `PolyFix P` a retract of
`PolyFreeM (polyFixCarrier P) P`.
-/
theorem polyFreeMAtFix_leftInverse (P : PolyEndo X) {x : X}
    (t : PolyFix P x) :
    polyFreeMAtFixToPolyFix P (polyFixToFreeMAtFix P t) = t := by
  induction t with
  | mk y i children ih =>
    simp only [polyFixToFreeMAtFix, polyFreeMAtFixToPolyFix]
    congr 1
    funext e
    exact ih e

/--
`polyFreeMAtFixToPolyFix` is a left inverse of `polyFixToFreeMAtFix`.
-/
theorem polyFixToFreeMAtFix_hasLeftInverse (P : PolyEndo X) (x : X) :
    Function.LeftInverse
      (polyFreeMAtFixToPolyFix P (x := x))
      (polyFixToFreeMAtFix P) :=
  polyFreeMAtFix_leftInverse P

/--
The embedding from W-type into free monad at W-type carrier is injective.
-/
theorem polyFixToFreeMAtFix_injective (P : PolyEndo X) (x : X) :
    Function.Injective (polyFixToFreeMAtFix P (x := x)) :=
  (polyFixToFreeMAtFix_hasLeftInverse P x).injective

/--
The flattening map from free monad at W-type carrier to W-type is surjective.
-/
theorem polyFreeMAtFixToPolyFix_surjective (P : PolyEndo X) (x : X) :
    Function.Surjective (polyFreeMAtFixToPolyFix P (x := x)) :=
  (polyFixToFreeMAtFix_hasLeftInverse P x).surjective

/-! ### Cofree Comonad at Terminal Coalgebra

The cofree comonad applied to the terminal coalgebra (M-type) forms a
section-retraction pair with the terminal coalgebra. Specifically:

- `polyCofixToCofreeAtCofix` annotates each node with its subtree
- `polyCofreeAtCofixToPolyCofix` extracts the root annotation

The composition `extract ∘ annotate = id` holds (M-type is a retract), but
`annotate ∘ extract ≠ id` in general. This is because
`PolyCofreeM (polyCofixCarrier P) P` allows arbitrary M-type annotations at
each node, not just the subtree rooted there.

Extracting gives the root annotation (an M-type), but re-annotating creates
a cofree comonad where each node's annotation IS its subtree. If the original
had different annotations, we don't recover it.

A quotient identifying different annotation choices that have the same
root would yield a true equivalence.
-/

/--
Build the approximation for annotating an M-type with its subtrees.
At each node, the annotation is the M-type itself (the full subtree rooted at
that position). We pass the M-type as an additional parameter.
-/
def polyCofixToCofreeAtCofixApprox (P : PolyEndo X) {n : Nat} {x : X}
    (m : PolyCofix P x) :
    PolyCofixApprox (polyScale (polyCofixCarrier P) P) n x :=
  match n with
  | 0 => PolyCofixApprox.continue x
  | _ + 1 =>
    PolyCofixApprox.intro x ⟨⟨⟨x, m⟩, rfl⟩, m.head⟩
      (fun e => polyCofixToCofreeAtCofixApprox P (m.children e))

/--
The approximations for annotating an M-type with its subtrees are consistent.
-/
theorem polyCofixToCofreeAtCofixApprox_consistent (P : PolyEndo X) {n : Nat}
    {x : X} (m : PolyCofix P x) :
    PolyCofixAgree (polyScale (polyCofixCarrier P) P)
      (polyCofixToCofreeAtCofixApprox P (n := n) m)
      (polyCofixToCofreeAtCofixApprox P (n := n + 1) m) := by
  cases n with
  | zero =>
    simp only [polyCofixToCofreeAtCofixApprox]
    exact PolyCofixAgree.continue x _
  | succ n =>
    simp only [polyCofixToCofreeAtCofixApprox]
    exact PolyCofixAgree.intro _ _
      (fun e => polyCofixToCofreeAtCofixApprox_consistent P (m.children e))

/--
Embed an M-type into the cofree comonad at the M-type carrier.
Each node is annotated with the subtree rooted at that node.
-/
def polyCofixToCofreeAtCofix (P : PolyEndo X) {x : X}
    (m : PolyCofix P x) : PolyCofreeM (polyCofixCarrier P) P x where
  approx := fun _ => polyCofixToCofreeAtCofixApprox P m
  consistent := fun _ => polyCofixToCofreeAtCofixApprox_consistent P m

/--
Extract the root annotation from a cofree comonad at M-type carrier.
This is the counit/extract operation of the comonad.
-/
def polyCofreeAtCofixToPolyCofix (P : PolyEndo X) {x : X}
    (c : PolyCofreeM (polyCofixCarrier P) P x) : PolyCofix P x :=
  c.head.1.property ▸ c.head.1.val.2

/--
Round-trip from PolyCofix through PolyCofreeM returns the original M-type.
This shows that `polyCofreeAtCofixToPolyCofix` is a left inverse of
`polyCofixToCofreeAtCofix`.
-/
theorem polyCofreeAtCofix_leftInverse (P : PolyEndo X) {x : X}
    (m : PolyCofix P x) :
    polyCofreeAtCofixToPolyCofix P (polyCofixToCofreeAtCofix P m) = m := rfl

/--
`polyCofreeAtCofixToPolyCofix` is a left inverse of `polyCofixToCofreeAtCofix`.
This means PolyCofix P is a retract of PolyCofreeM (polyCofixCarrier P) P.
-/
theorem polyCofixToCofreeAtCofix_hasLeftInverse (P : PolyEndo X) (x : X) :
    Function.LeftInverse
      (polyCofreeAtCofixToPolyCofix P (x := x))
      (polyCofixToCofreeAtCofix P) :=
  polyCofreeAtCofix_leftInverse P

/--
The terminal coalgebra is injected into the cofree comonad at the coalgebra.
-/
theorem polyCofixToCofreeAtCofix_injective (P : PolyEndo X) (x : X) :
    Function.Injective (polyCofixToCofreeAtCofix P (x := x)) :=
  (polyCofixToCofreeAtCofix_hasLeftInverse P x).injective

/--
Extraction from the cofree comonad at the terminal coalgebra is surjective.
-/
theorem polyCofreeAtCofixToPolyCofix_surjective (P : PolyEndo X) (x : X) :
    Function.Surjective (polyCofreeAtCofixToPolyCofix P (x := x)) :=
  (polyCofixToCofreeAtCofix_hasLeftInverse P x).surjective

/-! ### Monad Structure on Free Monad

The free monad `PolyFreeM A P` has a monad structure where:
- `pure` embeds an A-value as a leaf
- `bind` substitutes at leaves
-/

/--
The pure operation for the free monad: embed an A-value as a leaf.
Given an element of A at fiber x, create a leaf node in the free monad.
-/
def polyFreeMPure (A : Over X) (P : PolyEndo X) {x : X}
    (a : { v : A.left // A.hom v = x }) : PolyFreeM A P x :=
  PolyFix.mk x (Sum.inl a) (fun e => PEmpty.elim e)

/--
Two `polyFreeMPure` values with the same underlying element are HEq across fibers.
-/
lemma polyFreeMPure_fiber_heq (A : Over X) (P : PolyEndo X) {x y : X}
    (hfib : x = y) (a : A.left) (hx : A.hom a = x) (hy : A.hom a = y) :
    HEq (polyFreeMPure A P ⟨a, hx⟩ : PolyFreeM A P x)
        (polyFreeMPure A P ⟨a, hy⟩ : PolyFreeM A P y) := by
  subst hfib
  rfl

/--
The bind operation for the free monad: substitute at leaves.
Recursively traverses the tree, replacing leaves with subtrees computed by f.
-/
def polyFreeMBind (A B : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x)
    (f : ∀ y, { a : A.left // A.hom a = y } → PolyFreeM B P y) :
    PolyFreeM B P x :=
  match t with
  | PolyFix.mk _ (Sum.inl a) _ => f x a
  | PolyFix.mk _ (Sum.inr p) children =>
    PolyFix.mk x (Sum.inr p) fun e =>
      polyFreeMBind A B P (children e) f

/--
Left identity: bind (pure a) f = f a
-/
theorem polyFreeM_pure_bind (A B : Over X) (P : PolyEndo X) {x : X}
    (a : { v : A.left // A.hom v = x })
    (f : ∀ y, { a : A.left // A.hom a = y } → PolyFreeM B P y) :
    polyFreeMBind A B P (polyFreeMPure A P a) f = f x a := rfl

/--
Right identity: bind t pure = t
-/
theorem polyFreeM_bind_pure (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x) :
    polyFreeMBind A A P t (fun _ a => polyFreeMPure A P a) = t := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl a =>
      simp only [polyFreeMBind, polyFreeMPure]
      congr 1
      funext e
      exact PEmpty.elim e
    | Sum.inr p =>
      simp only [polyFreeMBind]
      congr 1
      funext e
      exact ih e

/--
Associativity: bind (bind t f) g = bind t (fun a => bind (f a) g)
-/
theorem polyFreeM_bind_assoc (A B C : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x)
    (f : ∀ y, { a : A.left // A.hom a = y } → PolyFreeM B P y)
    (g : ∀ y, { b : B.left // B.hom b = y } → PolyFreeM C P y) :
    polyFreeMBind B C P (polyFreeMBind A B P t f) g =
    polyFreeMBind A C P t (fun y a => polyFreeMBind B C P (f y a) g) := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl a => rfl
    | Sum.inr p =>
      simp only [polyFreeMBind]
      congr 1
      funext e
      exact ih e

/-! ### Comonad Structure on Cofree Comonad

The cofree comonad `PolyCofreeM A P` has a comonad structure where:
- `extract` extracts the A-annotation at the root
- `extend` recomputes annotations throughout the tree
-/

/--
Extract the A-annotation at the root of a cofree comonad tree.
-/
def polyCofreeExtract (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : { a : A.left // A.hom a = x } :=
  let head := m.head
  head.1

/--
The head of a cofree comonad tree gives both the label and the P-index.
-/
def polyCofreeHead (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : polyScaleIndex A P x :=
  m.head

/--
Helper for building the approximation at depth n for extend.
-/
def polyCofreeExtendApprox (A B : Over X) (P : PolyEndo X) (n : Nat)
    (f : ∀ y, PolyCofreeM A P y → { b : B.left // B.hom b = y })
    (x : X) (m : PolyCofreeM A P x) :
    PolyCofixApprox (polyScale B P) n x :=
  match n with
  | 0 => PolyCofixApprox.continue x
  | n + 1 =>
    let head := m.head
    let newLabel : { b : B.left // B.hom b = x } := f x m
    PolyCofixApprox.intro x ⟨newLabel, head.2⟩ fun e =>
      polyCofreeExtendApprox A B P n f _ (m.children e)

/--
Helper for proving consistency for extend.
-/
def polyCofreeExtendAgree (A B : Over X) (P : PolyEndo X) (n : Nat)
    (f : ∀ y, PolyCofreeM A P y → { b : B.left // B.hom b = y })
    (x : X) (m : PolyCofreeM A P x) :
    PolyCofixAgree (polyScale B P)
      (polyCofreeExtendApprox A B P n f x m)
      (polyCofreeExtendApprox A B P (n + 1) f x m) :=
  match n with
  | 0 => PolyCofixAgree.continue x _
  | n + 1 =>
    PolyCofixAgree.intro _ _ fun e =>
      polyCofreeExtendAgree A B P n f _ (m.children e)

/--
Extend (duplicate) operation for the cofree comonad.
At each node, the new annotation is computed by applying f to the subtree.
-/
def polyCofreeExtend (A B : Over X) (P : PolyEndo X) {x : X}
    (f : ∀ y, PolyCofreeM A P y → { b : B.left // B.hom b = y })
    (m : PolyCofreeM A P x) : PolyCofreeM B P x := {
  approx := fun n => polyCofreeExtendApprox A B P n f x m
  consistent := fun n => polyCofreeExtendAgree A B P n f x m
}

/-! ### Polynomial Representation of Free Monad

The free monad functor `A ↦ PolyFreeM A P` is itself a polynomial functor.
To represent it as a `PolyEndo X`:
- Positions at x = tree shapes = `PolyFreeM (overTerminal X) P x`
- Directions at position t = leaf positions in the tree t
-/

/--
Tree shapes for the free monad: trees with trivially-labeled leaves.
These are the positions of the free monad viewed as a polynomial functor.
-/
abbrev PolyFreeMShape (P : PolyEndo X) (x : X) : Type u :=
  PolyFreeM (overTerminal X) P x

/--
Leaf positions in a tree shape. For each tree shape, this gives the type
of "holes" where leaf data from A would be placed.

At a leaf node: exactly one position (the leaf itself)
At an internal node: the sum of leaf positions in all children
-/
def PolyFreeMLeafPos (P : PolyEndo X) {x : X} :
    PolyFreeMShape P x → Type u
  | PolyFix.mk _ (Sum.inl _) _ => PUnit
  | PolyFix.mk _ (Sum.inr p) children =>
    Σ (e : (polyBetweenFamily X X P x p).left),
      PolyFreeMLeafPos P (children e)

/--
The fiber of a leaf position. Given a tree shape and a leaf position in it,
returns the fiber at which that leaf lives.
-/
def PolyFreeMLeafFiber (P : PolyEndo X) {x : X}
    (t : PolyFreeMShape P x) : PolyFreeMLeafPos P t → X :=
  match t with
  | PolyFix.mk y (Sum.inl _) _ => fun _ => y
  | PolyFix.mk _ (Sum.inr _) children => fun pos =>
    let ⟨e, pos'⟩ := pos
    PolyFreeMLeafFiber P (children e) pos'

/--
The family for the free monad polynomial at each position.
Maps each tree shape to the Over X object representing its leaf positions.
-/
def polyFreeMFamily (P : PolyEndo X) (x : X)
    (shape : PolyFreeMShape P x) : Over X :=
  Over.mk (f := PolyFreeMLeafFiber P shape)

/--
The free monad functor represented as a polynomial endofunctor.
-/
def polyFreeMPoly (P : PolyEndo X) : PolyEndo X := fun x =>
  ccrObjMk (polyFreeMFamily P x)

/--
The positions of the free monad polynomial at fiber `x` are exactly the tree
shapes (free monad applied to the terminal object).
-/
lemma polyFreeMPoly_index (P : PolyEndo X) (x : X) :
    polyBetweenIndex X X (polyFreeMPoly P) x = PolyFreeMShape P x := rfl

/--
Build a free monad tree from a shape and leaf data.
Given a tree shape and a function assigning A-values to each leaf position,
constructs the corresponding element of PolyFreeM A P.
-/
def polyFreeMFromShape (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyFreeMShape P x)
    (leafData : (pos : PolyFreeMLeafPos P shape) →
      { a : A.left // A.hom a = PolyFreeMLeafFiber P shape pos }) :
    PolyFreeM A P x :=
  match shape with
  | PolyFix.mk y (Sum.inl _) _ =>
    let aVal := leafData PUnit.unit
    PolyFix.mk y (Sum.inl aVal) (fun e => PEmpty.elim e)
  | PolyFix.mk y (Sum.inr p) children =>
    PolyFix.mk y (Sum.inr p) fun e =>
      polyFreeMFromShape A P (children e) fun pos =>
        leafData ⟨e, pos⟩

/--
Extract the shape from a free monad tree.
Replaces all leaf labels with trivial labels.
-/
def polyFreeMToShape (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x) : PolyFreeMShape P x :=
  match t with
  | PolyFix.mk y (Sum.inl _) _ =>
    PolyFix.mk y (Sum.inl ⟨y, rfl⟩) (fun e => PEmpty.elim e)
  | PolyFix.mk y (Sum.inr p) children =>
    PolyFix.mk y (Sum.inr p) fun e =>
      polyFreeMToShape A P (children e)

/--
Extract the leaf data from a free monad tree.
Given a tree, returns a function mapping each leaf position to its label.
-/
def polyFreeMLeafData (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x) :
    (pos : PolyFreeMLeafPos P (polyFreeMToShape A P t)) →
    { a : A.left // A.hom a = PolyFreeMLeafFiber P (polyFreeMToShape A P t) pos
    } :=
  match t with
  | PolyFix.mk _ (Sum.inl a) _ => fun _ => a
  | PolyFix.mk _ (Sum.inr _) children => fun ⟨e, pos⟩ =>
    polyFreeMLeafData A P (children e) pos

/--
Roundtrip: extracting shape from a tree built from shape and data gives back
the original shape.
-/
theorem polyFreeMFromShape_toShape (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyFreeMShape P x)
    (leafData : (pos : PolyFreeMLeafPos P shape) →
      { a : A.left // A.hom a = PolyFreeMLeafFiber P shape pos }) :
    polyFreeMToShape A P (polyFreeMFromShape A P shape leafData) = shape := by
  induction shape with
  | mk y idx children ih =>
    cases idx with
    | inl label =>
      simp only [polyFreeMFromShape, polyFreeMToShape]
      congr 1
      · congr 1
        exact Subtype.ext label.property.symm
      · funext e
        exact PEmpty.elim e
    | inr p =>
      simp only [polyFreeMFromShape, polyFreeMToShape]
      congr 1
      funext e
      exact ih e _

/--
Roundtrip: building a tree from shape and data, then extracting, gives back
the original tree.
-/
theorem polyFreeM_roundtrip (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x) :
    polyFreeMFromShape A P (polyFreeMToShape A P t)
      (polyFreeMLeafData A P t) = t := by
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      simp only [polyFreeMToShape, polyFreeMFromShape, polyFreeMLeafData]
      congr 1
      funext e
      exact PEmpty.elim e
    | inr p =>
      simp only [polyFreeMToShape, polyFreeMFromShape]
      congr 1
      funext e
      exact ih e


/--
The free monad polynomial evaluation type: standard polynomial evaluation
of the free monad polynomial at A.
-/
abbrev PolyFreeMPolyEval (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  polyBetweenEvalFamily X X (polyFreeMPoly P) A x

/--
Convert from polynomial evaluation to free monad.
-/
def polyFreeMPolyEval_to_polyFreeM (A : Over X) (P : PolyEndo X) {x : X}
    (eval : PolyFreeMPolyEval A P x) : PolyFreeM A P x :=
  polyFreeMFromShape A P eval.fst fun pos =>
    ⟨eval.snd.left pos, overMor_w eval.snd pos⟩

/--
Convert from free monad to polynomial evaluation.
-/
def polyFreeM_to_polyFreeMPolyEval (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM A P x) : PolyFreeMPolyEval A P x :=
  ⟨polyFreeMToShape A P t,
   Over.homMk (fun pos => (polyFreeMLeafData A P t pos).val)
     (funext fun pos => (polyFreeMLeafData A P t pos).property)⟩

/--
Right inverse helper: the sigma pair roundtrip equality for the polynomial
evaluation type. This is proven by induction on the shape.
-/
theorem polyFreeMPolyEval_roundtrip (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyFreeMShape P x)
    (mor : polyFreeMFamily P x shape ⟶ A) :
    polyFreeM_to_polyFreeMPolyEval A P
      (polyFreeMFromShape A P shape
        (fun pos => ⟨mor.left pos, overMor_w mor pos⟩)) =
    ⟨shape, mor⟩ := by
  induction shape with
  | mk y idx children ih =>
    cases idx with
    | inl _ =>
      simp only [polyFreeMFromShape, polyFreeM_to_polyFreeMPolyEval,
        polyFreeMToShape, polyFreeMLeafData]
      have hfst := polyFreeMFromShape_toShape A P
        (PolyFix.mk y (Sum.inl _) children)
        (fun pos => ⟨mor.left pos, overMor_w mor pos⟩)
      simp only [polyFreeMFromShape, polyFreeMToShape] at hfst
      apply Sigma.ext hfst
      apply heq_of_eq
      apply Over.OverMorphism.ext
      funext pos
      cases pos
      rfl
    | inr p =>
      let mor_e (e : _) : polyFreeMFamily P _ (children e) ⟶ A :=
        Over.homMk (fun pos' => mor.left ⟨e, pos'⟩)
          (funext fun pos' => overMor_w mor ⟨e, pos'⟩)
      have ih_applied : ∀ e, polyFreeM_to_polyFreeMPolyEval A P
          (polyFreeMFromShape A P (children e)
            (fun pos => ⟨(mor_e e).left pos, overMor_w (mor_e e) pos⟩)) =
          ⟨children e, mor_e e⟩ :=
        fun e => ih e (mor_e e)
      simp only [polyFreeMFromShape, polyFreeM_to_polyFreeMPolyEval,
        polyFreeMToShape, polyFreeMLeafData]
      simp only [polyFreeM_to_polyFreeMPolyEval] at ih_applied
      have hfst := polyFreeMFromShape_toShape A P
        (PolyFix.mk y (Sum.inr p) children)
        (fun pos => ⟨mor.left pos, overMor_w mor pos⟩)
      simp only [polyFreeMFromShape, polyFreeMToShape] at hfst
      have hchildren_eq : (fun e =>
          polyFreeMToShape A P (polyFreeMFromShape A P (children e)
            fun pos => ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩)) = children := by
        funext e'
        exact congrArg Sigma.fst (ih_applied e')
      refine Sigma.ext hfst ?_
      have htype : (polyFreeMFamily P y (PolyFix.mk y (Sum.inr p) fun e =>
          polyFreeMToShape A P (polyFreeMFromShape A P (children e) fun pos =>
            ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩)) ⟶ A) =
          (polyFreeMFamily P y (PolyFix.mk y (Sum.inr p) children) ⟶ A) :=
        congrArg (fun s => polyFreeMFamily P y s ⟶ A) hfst
      refine HEq.trans ?heq1 (cast_heq htype.symm mor)
      apply heq_of_eq
      apply Over.OverMorphism.ext
      funext ⟨e, pos_inner⟩
      simp only [Over.homMk_left]
      have hshape_e : polyFreeMToShape A P
          (polyFreeMFromShape A P (children e) fun pos =>
            ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩) = children e :=
        congrArg Sigma.fst (ih_applied e)
      have hmor_type_e : (polyFreeMFamily P
          ((polyBetweenFamily X X (polyTranslate (overTerminal X) P) y (Sum.inr p)).hom e)
          (polyFreeMToShape A P (polyFreeMFromShape A P (children e) fun pos =>
            ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩)) ⟶ A) =
          (polyFreeMFamily P
            ((polyBetweenFamily X X (polyTranslate (overTerminal X) P) y (Sum.inr p)).hom e)
            (children e) ⟶ A) :=
        congrArg (fun s => polyFreeMFamily P _ s ⟶ A) hshape_e
      have hpos_cast : PolyFreeMLeafPos P
          (polyFreeMToShape A P (polyFreeMFromShape A P (children e) fun pos =>
            ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩)) =
          PolyFreeMLeafPos P (children e) :=
        congrArg (PolyFreeMLeafPos P) hshape_e
      have hmor_snd_heq : (polyFreeM_to_polyFreeMPolyEval A P
            (polyFreeMFromShape A P (children e) fun pos =>
              ⟨(mor_e e).left pos, overMor_w (mor_e e) pos⟩)).snd ≍ (mor_e e) :=
        sigma_snd_heq_of_eq (ih_applied e)
      have hmor_eq : (polyFreeM_to_polyFreeMPolyEval A P
            (polyFreeMFromShape A P (children e) fun pos =>
              ⟨(mor_e e).left pos, overMor_w (mor_e e) pos⟩)).snd =
          cast hmor_type_e.symm (mor_e e) :=
        eq_of_heq (hmor_snd_heq.trans (cast_heq hmor_type_e.symm _).symm)
      have hdata_eq : (polyFreeMLeafData A P
            (polyFreeMFromShape A P (children e) fun pos =>
              ⟨mor.left ⟨e, pos⟩, overMor_w mor ⟨e, pos⟩⟩) pos_inner).val =
          (mor_e e).left (cast hpos_cast pos_inner) := by
        have h_left_fn_eq : (polyFreeM_to_polyFreeMPolyEval A P
            (polyFreeMFromShape A P (children e) fun pos =>
              ⟨(mor_e e).left pos, overMor_w (mor_e e) pos⟩)).snd.left =
            (cast hmor_type_e.symm (mor_e e)).left := by
          rw [hmor_eq]
        simp only [polyFreeM_to_polyFreeMPolyEval, Over.homMk_left] at h_left_fn_eq
        have h_at_pos := congrFun h_left_fn_eq pos_inner
        rw [over_cast_left (congrArg (polyFreeMFamily P _) hshape_e.symm)] at h_at_pos
        simp only [polyFreeMFamily, Over.mk_left] at h_at_pos
        simp only [mor_e, Over.homMk_left] at h_at_pos ⊢
        exact h_at_pos
      simp only [hdata_eq]
      simp only [polyFreeMFamily, Over.mk_left, PolyFreeMLeafPos]
      rw [over_cast_left (congrArg (fun s => polyFreeMFamily P y s) hfst.symm)]
      simp only [polyFreeMFamily, Over.mk_left, PolyFreeMLeafPos]
      simp only [mor_e, Over.homMk_left]
      have harg_eq : ⟨e, cast hpos_cast pos_inner⟩ =
          (cast (congrArg (fun f => Σ e, PolyFreeMLeafPos P (f e)) hchildren_eq)
            ⟨e, pos_inner⟩) := by
        symm
        exact sigma_cast_eq_mk (fun e' =>
          congrArg (PolyFreeMLeafPos P) (congrFun hchildren_eq e'))
      rw [harg_eq]

/--
The bijection between free monad and polynomial evaluation.

The forward direction extracts the tree shape and leaf data.
The backward direction reconstructs the tree from shape and leaf data.

The left inverse is proven via `polyFreeM_roundtrip`.
The right inverse is proven via `polyFreeMPolyEval_roundtrip`.
-/
def polyFreeMEquivPolyEval (A : Over X) (P : PolyEndo X) (x : X) :
    PolyFreeM A P x ≃ PolyFreeMPolyEval A P x where
  toFun := polyFreeM_to_polyFreeMPolyEval A P
  invFun := polyFreeMPolyEval_to_polyFreeM A P
  left_inv t := polyFreeM_roundtrip A P t
  right_inv := by
    intro ⟨shape, mor⟩
    exact polyFreeMPolyEval_roundtrip A P shape mor

/--
Evaluating the free monad polynomial at the terminal object gives an
equivalence with the shape type (positions of the polynomial).

Since `PolyFreeMShape P x = PolyFreeM (overTerminal X) P x`, this is an
instance of `polyFreeMEquivPolyEval` at the terminal object.
-/
def polyFreeMTerminalEvalEquiv (P : PolyEndo X) (x : X) :
    PolyFreeMShape P x ≃ PolyFreeMPolyEval (overTerminal X) P x :=
  polyFreeMEquivPolyEval (overTerminal X) P x

/--
Evaluating the free monad polynomial at the initial object gives an
equivalence with the initial algebra (W-type).

Since `PolyFreeM (overInitial X) P x ≃ PolyFix P x`, this composes
`polyFixEquivPolyFreeM` with `polyFreeMEquivPolyEval`.
-/
def polyFreeMInitialEvalEquiv (P : PolyEndo X) (x : X) :
    PolyFix P x ≃ PolyFreeMPolyEval (overInitial X) P x :=
  (polyFixEquivPolyFreeM P x).trans (polyFreeMEquivPolyEval (overInitial X) P x)

/-! ### Polynomial Representation of Cofree Comonad

The cofree comonad `A ↦ PolyCofreeM A P` is a polynomial functor. Its positions
(shapes) are M-type structures with trivial annotations, and its directions are
the annotation positions within each shape.
-/

/--
Shape of the cofree comonad: streams with trivial (terminal) annotations.
This represents the "structure" of the stream without the annotation data.
-/
abbrev PolyCofreeShape (P : PolyEndo X) (x : X) : Type u :=
  PolyCofreeM (overTerminal X) P x

/--
A path segment in a cofree comonad shape consists of the fiber and the
child index taken.
-/
structure PolyCofreePathSeg (P : PolyEndo X) where
  fiber : X
  idx : polyBetweenIndex X X P fiber
  childIdx : (polyBetweenFamily X X P fiber idx).left

/--
Annotation positions in a cofree comonad shape at depth n.
At depth 0, there's just the root position.
At depth n+1, we have a path segment followed by a position at depth n.
-/
def PolyCofreeAnnotPosAt (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x) : Nat → Type u
  | 0 => PUnit
  | n + 1 =>
    Σ (e : (polyBetweenFamily X X P x s.head.2).left),
      PolyCofreeAnnotPosAt P (s.children e) n

/--
Annotation positions in a cofree comonad shape: either the root or a position
at some depth.
-/
def PolyCofreeAnnotPos (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x) : Type u :=
  Σ n : Nat, PolyCofreeAnnotPosAt P s n

/--
Helper to get the fiber of a position at depth n.
-/
def PolyCofreeAnnotFiberAt (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x) : (n : Nat) → PolyCofreeAnnotPosAt P s n → X
  | 0, _ => x
  | n + 1, ⟨e, pos⟩ => PolyCofreeAnnotFiberAt P (s.children e) n pos

/--
The fiber at each annotation position in a cofree comonad shape.
-/
def PolyCofreeAnnotFiber (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x) (pos : PolyCofreeAnnotPos P s) : X :=
  PolyCofreeAnnotFiberAt P s pos.1 pos.2

/--
The family for the cofree comonad polynomial at each position.
Maps each M-type shape to the Over X object representing its annotation
positions.
-/
def polyCofreeFamily (P : PolyEndo X) (x : X)
    (shape : PolyCofreeShape P x) : Over X :=
  Over.mk (f := PolyCofreeAnnotFiber P shape)

/--
The cofree comonad functor represented as a polynomial endofunctor.
-/
def polyCofreeMPoly (P : PolyEndo X) : PolyEndo X := fun x =>
  ccrObjMk (polyCofreeFamily P x)

/--
The positions of the cofree comonad polynomial at fiber `x` are exactly the
stream shapes (cofree comonad applied to the terminal object).
-/
lemma polyCofreeMPoly_index (P : PolyEndo X) (x : X) :
    polyBetweenIndex X X (polyCofreeMPoly P) x = PolyCofreeShape P x := rfl

/--
The cofree comonad polynomial evaluation type: standard polynomial evaluation
of the cofree comonad polynomial at A.
-/
abbrev PolyCofreePolyEval (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  polyBetweenEvalFamily X X (polyCofreeMPoly P) A x

/--
Convert a cofree comonad approximation to a shape approximation by forgetting
annotations.
-/
def polyCofreeApproxToShape (A : Over X) (P : PolyEndo X) {n : Nat} {x : X} :
    PolyCofixApprox (polyScale A P) n x →
    PolyCofixApprox (polyScale (overTerminal X) P) n x
  | PolyCofixApprox.continue y => PolyCofixApprox.continue y
  | PolyCofixApprox.intro y ⟨_, i⟩ children =>
    PolyCofixApprox.intro y ⟨⟨y, rfl⟩, i⟩
      (fun e => polyCofreeApproxToShape A P (children e))

/--
The approximation-to-shape conversion preserves the agreement relation.
-/
theorem polyCofreeApproxToShape_agree (A : Over X) (P : PolyEndo X)
    {n : Nat} {x : X}
    {a : PolyCofixApprox (polyScale A P) n x}
    {b : PolyCofixApprox (polyScale A P) (n + 1) x}
    (h : PolyCofixAgree (polyScale A P) a b) :
    PolyCofixAgree (polyScale (overTerminal X) P)
      (polyCofreeApproxToShape A P a)
      (polyCofreeApproxToShape A P b) := by
  induction h with
  | «continue» x' y' =>
    exact PolyCofixAgree.continue x' (polyCofreeApproxToShape A P y')
  | intro f f' child_agree ih' =>
    exact PolyCofixAgree.intro _ _ ih'

/--
Extract the shape from a cofree comonad value.
-/
def polyCofreeToShape (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : PolyCofreeShape P x := {
  approx := fun n => polyCofreeApproxToShape A P (m.approx n)
  consistent := fun n => polyCofreeApproxToShape_agree A P (m.consistent n)
}

/--
The approximation-to-shape conversion preserves the polynomial index.
-/
lemma polyCofreeApproxToShape_index (A : Over X) (P : PolyEndo X)
    {n : Nat} {x : X} (a : PolyCofixApprox (polyScale A P) (n + 1) x) :
    (polyCofreeApproxToShape A P a).getIndex.2 = a.getIndex.2 := by
  cases a with
  | intro y i children => rfl

/--
The shape extraction preserves the head's polynomial index.
-/
lemma polyCofreeToShape_head_index (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) :
    (polyCofreeToShape A P m).head.2 = m.head.2 := by
  simp only [PolyCofix.head, polyCofreeToShape]
  exact polyCofreeApproxToShape_index A P (m.approx 1)

/--
Cast a position element using the head index equality.
-/
def polyCofreeShapePosToMPos (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (e : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left) :
    (polyBetweenFamily X X P x m.head.2).left :=
  (polyCofreeToShape_head_index A P m) ▸ e

/--
Extract the root annotation from a cofree comonad value.
-/
def polyCofreeGetRoot (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : { a : A.left // A.hom a = x } :=
  m.head.1

/--
Helper: transport in polyBetweenFamily preserves the fiber projection.
-/
lemma polyBetweenFamily_hom_transport {Y : Type u} {P' : PolyEndo Y} {y : Y}
    {i j : polyBetweenIndex Y Y P' y}
    (h : i = j) (e : (polyBetweenFamily Y Y P' y i).left) :
    (polyBetweenFamily Y Y P' y i).hom e =
    (polyBetweenFamily Y Y P' y j).hom (h ▸ e) := by
  subst h
  rfl

/--
The fiber of a shape position equals the fiber of the corresponding M-type
position under `polyCofreeShapePosToMPos`.
-/
lemma polyCofreeShapePosToMPos_fiber (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (e_shape : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    :
    (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom e_shape =
    (polyBetweenFamily X X P x m.head.2).hom
      (polyCofreeShapePosToMPos A P m e_shape) := by
  simp only [polyCofreeShapePosToMPos]
  exact polyBetweenFamily_hom_transport (polyCofreeToShape_head_index A P m)
    e_shape

/--
HEq version of shape position to M-type position conversion.
-/
lemma polyCofreeShapePosToMPos_heq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (e_shape : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    :
    HEq e_shape (polyCofreeShapePosToMPos A P m e_shape) := by
  simp only [polyCofreeShapePosToMPos]
  exact (eqRec_heq (φ := fun i => (polyBetweenFamily X X P x i).left)
    (polyCofreeToShape_head_index A P m) e_shape).symm

/--
Helper: HEq for PolyCofixApprox.continue when the fiber values are equal.
-/
lemma polyCofixApprox_continue_heq {P : PolyEndo X} {y1 y2 : X} (h : y1 = y2) :
    HEq (PolyCofixApprox.continue (P := P) y1)
        (PolyCofixApprox.continue (P := P) y2) := by
  subst h
  rfl

/--
For an `.intro` approximation, extracting children then converting to shape
is HEq to converting to shape then extracting children.

This lemma avoids the `generalize` issue by having the approximation as an
explicit parameter that can be directly pattern matched.
-/
lemma polyCofreeApproxToShape_childApproxAt_succ_aux_heq
    (A : Over X) (P : PolyEndo X) {n : Nat} {x : X}
    (head_m : polyBetweenIndex X X (polyScale A P) x)
    (head_shape : polyBetweenIndex X X (polyScale (overTerminal X) P) x)
    (hhead_P : head_shape.2 = head_m.2)
    (a : PolyCofixApprox (polyScale A P) (n + 2) x)
    (heq_m : a.getIndex = head_m)
    (heq_shape : (polyCofreeApproxToShape A P a).getIndex = head_shape)
    (e_shape : (polyBetweenFamily X X (polyScale (overTerminal X) P) x
      head_shape).left)
    (e_m : (polyBetweenFamily X X (polyScale A P) x head_m).left)
    (he : HEq e_shape e_m)
    (hfiber : (polyBetweenFamily X X (polyScale (overTerminal X) P) x
        head_shape).hom e_shape =
      (polyBetweenFamily X X (polyScale A P) x head_m).hom e_m) :
    HEq (PolyCofix.childApproxAt_succ_aux head_shape
        (polyCofreeApproxToShape A P a) heq_shape e_shape)
      (polyCofreeApproxToShape A P
        (PolyCofix.childApproxAt_succ_aux head_m a heq_m e_m)) := by
  cases a with
  | intro _ idx children =>
    simp only [PolyCofix.childApproxAt_succ_aux]
    have hidx_shape_eq : (⟨⟨x, rfl⟩, idx.2⟩ : polyBetweenIndex X X
        (polyScale (overTerminal X) P) x) = head_shape := by
      simp only [PolyCofixApprox.getIndex] at heq_shape
      exact heq_shape
    have hidx_m_eq : idx = head_m := heq_m
    subst hidx_m_eq hidx_shape_eq
    simp only [eqRec_eq_cast]
    cases he
    rfl

/--
The shape of a child equals the child of the shape (via HEq for fibers).

This relates navigating children in shape-space vs M-type-space.
-/
theorem polyCofreeToShape_children_heq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (e_shape : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    :
    HEq ((polyCofreeToShape A P m).children e_shape)
        (polyCofreeToShape A P
          (m.children (polyCofreeShapePosToMPos A P m e_shape))) := by
  apply PolyCofix.heq_of_approx_heq (polyCofreeShapePosToMPos_fiber A P m e_shape)
  intro n
  simp only [PolyCofix.children, polyCofreeToShape]
  cases n with
  | zero =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_zero,
      polyCofreeApproxToShape]
    exact polyCofixApprox_continue_heq
      (polyCofreeShapePosToMPos_fiber A P m e_shape)
  | succ n =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_succ]
    have heq_shape_proof :
        (polyCofreeApproxToShape A P (m.approx (n + 2))).getIndex =
          (polyCofreeToShape A P m).head := by
      simp only [PolyCofix.head, polyCofreeToShape]
      have h1 := polyCofreeApproxToShape_index A P (m.approx (n + 2))
      have h2 := polyCofreeApproxToShape_index A P (m.approx 1)
      have h3 := m.index_eq_head (n + 1)
      have h4 : (m.approx (n + 2)).getIndex.2 = (m.approx 1).getIndex.2 := by
        rw [congrArg Prod.snd h3]
        rfl
      apply Prod.ext
      · apply Subtype.ext
        simp only [overTerminal, Over.mk_left, Over.mk_hom]
        have ha := (polyCofreeApproxToShape A P (m.approx (n + 2))).getIndex.1.2
        have hb := (polyCofreeApproxToShape A P (m.approx 1)).getIndex.1.2
        exact ha.trans hb.symm
      · exact h1.trans (h4.trans h2.symm)
    exact polyCofreeApproxToShape_childApproxAt_succ_aux_heq A P
      m.head (polyCofreeToShape A P m).head
      (polyCofreeToShape_head_index A P m)
      (m.approx (n + 2))
      (m.index_eq_head (n + 1))
      heq_shape_proof
      e_shape
      (polyCofreeShapePosToMPos A P m e_shape)
      (polyCofreeShapePosToMPos_heq A P m e_shape)
      (polyCofreeShapePosToMPos_fiber A P m e_shape)


/-! ### M-type Based Positions

To avoid dependent type transport issues, we define positions directly on M-types
rather than on shapes. This makes annotation extraction straightforward, and we
then connect back to shape-based positions for the polynomial evaluation form.
-/

/--
Annotation positions directly on an M-type at depth n.
At depth 0: the root position.
At depth n+1: a child index paired with a position in that child.

The child index type uses the P family at `m.head.2`, which equals the
`polyScale A P` family at `m.head` by definition of `polyScale`.
-/
def PolyCofreeAnnotPosAtM (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : Nat → Type u
  | 0 => PUnit
  | n + 1 =>
    Σ (e : (polyBetweenFamily X X (polyScale A P) x m.head).left),
      PolyCofreeAnnotPosAtM A P (m.children e) n

/--
The fiber at an M-type position at depth n.
-/
def PolyCofreeAnnotFiberAtM (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : (n : Nat) → PolyCofreeAnnotPosAtM A P m n → X
  | 0, _ => x
  | n + 1, ⟨e, pos⟩ => PolyCofreeAnnotFiberAtM A P (m.children e) n pos

/--
Extract the annotation at an M-type position directly.
This is straightforward structural recursion on the position depth.
-/
def polyCofreeGetAnnotAtM (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (n : Nat) (pos : PolyCofreeAnnotPosAtM A P m n) :
    { a : A.left // A.hom a = PolyCofreeAnnotFiberAtM A P m n pos } :=
  match n with
  | 0 => m.head.1
  | n + 1 =>
    let ⟨e, pos'⟩ := pos
    polyCofreeGetAnnotAtM A P (m.children e) n pos'

/--
The child family for `polyScale A P` equals the P family at the second component.
-/
lemma polyScaleFamily_eq_P_family (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) :
    polyBetweenFamily X X (polyScale A P) x m.head =
    polyBetweenFamily X X P x m.head.2 := rfl

/--
Given fiber equality and HEq of shapes, derive equality of shapes after transport.
-/
lemma polyCofreeShape_eq_of_heq_fiber {P : PolyEndo X} {y1 y2 : X}
    (hfiber : y1 = y2)
    (s1 : PolyCofreeShape P y1) (s2 : PolyCofreeShape P y2)
    (heq : HEq s1 s2) : hfiber ▸ s1 = s2 := by
  subst hfiber
  exact eq_of_heq heq

/--
Convert a position type along shape equality (same fiber).
-/
lemma polyCofreeAnnotPosAt_cast {P : PolyEndo X} {y : X}
    {s1 s2 : PolyCofreeShape P y} (h : s1 = s2) (n : Nat) :
    PolyCofreeAnnotPosAt P s1 n = PolyCofreeAnnotPosAt P s2 n := by
  subst h
  rfl

/--
Convert a position type along fiber equality and shape HEq.
-/
lemma polyCofreeAnnotPosAt_cast_fiber {P : PolyEndo X} {y1 y2 : X}
    (hfiber : y1 = y2)
    {s1 : PolyCofreeShape P y1} {s2 : PolyCofreeShape P y2}
    (hshape : HEq s1 s2) (n : Nat) :
    PolyCofreeAnnotPosAt P s1 n = PolyCofreeAnnotPosAt P s2 n := by
  subst hfiber
  exact polyCofreeAnnotPosAt_cast (eq_of_heq hshape) n

/--
Transport lemma for PolyCofreeAnnotFiberAt: the fiber value is preserved
when transporting along fiber equality and shape HEq.
-/
lemma polyCofreeAnnotFiberAt_transport {P : PolyEndo X} {y1 y2 : X}
    (hfiber : y1 = y2)
    {s1 : PolyCofreeShape P y1} {s2 : PolyCofreeShape P y2}
    (hshape : HEq s1 s2)
    (n : Nat) (pos : PolyCofreeAnnotPosAt P s1 n) :
    PolyCofreeAnnotFiberAt P s1 n pos =
    PolyCofreeAnnotFiberAt P s2 n
      (cast (polyCofreeAnnotPosAt_cast_fiber hfiber hshape n) pos) := by
  subst hfiber
  have hshape_eq := eq_of_heq hshape
  subst hshape_eq
  rfl

/--
The shape equality for children: after fiber transport.
-/
lemma polyCofreeToShape_children_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (e_shape : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    :
    let e_m := polyCofreeShapePosToMPos A P m e_shape
    let hfiber := polyCofreeShapePosToMPos_fiber A P m e_shape
    hfiber ▸ (polyCofreeToShape A P m).children e_shape =
    polyCofreeToShape A P (m.children e_m) :=
  polyCofreeShape_eq_of_heq_fiber
    (polyCofreeShapePosToMPos_fiber A P m e_shape)
    _ _
    (polyCofreeToShape_children_heq A P m e_shape)

/--
Convert a shape position to an M-type position at depth n.
Uses the equality `(polyCofreeToShape A P m).head.2 = m.head.2` to cast elements.
-/
def polyCofreeShapePosToMPosAt (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (n : Nat) (pos : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m) n) :
    PolyCofreeAnnotPosAtM A P m n :=
  match n with
  | 0 => PUnit.unit
  | n + 1 =>
    let ⟨e_shape, pos'⟩ := pos
    let e_m := polyCofreeShapePosToMPos A P m e_shape
    let hfiber := polyCofreeShapePosToMPos_fiber A P m e_shape
    let hshape_heq := polyCofreeToShape_children_heq A P m e_shape
    let pos'_transported : PolyCofreeAnnotPosAt P
        (polyCofreeToShape A P (m.children e_m)) n :=
      cast (polyCofreeAnnotPosAt_cast_fiber hfiber hshape_heq n) pos'
    ⟨e_m, polyCofreeShapePosToMPosAt A P (m.children e_m) n pos'_transported⟩

/--
The fiber at a shape position equals the fiber at the corresponding M-type position.
-/
lemma polyCofreeAnnotFiber_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (n : Nat) (pos : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m) n) :
    PolyCofreeAnnotFiberAt P (polyCofreeToShape A P m) n pos =
    PolyCofreeAnnotFiberAtM A P m n (polyCofreeShapePosToMPosAt A P m n pos) := by
  induction n generalizing x m with
  | zero => rfl
  | succ n ih =>
    obtain ⟨e_shape, pos'⟩ := pos
    simp only [PolyCofreeAnnotFiberAt, PolyCofreeAnnotFiberAtM,
      polyCofreeShapePosToMPosAt]
    let e_m := polyCofreeShapePosToMPos A P m e_shape
    let hfiber := polyCofreeShapePosToMPos_fiber A P m e_shape
    let hshape_heq := polyCofreeToShape_children_heq A P m e_shape
    have h1 : PolyCofreeAnnotFiberAt P ((polyCofreeToShape A P m).children e_shape)
        n pos' =
        PolyCofreeAnnotFiberAt P (polyCofreeToShape A P (m.children e_m)) n
          (cast (polyCofreeAnnotPosAt_cast_fiber hfiber hshape_heq n) pos') :=
      polyCofreeAnnotFiberAt_transport hfiber hshape_heq n pos'
    rw [h1]
    exact ih (m.children e_m)
      (cast (polyCofreeAnnotPosAt_cast_fiber hfiber hshape_heq n) pos')

/--
Extract the annotation at a depth-n position from a cofree comonad value.

Uses M-type based positions internally for clean recursion, then converts
the fiber proof using the fiber equality lemma.
-/
def polyCofreeGetAnnotAt (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (n : Nat) (pos : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m) n) :
    { a : A.left // A.hom a = PolyCofreeAnnotFiberAt P
        (polyCofreeToShape A P m) n pos } :=
  let pos_m := polyCofreeShapePosToMPosAt A P m n pos
  let result := polyCofreeGetAnnotAtM A P m n pos_m
  ⟨result.val, by
    rw [polyCofreeAnnotFiber_eq A P m n pos]
    exact result.property⟩

/--
Extract the annotation at any position from a cofree comonad value.
-/
def polyCofreeGetAnnot (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (pos : PolyCofreeAnnotPos P (polyCofreeToShape A P m)) :
    { a : A.left // A.hom a = PolyCofreeAnnotFiber P
        (polyCofreeToShape A P m) pos } :=
  polyCofreeGetAnnotAt A P m pos.1 pos.2

/--
Convert a cofree comonad value to its polynomial evaluation form.

The forward direction of the equivalence `PolyCofreeM A P ≃ PolyCofreePolyEval A P`.
-/
def polyCofreeM_to_polyCofreePolyEval (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) : PolyCofreePolyEval A P x :=
  ⟨polyCofreeToShape A P m,
    Over.homMk (fun pos => (polyCofreeGetAnnot A P m pos).val)
      (funext fun pos => (polyCofreeGetAnnot A P m pos).property)⟩

/-! ### Backward Direction: Building M-type from Shape and Annotations

Given a shape (M-type with trivial annotations) and annotation data, we can
reconstruct an M-type with those annotations by building approximations.
-/

/--
Child annotation function for the backward direction.
-/
def polyCofreeChildAnnotFn (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (e : (polyBetweenFamily X X P x shape.head.2).left)
    (pos : PolyCofreeAnnotPos P (shape.children e)) : A.left :=
  f ⟨pos.1 + 1, ⟨e, pos.2⟩⟩

/--
Child annotation function preserves the fiber condition.
-/
lemma polyCofreeChildAnnotFn_fiber (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (e : (polyBetweenFamily X X P x shape.head.2).left)
    (pos : PolyCofreeAnnotPos P (shape.children e)) :
    A.hom (polyCofreeChildAnnotFn A P shape f e pos) =
    PolyCofreeAnnotFiber P (shape.children e) pos := by
  simp only [polyCofreeChildAnnotFn, PolyCofreeAnnotFiber]
  exact hf ⟨pos.1 + 1, ⟨e, pos.2⟩⟩

/--
The child annotation function at position 0 equals the child's root annotation.
This is the annotation value equality used in the roundtrip proof.
-/
lemma polyCofreeChildAnnotFn_zero_eq_childRoot (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (e : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left) :
    let b' := polyCofreeShapePosToMPos A P m e
    polyCofreeChildAnnotFn A P (polyCofreeToShape A P m)
      (fun pos => (polyCofreeGetAnnot A P m pos).val) e ⟨0, PUnit.unit⟩ =
    (polyCofreeGetAnnot A P (m.children b') ⟨0, PUnit.unit⟩).val := by
  intro b'
  simp only [polyCofreeChildAnnotFn]
  simp only [polyCofreeGetAnnot, polyCofreeGetAnnotAt]
  simp only [polyCofreeShapePosToMPosAt]
  simp only [polyCofreeGetAnnotAtM]
  rfl

/--
Build approximations for the backward direction.
Given a shape and annotation function, construct approximations of the
M-type at each depth level.
-/
def polyCofreeFromShapeAndDataApprox (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (n : Nat) : PolyCofixApprox (polyScale A P) n x :=
  match n with
  | 0 => PolyCofixApprox.continue x
  | n + 1 =>
    let root_annot : { a : A.left // A.hom a = x } :=
      ⟨f ⟨0, PUnit.unit⟩, hf ⟨0, PUnit.unit⟩⟩
    let idx : polyBetweenIndex X X (polyScale A P) x := (root_annot, shape.head.2)
    PolyCofixApprox.intro x idx (fun e =>
      polyCofreeFromShapeAndDataApprox A P (shape.children e)
        (polyCofreeChildAnnotFn A P shape f e)
        (polyCofreeChildAnnotFn_fiber A P shape f hf e) n)

/--
Successive approximations from shape and data agree.
-/
lemma polyCofreeFromShapeAndDataApprox_agree (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (n : Nat) :
    PolyCofixAgree (polyScale A P)
      (polyCofreeFromShapeAndDataApprox A P shape f hf n)
      (polyCofreeFromShapeAndDataApprox A P shape f hf (n + 1)) := by
  induction n generalizing x shape f hf with
  | zero => exact PolyCofixAgree.continue x _
  | succ n ih =>
    simp only [polyCofreeFromShapeAndDataApprox]
    apply PolyCofixAgree.intro
    intro e
    exact ih (shape.children e) _ _

/--
Congruence lemma for `polyCofreeFromShapeAndDataApprox`: when shapes are equal
and data functions produce equal values at corresponding positions, the
resulting approximations are equal.
-/
lemma polyCofreeFromShapeAndDataApprox_congr (A : Over X) (P : PolyEndo X)
    {x : X} {s1 s2 : PolyCofreeShape P x} (hs : s1 = s2)
    (f1 : (pos : PolyCofreeAnnotPos P s1) → A.left)
    (f2 : (pos : PolyCofreeAnnotPos P s2) → A.left)
    (hf1 : ∀ pos, A.hom (f1 pos) = PolyCofreeAnnotFiber P s1 pos)
    (hf2 : ∀ pos, A.hom (f2 pos) = PolyCofreeAnnotFiber P s2 pos)
    (hfun : ∀ pos1 pos2, pos1 ≍ pos2 → f1 pos1 = f2 pos2)
    (k : Nat) :
    polyCofreeFromShapeAndDataApprox A P s1 f1 hf1 k =
    polyCofreeFromShapeAndDataApprox A P s2 f2 hf2 k := by
  subst hs
  congr 1
  funext pos
  exact hfun pos pos HEq.rfl

/--
Build the M-type from shape and annotation data.
-/
def polyCofreeFromShapeAndData (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos) :
    PolyCofreeM A P x :=
  ⟨fun n => polyCofreeFromShapeAndDataApprox A P shape f hf n,
    polyCofreeFromShapeAndDataApprox_agree A P shape f hf⟩

/--
Convert a polynomial evaluation form to a cofree comonad value.

The backward direction of the equivalence `PolyCofreeM A P ≃ PolyCofreePolyEval A P`.
-/
def polyCofreePolyEval_to_polyCofreeM (A : Over X) (P : PolyEndo X) {x : X}
    (eval : PolyCofreePolyEval A P x) : PolyCofreeM A P x :=
  polyCofreeFromShapeAndData A P eval.fst eval.snd.left (fun pos => overMor_w eval.snd pos)

/-! ### Roundtrip Proofs -/

/--
Helper: the shape approximations from the backward direction match the
original shape approximations.
-/
lemma polyCofreeFromShapeAndDataApprox_toShape (A : Over X) (P : PolyEndo X)
    {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (n : Nat) :
    polyCofreeApproxToShape A P
      (polyCofreeFromShapeAndDataApprox A P shape f hf n) =
    shape.approx n := by
  induction n generalizing x shape f hf with
  | zero =>
    simp only [polyCofreeFromShapeAndDataApprox, polyCofreeApproxToShape]
    exact (PolyCofixApprox.approx_zero_eq_continue (shape.approx 0)).symm
  | succ n ih =>
    simp only [polyCofreeFromShapeAndDataApprox, polyCofreeApproxToShape]
    have hidx : (shape.approx (n + 1)).getIndex = shape.head := shape.index_eq_head n
    match happ : shape.approx (n + 1) with
    | .intro _ sIdx sChildren =>
      have hIdxEq : sIdx = shape.head := by
        simp only [PolyCofixApprox.getIndex, happ] at hidx
        exact hidx
      subst hIdxEq
      congr 1
      · apply Prod.ext
        · apply Subtype.ext
          simp only [overTerminal, Over.mk_left, Over.mk_hom]
          exact shape.head.1.2.symm
        · rfl
      · funext e
        have ih_e := ih (shape.children e) (polyCofreeChildAnnotFn A P shape f e)
            (polyCofreeChildAnnotFn_fiber A P shape f hf e)
        rw [ih_e]
        simp only [PolyCofix.children, PolyCofix.childApproxAt]
        cases n with
        | zero =>
          simp only [PolyCofix.childApproxAt_zero]
          exact (PolyCofixApprox.approx_zero_eq_continue (sChildren e)).symm
        | succ k =>
          simp only [PolyCofix.childApproxAt_succ]
          have heq1 : (shape.approx (k + 2)).getIndex = shape.head :=
            shape.index_eq_head (k + 1)
          conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
            shape.head (shape.approx (k + 2)) (shape.index_eq_head (k + 1)) heq1 e]
          generalize ha : shape.approx (k + 2) = a at heq1
          rw [happ] at ha
          subst ha
          conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
            shape.head (.intro x shape.head sChildren) _ rfl e]
          rfl

/--
Right inverse: starting from polynomial eval, going to M-type and back
preserves the shape.
-/
lemma polyCofreePolyEval_roundtrip_shape (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos) :
    polyCofreeToShape A P (polyCofreeFromShapeAndData A P shape f hf) = shape := by
  apply PolyCofix.ext
  intro n
  simp only [polyCofreeFromShapeAndData, polyCofreeToShape]
  exact polyCofreeFromShapeAndDataApprox_toShape A P shape f hf n

/--
Congruence of `PolyCofix.children` under HEq of shapes and positions.
If two shapes are HEq and two positions in their respective polynomial families
are HEq, then the children are HEq.
-/
lemma PolyCofix.children_heq {P : PolyEndo X}
    {x1 x2 : X} (hx : x1 = x2)
    {m1 : PolyCofix P x1} {m2 : PolyCofix P x2} (hm : m1 ≍ m2)
    {e1 : (polyBetweenFamily X X P x1 m1.head).left}
    {e2 : (polyBetweenFamily X X P x2 m2.head).left}
    (he : e1 ≍ e2) :
    m1.children e1 ≍ m2.children e2 := by
  subst hx
  have hm_eq : m1 = m2 := eq_of_heq hm
  subst hm_eq
  have he_eq : e1 = e2 := eq_of_heq he
  subst he_eq
  rfl

/--
Extraction from a fiber-transported M-type equals extraction from the
original at HEq positions. Used when relating `h ▸ m` to `m`.
-/
lemma polyCofreeGetAnnotAtM_val_of_eqRec (A : Over X) (P : PolyEndo X)
    {y1 y2 : X} (h : y1 = y2) (m : PolyCofreeM A P y2) (k : Nat)
    (pos_at1 : PolyCofreeAnnotPosAt P (polyCofreeToShape A P (h ▸ m)) k)
    (pos_at2 : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m) k)
    (hpos : pos_at1 ≍ pos_at2) :
    (polyCofreeGetAnnotAtM A P (h ▸ m) k
      (polyCofreeShapePosToMPosAt A P (h ▸ m) k pos_at1)).val =
    (polyCofreeGetAnnotAtM A P m k
      (polyCofreeShapePosToMPosAt A P m k pos_at2)).val := by
  subst h
  have hpos_eq : pos_at1 = pos_at2 := eq_of_heq hpos
  subst hpos_eq
  rfl

/--
Extraction from two M-types equal via fiber transport gives equal values
at HEq positions. This is the applied form of `polyCofreeGetAnnotAtM_val_of_eqRec`.
-/
lemma polyCofreeGetAnnotAtM_val_of_eq (A : Over X) (P : PolyEndo X) {y1 y2 : X}
    (m1 : PolyCofreeM A P y1) (m2 : PolyCofreeM A P y2) (h : y1 = y2)
    (hm : m1 = h ▸ m2) (k : Nat)
    (pos_at1 : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m1) k)
    (pos_at2 : PolyCofreeAnnotPosAt P (polyCofreeToShape A P m2) k)
    (hpos : pos_at1 ≍ pos_at2) :
    (polyCofreeGetAnnotAtM A P m1 k
      (polyCofreeShapePosToMPosAt A P m1 k pos_at1)).val =
    (polyCofreeGetAnnotAtM A P m2 k
      (polyCofreeShapePosToMPosAt A P m2 k pos_at2)).val := by
  subst hm
  exact polyCofreeGetAnnotAtM_val_of_eqRec A P h m2 k pos_at1 pos_at2 hpos

/--
Succ case helper for polyCofreeGetAnnotAtM_fromShapeAndData.
Extracts annotation at depth k+1 from reconstructed M-type.
-/
lemma polyCofreeGetAnnotAtM_fromShapeAndData_succ (A : Over X) (P : PolyEndo X)
    (k : Nat)
    (ih : ∀ {x : X} (shape : PolyCofreeShape P x)
      (f : PolyCofreeAnnotPos P shape → A.left)
      (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
      (pos_at : PolyCofreeAnnotPosAt P
        (polyCofreeToShape A P (polyCofreeFromShapeAndData A P shape f hf)) k),
      let m := polyCofreeFromShapeAndData A P shape f hf
      let hshape := polyCofreePolyEval_roundtrip_shape A P shape f hf
      let pos_m := polyCofreeShapePosToMPosAt A P m k pos_at
      (polyCofreeGetAnnotAtM A P m k pos_m).val =
        f (cast (congrArg (PolyCofreeAnnotPos P) hshape) ⟨k, pos_at⟩))
    {x : X} (shape : PolyCofreeShape P x)
    (f : PolyCofreeAnnotPos P shape → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (pos_at : PolyCofreeAnnotPosAt P
      (polyCofreeToShape A P (polyCofreeFromShapeAndData A P shape f hf)) (k + 1)) :
    let m := polyCofreeFromShapeAndData A P shape f hf
    let hshape := polyCofreePolyEval_roundtrip_shape A P shape f hf
    let pos_m := polyCofreeShapePosToMPosAt A P m (k + 1) pos_at
    (polyCofreeGetAnnotAtM A P m (k + 1) pos_m).val =
      f (cast (congrArg (PolyCofreeAnnotPos P) hshape) ⟨k + 1, pos_at⟩) := by
  intro m hshape pos_m
  obtain ⟨e_shape, rest_pos⟩ := pos_at
  simp only [polyCofreeGetAnnotAtM]
  let e_m := polyCofreeShapePosToMPos A P m e_shape
  let child_m := m.children e_m
  let hfiber := polyCofreeShapePosToMPos_fiber A P m e_shape
  let hshape_children_heq := polyCofreeToShape_children_heq A P m e_shape
  have hshape_child := polyCofreeToShape_children_eq A P m e_shape
  let rest_pos_transported : PolyCofreeAnnotPosAt P
      (polyCofreeToShape A P child_m) k :=
    cast (polyCofreeAnnotPosAt_cast_fiber hfiber hshape_children_heq k) rest_pos
  have hhead_eq : (polyCofreeToShape A P m).head.2 = shape.head.2 :=
    congrArg (fun s => s.head.2) hshape
  have hdom_eq : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left =
      (polyBetweenFamily X X P x shape.head.2).left :=
    congrArg (fun idx => (polyBetweenFamily X X P x idx).left) hhead_eq
  let e' : (polyBetweenFamily X X P x shape.head.2).left := cast hdom_eq e_shape
  have he_heq : e_shape ≍ e' := (cast_heq hdom_eq e_shape).symm
  have hchildren_heq' : (polyCofreeToShape A P m).children e_shape ≍ shape.children e' :=
    PolyCofix.children_heq rfl (heq_of_eq hshape) he_heq
  have hchildren_eq : (polyCofreeToShape A P m).children e_shape = shape.children e' :=
    eq_of_heq hchildren_heq'
  have hrest_cast_eq : PolyCofreeAnnotPosAt P ((polyCofreeToShape A P m).children e_shape) k =
      PolyCofreeAnnotPosAt P (shape.children e') k :=
    congrArg (fun s => PolyCofreeAnnotPosAt P s k) hchildren_eq
  let rest' : PolyCofreeAnnotPosAt P (shape.children e') k := cast hrest_cast_eq rest_pos
  have hf_decomp : f (cast (congrArg (PolyCofreeAnnotPos P) hshape) ⟨k + 1, e_shape, rest_pos⟩) =
      polyCofreeChildAnnotFn A P shape f e' ⟨k, rest'⟩ := by
    simp only [polyCofreeChildAnnotFn]
    congr 1
    -- Show positions are equal as sigma types
    apply Sigma.ext
    · -- First components (depth) are equal
      have h := @sigma_cast_fst_of_outer (PolyCofreeShape P x) (fun _ => Nat)
        (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hshape (k + 1) ⟨e_shape, rest_pos⟩
      exact eq_of_heq h
    · -- Second components (position data) are HEq
      have h := @sigma_cast_snd_heq (PolyCofreeShape P x) (fun _ => Nat)
        (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hshape (k + 1) ⟨e_shape, rest_pos⟩
      -- h : snd ≍ ⟨e_shape, rest_pos⟩, goal: snd ≍ ⟨e', rest'⟩
      -- Need to show ⟨e_shape, rest_pos⟩ ≍ ⟨e', rest'⟩
      have hrest_heq : rest_pos ≍ rest' := (cast_heq hrest_cast_eq rest_pos).symm
      have hpos_heq : (⟨e_shape, rest_pos⟩ : PolyCofreeAnnotPosAt P
          (polyCofreeToShape A P m) (k + 1)) ≍
          (⟨e', rest'⟩ : PolyCofreeAnnotPosAt P shape (k + 1)) :=
        @sigma_heq_of_param_eq (PolyCofreeShape P x)
          (fun s => (polyBetweenFamily X X P x s.head.2).left)
          (fun s e => PolyCofreeAnnotPosAt P (s.children e) k)
          _ _ hshape _ _ he_heq _ _ hrest_heq
      exact HEq.trans h hpos_heq
  rw [hf_decomp]
  have hchild_shape_eq : (polyCofreeToShape A P m).children e_shape = shape.children e' :=
    hchildren_eq
  simp only [polyCofreeChildAnnotFn]
  have hpos_eq : rest' = cast (congrArg (fun s => PolyCofreeAnnotPosAt P s k)
      hchildren_eq) rest_pos := rfl
  rw [hpos_eq]
  have hchild_roundtrip : polyCofreeToShape A P (polyCofreeFromShapeAndData A P
      (shape.children e') (polyCofreeChildAnnotFn A P shape f e')
      (polyCofreeChildAnnotFn_fiber A P shape f hf e')) = shape.children e' :=
    polyCofreePolyEval_roundtrip_shape A P (shape.children e')
      (polyCofreeChildAnnotFn A P shape f e')
      (polyCofreeChildAnnotFn_fiber A P shape f hf e')
  have hshape_to_ih : (polyCofreeToShape A P m).children e_shape =
      polyCofreeToShape A P (polyCofreeFromShapeAndData A P (shape.children e')
        (polyCofreeChildAnnotFn A P shape f e')
        (polyCofreeChildAnnotFn_fiber A P shape f hf e')) :=
    hchildren_eq.trans hchild_roundtrip.symm
  let rest_pos_ih : PolyCofreeAnnotPosAt P (polyCofreeToShape A P (polyCofreeFromShapeAndData
      A P (shape.children e') (polyCofreeChildAnnotFn A P shape f e')
      (polyCofreeChildAnnotFn_fiber A P shape f hf e'))) k :=
    cast (congrArg (fun s => PolyCofreeAnnotPosAt P s k) hshape_to_ih) rest_pos
  have ih_result := ih (shape.children e') (polyCofreeChildAnnotFn A P shape f e')
    (polyCofreeChildAnnotFn_fiber A P shape f hf e') rest_pos_ih
  let child_m' := polyCofreeFromShapeAndData A P (shape.children e')
    (polyCofreeChildAnnotFn A P shape f e')
    (polyCofreeChildAnnotFn_fiber A P shape f hf e')
  simp only [polyCofreeChildAnnotFn] at ih_result ⊢
  have hfiber_eq : (polyBetweenFamily X X (polyScale A P) x (PolyCofix.head m)).hom e_m =
      (polyBetweenFamily X X (polyScale (overTerminal X) P) x (PolyCofix.head shape)).hom e' := by
    simp only [polyBetweenFamily]
    exact hfiber
  have hchild_eq : m.children e_m = hfiber_eq ▸ child_m' := by
    apply PolyCofix.ext
    intro n
    simp only [PolyCofix.children, PolyCofix.childApproxAt]
    cases n with
    | zero =>
      simp only [PolyCofix.childApproxAt_zero]
      rfl
    | succ n =>
      simp only [PolyCofix.childApproxAt_succ]
      rfl
  conv_lhs => simp only [pos_m, polyCofreeShapePosToMPosAt]
  have hcast_fst_heq : (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
      ⟨k, rest_pos_ih⟩).fst ≍ k :=
    @sigma_cast_fst_of_outer (PolyCofreeShape P _) (fun _ => Nat)
      (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hchild_roundtrip k rest_pos_ih
  have hcast_fst : (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
      ⟨k, rest_pos_ih⟩).fst = k := eq_of_heq hcast_fst_heq
  have hcast_snd_heq : (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
      ⟨k, rest_pos_ih⟩).snd ≍ rest_pos_ih :=
    @sigma_cast_snd_heq (PolyCofreeShape P _) (fun _ => Nat)
      (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hchild_roundtrip k rest_pos_ih
  have hrest_pos_ih_heq_rest' : rest_pos_ih ≍ rest' :=
    HEq.trans
      (cast_heq (congrArg (fun s => PolyCofreeAnnotPosAt P s k) hshape_to_ih) rest_pos)
      (HEq.symm (cast_heq hrest_cast_eq rest_pos))
  have hih_rhs : f ⟨(cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
      ⟨k, rest_pos_ih⟩).fst + 1,
      ⟨e', (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
        ⟨k, rest_pos_ih⟩).snd⟩⟩ = f ⟨k + 1, ⟨e', rest'⟩⟩ := by
    congr 1
    have hsnd_heq : (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
        ⟨k, rest_pos_ih⟩).snd ≍ rest' :=
      HEq.trans hcast_snd_heq hrest_pos_ih_heq_rest'
    have hfst_eq : (cast (congrArg (PolyCofreeAnnotPos P) hchild_roundtrip)
        ⟨k, rest_pos_ih⟩).fst + 1 = k + 1 := congrArg (· + 1) hcast_fst
    apply Sigma.ext hfst_eq
    exact @sigma_heq_of_fst_eq_snd_heq Nat
      ((polyBetweenFamily X X P x (PolyCofix.head shape).2).left)
      (fun n e => PolyCofreeAnnotPosAt P (PolyCofix.children shape e) n)
      _ _ hcast_fst _ _ rfl _ _ hsnd_heq
  rw [← hih_rhs]
  have hm_shape_heq : polyCofreeToShape A P (m.children e_m) ≍
      polyCofreeToShape A P child_m' := by
    rw [hchild_eq]
  have hpos_input_heq : (cast (congrArg (fun s => PolyCofreeAnnotPosAt P s k)
      (eq_of_heq hshape_children_heq)) rest_pos) ≍ rest_pos_ih := by
    apply HEq.trans (cast_heq _ rest_pos)
    exact HEq.symm (cast_heq _ rest_pos)
  trans (polyCofreeGetAnnotAtM A P child_m' k
    (polyCofreeShapePosToMPosAt A P child_m' k rest_pos_ih)).val
  · exact polyCofreeGetAnnotAtM_val_of_eq A P (m.children e_m) child_m' hfiber_eq
      hchild_eq k _ _ hpos_input_heq
  · exact ih_result

/--
Extracting annotation at depth n from the reconstructed M-type gives back
the original annotation function value, after appropriate position casting.
-/
lemma polyCofreeGetAnnotAtM_fromShapeAndData (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) → A.left)
    (hf : ∀ pos, A.hom (f pos) = PolyCofreeAnnotFiber P shape pos)
    (n : Nat)
    (pos_at : PolyCofreeAnnotPosAt P
      (polyCofreeToShape A P (polyCofreeFromShapeAndData A P shape f hf)) n) :
    let m := polyCofreeFromShapeAndData A P shape f hf
    let hshape := polyCofreePolyEval_roundtrip_shape A P shape f hf
    let pos_m := polyCofreeShapePosToMPosAt A P m n pos_at
    (polyCofreeGetAnnotAtM A P m n pos_m).val =
    f (cast (congrArg (PolyCofreeAnnotPos P) hshape) ⟨n, pos_at⟩) := by
  induction n generalizing x shape f hf with
  | zero =>
    simp only [polyCofreeShapePosToMPosAt, polyCofreeGetAnnotAtM]
    simp only [polyCofreeFromShapeAndData, PolyCofix.head,
      polyCofreeFromShapeAndDataApprox, PolyCofixApprox.getIndex]
    have hpos_at : pos_at = PUnit.unit := rfl
    subst hpos_at
    have hshape' := polyCofreePolyEval_roundtrip_shape A P shape f hf
    congr 1
    refine Sigma.ext ?_ ?_
    · exact (eq_of_heq (@sigma_cast_fst_of_outer (PolyCofreeShape P x) (fun _ => Nat)
        (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hshape' 0 PUnit.unit)).symm
    · exact HEq.symm (@sigma_cast_snd_heq (PolyCofreeShape P x) (fun _ => Nat)
        (fun s n => PolyCofreeAnnotPosAt P s n) _ _ hshape' 0 PUnit.unit)
  | succ k ih =>
    exact polyCofreeGetAnnotAtM_fromShapeAndData_succ A P k ih shape f hf pos_at

lemma polyCofreePolyEval_roundtrip (A : Over X) (P : PolyEndo X) {x : X}
    (eval : PolyCofreePolyEval A P x) :
    polyCofreeM_to_polyCofreePolyEval A P
      (polyCofreePolyEval_to_polyCofreeM A P eval) = eval := by
  obtain ⟨shape, mor⟩ := eval
  simp only [polyCofreePolyEval_to_polyCofreeM, polyCofreeM_to_polyCofreePolyEval]
  have hshape := polyCofreePolyEval_roundtrip_shape A P shape mor.left
    (fun pos => overMor_w mor pos)
  apply Sigma.ext hshape
  have htype : (polyCofreeFamily P x (polyCofreeToShape A P
      (polyCofreeFromShapeAndData A P shape mor.left
        (fun pos => overMor_w mor pos))) ⟶ A) =
      (polyCofreeFamily P x shape ⟶ A) :=
    congrArg (fun s => polyCofreeFamily P x s ⟶ A) hshape
  refine HEq.trans ?heq1 (cast_heq htype.symm mor)
  apply heq_of_eq
  apply Over.OverMorphism.ext
  funext pos
  simp only [Over.homMk_left]
  have hpos_cast : PolyCofreeAnnotPos P (polyCofreeToShape A P
      (polyCofreeFromShapeAndData A P shape mor.left
        (fun pos => overMor_w mor pos))) =
      PolyCofreeAnnotPos P shape :=
    congrArg (PolyCofreeAnnotPos P) hshape
  simp only [polyCofreeGetAnnot, polyCofreeGetAnnotAt]
  have hval := polyCofreeGetAnnotAtM_fromShapeAndData A P shape mor.left
    (fun pos => overMor_w mor pos) pos.1 pos.2
  rw [hval]
  rw [over_cast_left (congrArg (polyCofreeFamily P x) hshape.symm)]
  simp only [polyCofreeFamily, Over.mk_left]
  rfl

/--
When two family indices are equal, the fiber hom values are equal for
elements related by the induced domain cast.
-/
lemma polyBetweenFamily_hom_eq_of_index_eq {X : Type u} (P : PolyEndo X) {x : X}
    {idx1 idx2 : polyBetweenIndex X X P x}
    (hidx : idx1 = idx2)
    (a : (polyBetweenFamily X X P x idx1).left)
    (b : (polyBetweenFamily X X P x idx2).left)
    (hdom : (polyBetweenFamily X X P x idx1).left =
        (polyBetweenFamily X X P x idx2).left)
    (hab : cast hdom a = b) :
    (polyBetweenFamily X X P x idx1).hom a =
    (polyBetweenFamily X X P x idx2).hom b := by
  subst hidx
  subst hab
  rfl

/--
Codomain type equality for funext_heq_dep when working with polyScale children.
-/
lemma polyCofreeM_roundtrip_codomain_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) (k : Nat)
    (h2' : (polyCofreeToShape A P m).head.2 = (PolyCofix.head m).2)
    (hdom : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left =
        (polyBetweenFamily X X P x (PolyCofix.head m).2).left)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b : (polyBetweenFamily X X P x (PolyCofix.head m).2).left)
    (hab : a ≍ b) :
    PolyCofixApprox (polyScale A P) k
      ((polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a) =
    PolyCofixApprox (polyScale A P) k
      ((polyBetweenFamily X X P x (PolyCofix.head m).2).hom b) := by
  have heq_a_b : cast hdom a = b := cast_eq_iff_heq.mpr hab
  have hfib := polyBetweenFamily_hom_eq_of_index_eq P h2' a b hdom heq_a_b
  exact congrArg (PolyCofixApprox (polyScale A P) k) hfib

/--
HEq of products from component HEqs (same universe).
-/
lemma prod_mk_heq.{w, v} {A1 A2 : Type w} {B1 B2 : Type v}
    {a1 : A1} {a2 : A2} (ha : a1 ≍ a2)
    {b1 : B1} {b2 : B2} (hb : b1 ≍ b2) :
    (a1, b1) ≍ (a2, b2) := by
  cases ha
  cases hb
  rfl

/--
HEq of subtypes when underlying values are equal and predicates are HEq.
-/
lemma subtype_heq_of_val_eq_pred_heq {A : Type*} {P1 P2 : A → Prop}
    {x1 : Subtype P1} {x2 : Subtype P2}
    (hval : x1.val = x2.val)
    (hP : HEq P1 P2) : x1 ≍ x2 := by
  have hPeq : P1 = P2 := eq_of_heq hP
  exact subtype_heq_of_val_eq hPeq hval

/--
HEq of PolyCofix heads from fiber equality and HEq of the full values.
-/
lemma polyCofix_head_heq {P : PolyEndo X} {x1 x2 : X}
    (hx : x1 = x2)
    {m1 : PolyCofix P x1} {m2 : PolyCofix P x2}
    (h : m1 ≍ m2) : PolyCofix.head m1 ≍ PolyCofix.head m2 := by
  subst hx
  exact heq_of_eq (congrArg PolyCofix.head (eq_of_heq h))

/--
HEq of second components of PolyCofreeShape heads.
Uses the specific structure of `polyScale` where the index is a product.
-/
lemma polyCofreeShape_head_snd_heq (_A : Over X) (P : PolyEndo X) {x1 x2 : X}
    (hx : x1 = x2)
    {m1 : PolyCofreeShape P x1} {m2 : PolyCofreeShape P x2}
    (h : m1 ≍ m2) : (PolyCofix.head m1).2 ≍ (PolyCofix.head m2).2 := by
  subst hx
  have h_heads_eq : PolyCofix.head m1 = PolyCofix.head m2 :=
    congrArg PolyCofix.head (eq_of_heq h)
  exact heq_of_eq (congrArg Prod.snd h_heads_eq)

/--
HEq of `PolyCofixApprox.intro` for the same polynomial but different fibers.
When fibers are equal, we can prove HEq using the cast approach.
-/
lemma polyCofixApprox_intro_heq_of_fiber_eq (A : Over X) (P : PolyEndo X)
    {n : Nat} {x y : X} (hxy : x = y)
    (idx1 : polyBetweenIndex X X (polyScale A P) x)
    (idx2 : polyBetweenIndex X X (polyScale A P) y)
    (hidx : idx1 ≍ idx2)
    (f : ∀ e, PolyCofixApprox (polyScale A P) n
        ((polyBetweenFamily X X (polyScale A P) x idx1).hom e))
    (g : ∀ e, PolyCofixApprox (polyScale A P) n
        ((polyBetweenFamily X X (polyScale A P) y idx2).hom e))
    (hfg : ∀ (e1 : (polyBetweenFamily X X (polyScale A P) x idx1).left)
        (e2 : (polyBetweenFamily X X (polyScale A P) y idx2).left),
        e1 ≍ e2 → f e1 ≍ g e2) :
    HEq (PolyCofixApprox.intro x idx1 f)
        (PolyCofixApprox.intro y idx2 g) := by
  subst hxy
  have hidx_eq : idx1 = idx2 := eq_of_heq hidx
  subst hidx_eq
  apply heq_of_eq
  congr 1
  funext e
  exact eq_of_heq (hfg e e HEq.rfl)

/--
HEq of `polyCofreeFromShapeAndDataApprox` when shapes are HEq and annotation
functions correspond. This is the general form needed when working with
children of M-types.
-/
lemma polyCofreeFromShapeAndDataApprox_heq_of_shapes_heq (A : Over X) (P : PolyEndo X)
    {y1 y2 : X} (hy : y1 = y2)
    {shape1 : PolyCofreeShape P y1} {shape2 : PolyCofreeShape P y2}
    (hshape : shape1 ≍ shape2)
    (f1 : PolyCofreeAnnotPos P shape1 → A.left)
    (f2 : PolyCofreeAnnotPos P shape2 → A.left)
    (hf : ∀ (pos1 : PolyCofreeAnnotPos P shape1)
        (pos2 : PolyCofreeAnnotPos P shape2), pos1 ≍ pos2 → f1 pos1 = f2 pos2)
    (hf1 : ∀ pos, A.hom (f1 pos) = PolyCofreeAnnotFiber P shape1 pos)
    (hf2 : ∀ pos, A.hom (f2 pos) = PolyCofreeAnnotFiber P shape2 pos)
    (k : Nat) :
    polyCofreeFromShapeAndDataApprox A P shape1 f1 hf1 k ≍
    polyCofreeFromShapeAndDataApprox A P shape2 f2 hf2 k := by
  subst hy
  have hshape_eq : shape1 = shape2 := eq_of_heq hshape
  subst hshape_eq
  have hf_eq : f1 = f2 := by
    funext pos
    exact hf pos pos HEq.rfl
  subst hf_eq
  rfl

/--
The child shapes have fibers that are equal: from `hfiber` at the parent level,
we derive fiber equality at the child level in the polyScale form.
-/
lemma polyCofreeAnnotPos_fiber_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (_hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b')) :
    (polyBetweenFamily X X (polyScale (overTerminal X) P) x
        (polyCofreeToShape A P m).head).hom a =
    (polyBetweenFamily X X (polyScale A P) x m.head).hom b' := by
  exact hfiber

/--
The head.2 indices of the child shapes are HEq.
-/
lemma polyCofreeAnnotPos_head2_heq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b')) :
    ((polyCofreeToShape A P m).children a).head.2 ≍
    (polyCofreeToShape A P (m.children b')).head.2 := by
  have hfiber_eq := polyCofreeAnnotPos_fiber_eq A P m a b' hfiber hshape12
  exact polyCofreeShape_head_snd_heq (overTerminal X) P hfiber_eq hshape12

/--
The grandchild shapes have equal fibers.
-/
lemma polyCofreeAnnotPos_grandchild_fiber_eq (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b'))
    (e1 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).left)
    (e2 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).left)
    (he12 : e1 ≍ e2) :
    (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).hom e1 =
    (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).hom e2 := by
  have hparent := polyCofreeAnnotPos_fiber_eq A P m a b' hfiber hshape12
  have hhead2 := polyCofreeAnnotPos_head2_heq A P m a b' hfiber hshape12
  exact polyBetweenFamily_hom_eq_of_heq hparent
    ((polyCofreeToShape A P m).children a).head.2
    (polyCofreeToShape A P (m.children b')).head.2
    hhead2 e1 e2 he12

/--
The grandchild shapes are HEq.
-/
lemma polyCofreeAnnotPos_grandchild_shape_heq (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b'))
    (e1 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).left)
    (e2 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).left)
    (he12 : e1 ≍ e2) :
    ((polyCofreeToShape A P m).children a).children e1 ≍
    (polyCofreeToShape A P (m.children b')).children e2 := by
  have hparent := polyCofreeAnnotPos_fiber_eq A P m a b' hfiber hshape12
  exact PolyCofix.children_heq hparent hshape12 he12

/--
The grandchild shape types are equal.
-/
lemma polyCofreeAnnotPos_grandchild_type_eq (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b'))
    (e1 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).left)
    (e2 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).left)
    (he12 : e1 ≍ e2) :
    PolyCofreeShape P (
      (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).hom e1) =
    PolyCofreeShape P (
      (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).hom e2) := by
  have hgc_fiber := polyCofreeAnnotPos_grandchild_fiber_eq A P m a b'
    hfiber hshape12 e1 e2 he12
  exact congrArg (PolyCofreeShape P) hgc_fiber

/--
The position-at families are equal.
-/
lemma polyCofreeAnnotPosAt_family_eq (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (b' : (polyBetweenFamily X X P x m.head.2).left)
    (hfiber : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).hom a =
        (polyBetweenFamily X X P x m.head.2).hom b')
    (hshape12 : (polyCofreeToShape A P m).children a ≍
        polyCofreeToShape A P (m.children b'))
    (e1 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (polyCofreeToShape A P m).head).hom a)
        ((polyCofreeToShape A P m).children a).head.2).left)
    (e2 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x m.head).hom b')
        (polyCofreeToShape A P (m.children b')).head.2).left)
    (he12 : e1 ≍ e2) :
    PolyCofreeAnnotPosAt P (((polyCofreeToShape A P m).children a).children e1) =
    PolyCofreeAnnotPosAt P ((polyCofreeToShape A P (m.children b')).children e2) := by
  have hgc_fiber := polyCofreeAnnotPos_grandchild_fiber_eq A P m a b'
    hfiber hshape12 e1 e2 he12
  have hgc_heq := polyCofreeAnnotPos_grandchild_shape_heq A P m a b'
    hfiber hshape12 e1 e2 he12
  funext n
  exact polyCofreeAnnotPosAt_cast_fiber hgc_fiber hgc_heq n

/--
Descent lemma for annotation extraction: extracting at depth n+1+1 with position
(a, rest) equals extracting at depth n+1 from the child with the transported position.
-/
lemma polyCofreeGetAnnot_descent_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (n : Nat)
    (rest : PolyCofreeAnnotPosAt P ((polyCofreeToShape A P m).children a) n) :
    let b' := polyCofreeShapePosToMPos A P m a
    let hfiber := polyCofreeShapePosToMPos_fiber A P m a
    let hchildren_heq := polyCofreeToShape_children_heq A P m a
    (polyCofreeGetAnnot A P m ⟨n + 1, ⟨a, rest⟩⟩).val =
    (polyCofreeGetAnnotAt A P (m.children b') n
      (cast (polyCofreeAnnotPosAt_cast_fiber hfiber hchildren_heq n) rest)).val := by
  intro b' hfiber hchildren_heq
  simp only [polyCofreeGetAnnot, polyCofreeGetAnnotAt,
    polyCofreeShapePosToMPosAt, polyCofreeGetAnnotAtM]
  rfl

/--
Cast of a sigma type with both component type equalities.
When we have `hE : E1 = E2` and for each `e1 : E1` a proof that `P1 e1 = P2 (cast hE e1)`,
the cast of a sigma decomposes into the casts of components.
-/
lemma sigma_cast_eq_of_component_casts.{v, w} {E1 E2 : Type v} {P1 : E1 → Type w}
    {P2 : E2 → Type w}
    (hE : E1 = E2)
    (hP : ∀ e1 : E1, P1 e1 = P2 (cast hE e1))
    (e1 : E1) (p1 : P1 e1)
    (hsig : (Σ e : E1, P1 e) = (Σ e : E2, P2 e)) :
    cast hsig ⟨e1, p1⟩ = ⟨cast hE e1, cast (hP e1) p1⟩ := by
  cases hE
  simp only [cast_eq] at hP
  have hP' : P1 = P2 := funext hP
  cases hP'
  simp only [cast_eq]

/--
HEq of annotation position sigmas when fibers are equal, shapes are HEq, and
component HEqs hold. Used to show cast of position equals target position.
-/
lemma polyCofreeAnnotPosAt_sigma_heq (P : PolyEndo X)
    {y1 y2 : X} (hy : y1 = y2)
    {s1 : PolyCofreeShape P y1} {s2 : PolyCofreeShape P y2} (hs : s1 ≍ s2)
    {n : Nat}
    {e1 : (polyBetweenFamily X X P y1 s1.head.2).left}
    {e2 : (polyBetweenFamily X X P y2 s2.head.2).left}
    (he : e1 ≍ e2)
    {p1 : PolyCofreeAnnotPosAt P (s1.children e1) n}
    {p2 : PolyCofreeAnnotPosAt P (s2.children e2) n}
    (hp : p1 ≍ p2) :
    (⟨e1, p1⟩ : PolyCofreeAnnotPosAt P s1 (n + 1)) ≍
    (⟨e2, p2⟩ : PolyCofreeAnnotPosAt P s2 (n + 1)) := by
  cases hy
  cases hs
  cases he
  cases hp
  rfl

lemma polyCofreeGetAnnot_parent_child_eq (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x
        (PolyCofix.head (polyCofreeToShape A P m)).2).left)
    (e1 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (PolyCofix.head (polyCofreeToShape A P m))).hom a)
        ((polyCofreeToShape A P m).children a).head.2).left)
    (e2 : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x (PolyCofix.head m)).hom
          (polyCofreeShapePosToMPos A P m a))
        (polyCofreeToShape A P (m.children
          (polyCofreeShapePosToMPos A P m a))).head.2).left)
    (he12 : e1 ≍ e2)
    (pos1 : PolyCofreeAnnotPos P (((polyCofreeToShape A P m).children a).children e1))
    (pos2 : PolyCofreeAnnotPos P ((polyCofreeToShape A P (m.children
        (polyCofreeShapePosToMPos A P m a))).children e2))
    (hpos12 : pos1 ≍ pos2) :
    let b' := polyCofreeShapePosToMPos A P m a
    (polyCofreeGetAnnot A P m ⟨pos1.fst + 1 + 1, ⟨a, ⟨e1, pos1.snd⟩⟩⟩).val =
    (polyCofreeGetAnnot A P (m.children b') ⟨pos2.fst + 1, ⟨e2, pos2.snd⟩⟩).val := by
  intro b'
  let hfiber := polyCofreeShapePosToMPos_fiber A P m a
  let hchildren_heq := polyCofreeToShape_children_heq A P m a
  let shape1 := (polyCofreeToShape A P m).children a
  let shape2 := polyCofreeToShape A P (m.children b')
  have hhead2_heq : shape1.head.2 ≍ shape2.head.2 :=
    polyCofreeShape_head_snd_heq (overTerminal X) P hfiber hchildren_heq
  have hgrandchild_fiber : (polyBetweenFamily X X P _ shape1.head.2).hom e1 =
      (polyBetweenFamily X X P _ shape2.head.2).hom e2 :=
    polyBetweenFamily_hom_eq_of_heq hfiber shape1.head.2 shape2.head.2 hhead2_heq e1 e2 he12
  have hgrandchild_heq : shape1.children e1 ≍ shape2.children e2 :=
    PolyCofix.children_heq hfiber hchildren_heq he12
  have hfamily_eq : (fun n => PolyCofreeAnnotPosAt P (shape1.children e1) n) =
      (fun n => PolyCofreeAnnotPosAt P (shape2.children e2) n) := by
    funext n
    exact polyCofreeAnnotPosAt_cast_fiber hgrandchild_fiber hgrandchild_heq n
  obtain ⟨n1, pos1_snd⟩ := pos1
  obtain ⟨n2, pos2_snd⟩ := pos2
  have hfst : n1 = n2 := sigma_fst_heq_eq hfamily_eq hpos12
  have hsnd_heq : pos1_snd ≍ pos2_snd := sigma_snd_heq_of_heq_same_index hfamily_eq hpos12
  subst hfst
  have htype_eq : (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (PolyCofix.head (polyCofreeToShape A P m))).hom a)
        shape1.head.2).left =
      (polyBetweenFamily X X P
        ((polyBetweenFamily X X (polyScale A P) x (PolyCofix.head m)).hom b')
        shape2.head.2).left :=
    eq_of_heq (polyBetweenFamily_left_heq hfiber shape1.head.2 shape2.head.2 hhead2_heq)
  have he12_eq : cast htype_eq e1 = e2 :=
    eq_of_heq ((cast_heq htype_eq e1).trans he12)
  have hpos_type_eq := polyCofreeAnnotPosAt_cast_fiber hgrandchild_fiber hgrandchild_heq n1
  have hpos_cast_eq : cast hpos_type_eq pos1_snd = pos2_snd :=
    eq_of_heq ((cast_heq hpos_type_eq pos1_snd).trans hsnd_heq)
  have hcast := polyCofreeAnnotPosAt_cast_fiber hfiber hchildren_heq (n1 + 1)
  have h1 : (polyCofreeGetAnnot A P m ⟨n1 + 1 + 1, ⟨a, ⟨e1, pos1_snd⟩⟩⟩).val =
      (polyCofreeGetAnnotAt A P (m.children b') (n1 + 1)
        (cast hcast ⟨e1, pos1_snd⟩)).val :=
    polyCofreeGetAnnot_descent_eq A P m a (n1 + 1) ⟨e1, pos1_snd⟩
  have h2 : cast hcast ⟨e1, pos1_snd⟩ = ⟨e2, pos2_snd⟩ := by
    have heq_sig : (⟨e1, pos1_snd⟩ : PolyCofreeAnnotPosAt P shape1 (n1 + 1)) ≍
        (⟨e2, pos2_snd⟩ : PolyCofreeAnnotPosAt P shape2 (n1 + 1)) :=
      polyCofreeAnnotPosAt_sigma_heq P hfiber hchildren_heq he12 hsnd_heq
    exact eq_of_heq ((cast_heq _ _).trans heq_sig)
  rw [h1, h2]
  rfl

/--
HEq of approximations when shape children are HEq and annotation functions correspond.
Used to relate `polyCofreeChildAnnotFn` on a shape to `polyCofreeGetAnnot` on the child.

The induction generalizes over `x`, `m`, and `a` so that in the successor case
we can apply the induction hypothesis to children of `m`.
-/
lemma polyCofreeFromShapeAndData_children_approx_heq (A : Over X) (P : PolyEndo X)
    {x : X} (m : PolyCofreeM A P x)
    (a : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left)
    (k : Nat) :
    let b' := polyCofreeShapePosToMPos A P m a
    polyCofreeFromShapeAndDataApprox A P
      ((polyCofreeToShape A P m).children a)
      (polyCofreeChildAnnotFn A P (polyCofreeToShape A P m)
        (fun pos => (polyCofreeGetAnnot A P m pos).val) a)
      (polyCofreeChildAnnotFn_fiber A P (polyCofreeToShape A P m)
        (fun pos => (polyCofreeGetAnnot A P m pos).val)
        (fun pos => (polyCofreeGetAnnot A P m pos).property) a) k ≍
    polyCofreeFromShapeAndDataApprox A P
      (polyCofreeToShape A P (m.children b'))
      (fun pos => (polyCofreeGetAnnot A P (m.children b') pos).val)
      (fun pos => (polyCofreeGetAnnot A P (m.children b') pos).property) k := by
  intro b'
  have hchildren_heq := polyCofreeToShape_children_heq A P m a
  have hfiber := polyCofreeShapePosToMPos_fiber A P m a
  induction k generalizing x m a with
  | zero =>
    simp only [polyCofreeFromShapeAndDataApprox]
    exact PolyCofixApprox.continue_heq hfiber
  | succ k' ih =>
    simp only [polyCofreeFromShapeAndDataApprox]
    let shape1 := (polyCofreeToShape A P m).children a
    let shape2 := polyCofreeToShape A P (m.children b')
    have hannot_eq := polyCofreeChildAnnotFn_zero_eq_childRoot A P m a
    have hshape1_head2_heq : (PolyCofix.head shape1).2 ≍ (PolyCofix.head shape2).2 :=
      polyCofreeShape_head_snd_heq (overTerminal X) P hfiber hchildren_heq
    have h_pred_eq : (fun aa => A.hom aa =
        (polyBetweenFamily X X (polyScale (overTerminal X) P) x
          (PolyCofix.head (polyCofreeToShape A P m))).hom a) =
        (fun aa => A.hom aa =
          (polyBetweenFamily X X (polyScale A P) x (PolyCofix.head m)).hom b') := by
      funext aa
      exact congrArg (A.hom aa = ·) hfiber
    have h_annot_heq : (⟨polyCofreeChildAnnotFn A P (polyCofreeToShape A P m)
            (fun pos => (polyCofreeGetAnnot A P m pos).val) a ⟨0, PUnit.unit⟩,
          polyCofreeChildAnnotFn_fiber A P (polyCofreeToShape A P m)
            (fun pos => (polyCofreeGetAnnot A P m pos).val)
            (fun pos => (polyCofreeGetAnnot A P m pos).property) a ⟨0, PUnit.unit⟩⟩ :
        { aa : A.left // A.hom aa = _ }) ≍
        (⟨(polyCofreeGetAnnot A P (m.children b') ⟨0, PUnit.unit⟩).val,
          (polyCofreeGetAnnot A P (m.children b') ⟨0, PUnit.unit⟩).property⟩ :
        { aa : A.left // A.hom aa = _ }) := by
      apply subtype_heq_of_val_eq_pred_heq hannot_eq
      exact heq_of_eq h_pred_eq
    have h_idx_heq := prod_mk_heq h_annot_heq hshape1_head2_heq
    apply polyCofixApprox_intro_heq_of_fiber_eq A P hfiber
      (⟨polyCofreeChildAnnotFn A P (polyCofreeToShape A P m)
          (fun pos => (polyCofreeGetAnnot A P m pos).val) a ⟨0, PUnit.unit⟩,
        polyCofreeChildAnnotFn_fiber A P (polyCofreeToShape A P m)
          (fun pos => (polyCofreeGetAnnot A P m pos).val)
          (fun pos => (polyCofreeGetAnnot A P m pos).property) a ⟨0, PUnit.unit⟩⟩,
        shape1.head.2)
      (⟨(polyCofreeGetAnnot A P (m.children b') ⟨0, PUnit.unit⟩).val,
        (polyCofreeGetAnnot A P (m.children b') ⟨0, PUnit.unit⟩).property⟩,
        (PolyCofix.head shape2).2)
      h_idx_heq
    intro e1 e2 he12
    have hchildren_shape_heq : shape1.children e1 ≍ shape2.children e2 :=
      PolyCofix.children_heq hfiber hchildren_heq he12
    have hchildren_fiber : (polyBetweenFamily X X P _ shape1.head.2).hom e1 =
        (polyBetweenFamily X X P _ shape2.head.2).hom e2 :=
      polyBetweenFamily_hom_eq_of_heq hfiber shape1.head.2 shape2.head.2
        hshape1_head2_heq e1 e2 he12
    apply polyCofreeFromShapeAndDataApprox_heq_of_shapes_heq A P hchildren_fiber
      hchildren_shape_heq
    intro pos1 pos2 hpos12
    -- Both extractions trace to the same position in m.
    -- LHS: (polyCofreeGetAnnot A P m ⟨pos1.fst+2, ⟨a, ⟨e1, pos1.snd⟩⟩⟩).val
    -- RHS: (polyCofreeGetAnnot A P (m.children b') ⟨pos2.fst+1, ⟨e2, pos2.snd⟩⟩).val
    -- RHS unfolds to extraction from m at shifted position
    simp only [polyCofreeChildAnnotFn]
    exact polyCofreeGetAnnot_parent_child_eq A P m a e1 e2 he12 pos1 pos2 hpos12

/--
Children HEq helper for polyCofreeM_roundtrip succ case.
Relates polyCofreeFromShapeAndDataApprox on shape children to M-type children.
-/
lemma polyCofreeM_roundtrip_children_heq (A : Over X) (P : PolyEndo X)
    (k : Nat)
    (ih : ∀ {x : X} (m : PolyCofreeM A P x),
      polyCofreeFromShapeAndDataApprox A P (polyCofreeToShape A P m)
        (fun pos => (polyCofreeGetAnnot A P m pos).val)
        (fun pos => (polyCofreeGetAnnot A P m pos).property) k = m.approx k)
    {x : X} (m : PolyCofreeM A P x)
    (childFun : (e : (polyBetweenFamily X X (polyScale A P) x
        (PolyCofix.head m)).left) →
      PolyCofixApprox (polyScale A P) k
        ((polyBetweenFamily X X (polyScale A P) x (PolyCofix.head m)).hom e))
    (ha : m.approx (k + 1) = PolyCofixApprox.intro x (PolyCofix.head m) childFun)
    (_h2' : (PolyCofix.head (polyCofreeToShape A P m)).2 = (PolyCofix.head m).2)
    (_hdom : (polyBetweenFamily X X P x
        (PolyCofix.head (polyCofreeToShape A P m)).2).left =
      (polyBetweenFamily X X P x (PolyCofix.head m).2).left)
    (a : (polyBetweenFamily X X P x
        (PolyCofix.head (polyCofreeToShape A P m)).2).left)
    (b : (polyBetweenFamily X X P x (PolyCofix.head m).2).left)
    (hab : a ≍ b) :
    polyCofreeFromShapeAndDataApprox A P
      (PolyCofix.children (polyCofreeToShape A P m) a)
      (polyCofreeChildAnnotFn A P (polyCofreeToShape A P m)
        (fun pos => (polyCofreeGetAnnot A P m pos).val) a)
      (polyCofreeChildAnnotFn_fiber A P (polyCofreeToShape A P m)
        (fun pos => (polyCofreeGetAnnot A P m pos).val)
        (fun pos => (polyCofreeGetAnnot A P m pos).property) a) k ≍
    childFun b := by
  let b' := polyCofreeShapePosToMPos A P m a
  have hab' : a ≍ b' := polyCofreeShapePosToMPos_heq A P m a
  have hb'b : b' = b := eq_of_heq (hab'.symm.trans hab)
  subst hb'b
  have hfiber := polyCofreeShapePosToMPos_fiber A P m a
  have hchildren_heq := polyCofreeToShape_children_heq A P m a
  have ih_child := ih (m.children b')
  have hchildApprox : (m.children b').approx k = childFun b' := by
    simp only [PolyCofix.children, PolyCofix.childApproxAt]
    cases k with
    | zero =>
      simp only [PolyCofix.childApproxAt_zero]
      have hcf : childFun b' = .continue _ :=
        PolyCofixApprox.approx_zero_eq_continue _
      rw [hcf]
    | succ k' =>
      simp only [PolyCofix.childApproxAt_succ]
      have heq1 : (m.approx (k' + 2)).getIndex = m.head := m.index_eq_head (k' + 1)
      conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head
        (m.approx (k' + 2)) (m.index_eq_head (k' + 1)) heq1 b']
      generalize haa : m.approx (k' + 2) = aa at heq1
      rw [ha] at haa
      subst haa
      conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head
        (.intro x m.head childFun) heq1 rfl b']
      exact PolyCofix.childApproxAt_succ_aux_intro m.head childFun b'
  rw [← hchildApprox, ← ih_child]
  have hfiber' := polyCofreeShapePosToMPos_fiber A P m a
  apply polyCofreeFromShapeAndData_children_approx_heq A P m a k

/--
Left inverse: starting from M-type, going to polynomial eval and back
gives the original M-type.
-/
lemma polyCofreeM_roundtrip (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) :
    polyCofreePolyEval_to_polyCofreeM A P
      (polyCofreeM_to_polyCofreePolyEval A P m) = m := by
  simp only [polyCofreePolyEval_to_polyCofreeM, polyCofreeM_to_polyCofreePolyEval]
  apply PolyCofix.ext
  intro n
  simp only [polyCofreeFromShapeAndData]
  induction n generalizing x m with
  | zero =>
    simp only [polyCofreeFromShapeAndDataApprox]
    exact (PolyCofixApprox.approx_zero_eq_continue (m.approx 0)).symm
  | succ k ih =>
    simp only [polyCofreeFromShapeAndDataApprox]
    have hidx_eq : (m.approx (k + 1)).getIndex = m.head := m.index_eq_head k
    generalize ha : m.approx (k + 1) = a at hidx_eq
    match a, hidx_eq with
    | .intro _ idx childFun, hidx_eq =>
      subst hidx_eq
      congr 1
      · have h1 : (polyCofreeGetAnnot A P m ⟨0, PUnit.unit⟩).val = m.head.1.val := by
          simp only [polyCofreeGetAnnot, polyCofreeGetAnnotAt, polyCofreeShapePosToMPosAt,
            polyCofreeGetAnnotAtM]
        have h2 : (polyCofreeToShape A P m).head.2 = m.head.2 :=
          polyCofreeToShape_head_index A P m
        apply Prod.ext
        · apply Subtype.ext
          exact h1
        · exact h2
      · have h2' : (polyCofreeToShape A P m).head.2 = (PolyCofix.head m).2 :=
          polyCofreeToShape_head_index A P m
        have hdom : (polyBetweenFamily X X P x (polyCofreeToShape A P m).head.2).left =
            (polyBetweenFamily X X P x (PolyCofix.head m).2).left :=
          congrArg (fun idx => (polyBetweenFamily X X P x idx).left) h2'
        apply funext_heq_dep hdom
        · intro a b hab
          exact polyCofreeM_roundtrip_codomain_eq A P m k h2' hdom a b hab
        · intro a b hab
          exact polyCofreeM_roundtrip_children_heq A P k ih m childFun ha h2'
            hdom a b hab

/--
Auxiliary lemma: approximations at depth k are equal when shapes are HEq
and annotations match at corresponding positions. This lemma is useful for
proving M-type equality when both shape and annotation data are known to match.
-/
lemma polyCofreeApprox_eq_of_shape_annot_match (A : Over X) (P : PolyEndo X)
    (k : Nat) :
    ∀ {y : X} (m1 m2 : PolyCofreeM A P y),
      polyCofreeToShape A P m1 ≍ polyCofreeToShape A P m2 →
      (∀ (pos1 : PolyCofreeAnnotPos P (polyCofreeToShape A P m1))
          (pos2 : PolyCofreeAnnotPos P (polyCofreeToShape A P m2)),
          pos1 ≍ pos2 → (polyCofreeGetAnnot A P m1 pos1).val =
            (polyCofreeGetAnnot A P m2 pos2).val) →
      m1.approx k = m2.approx k := by
  intro y m1 m2 hshape hannot
  have hshape_eq : polyCofreeToShape A P m1 = polyCofreeToShape A P m2 :=
    eq_of_heq hshape
  have hrt1 := polyCofreeM_roundtrip A P m1
  have hrt2 := polyCofreeM_roundtrip A P m2
  simp only [polyCofreePolyEval_to_polyCofreeM, polyCofreeM_to_polyCofreePolyEval] at hrt1 hrt2
  rw [← hrt1, ← hrt2]
  simp only [polyCofreeFromShapeAndData]
  refine polyCofreeFromShapeAndDataApprox_congr A P hshape_eq _ _ _ _ ?_ k
  exact hannot

/--
The equivalence between the cofree comonad M-type and its polynomial
evaluation form (shape + annotation data).

This formalizes that the M-type of `polyScale A P` decomposes as:
- A shape (M-type of `polyScale (overTerminal X) P`)
- An annotation function from positions to A-values with fiber conditions
-/
def polyCofreeEquiv (A : Over X) (P : PolyEndo X) (x : X) :
    PolyCofreeM A P x ≃ PolyCofreePolyEval A P x where
  toFun := polyCofreeM_to_polyCofreePolyEval A P
  invFun := polyCofreePolyEval_to_polyCofreeM A P
  left_inv := polyCofreeM_roundtrip A P
  right_inv := polyCofreePolyEval_roundtrip A P

/--
Evaluating the cofree comonad polynomial at the terminal object gives an
equivalence with the shape type (positions of the polynomial).

Since `PolyCofreeShape P x = PolyCofreeM (overTerminal X) P x`, this is an
instance of `polyCofreeEquiv` at the terminal object.
-/
def polyCofreeTerminalEvalEquiv (P : PolyEndo X) (x : X) :
    PolyCofreeShape P x ≃ PolyCofreePolyEval (overTerminal X) P x :=
  polyCofreeEquiv (overTerminal X) P x

/--
Evaluating the cofree comonad polynomial at the initial object gives an
empty type.

Since `PolyCofreeM (overInitial X) P x` is empty (there's no way to annotate
nodes with elements of the empty type), the polynomial evaluation is also
empty via `polyCofreeEquiv`.
-/
instance polyCofreeInitialEvalIsEmpty (P : PolyEndo X) (x : X) :
    IsEmpty (PolyCofreePolyEval (overInitial X) P x) :=
  (polyCofreeEquiv (overInitial X) P x).symm.isEmpty

/--
The cofree comonad polynomial evaluated at the initial object is equivalent
to `PEmpty`.
-/
def polyCofreeInitialEvalEquivPEmpty (P : PolyEndo X) (x : X) :
    PolyCofreePolyEval (overInitial X) P x ≃ PEmpty :=
  Equiv.equivPEmpty _

end FreeMonadCofreeComonad

/-! ## Free and Cofree Adjunctions

The free P-algebra functor is left adjoint to the forgetful functor.
The cofree P-coalgebra functor is right adjoint to the forgetful functor.
-/

section Adjunctions

variable {X : Type u}

/-! ### Free Algebra Structure

For an object `A : Over X`, the free P-algebra on A has:
- Carrier: `PolyFreeM A P` (P-branching trees with A-labeled leaves)
- Structure map: fold a P-node with tree children into a tree with node index
-/

/--
Given an element of the polynomial P evaluated at the free monad carrier,
construct the corresponding element of the free monad.

The input is a P-index `i` together with a morphism from the family at `i`
to `polyFreeMCarrier A P`. The output is a PolyFreeM node with index `Sum.inr i`
and children extracted from the morphism.
-/
def polyFreeMStrFamily (A : Over X) (P : PolyEndo X) (x : X)
    (elem : polyBetweenEvalFamily X X P (polyFreeMCarrier A P) x) :
    PolyFreeM A P x :=
  let i := pbefIndex elem
  let childMor := pbefMor elem
  PolyFix.mk x (Sum.inr i) (fun e =>
    let child := childMor.left e
    let fiber_eq : child.1 = (polyBetweenFamily X X P x i).hom e :=
      congrFun (Over.w childMor) e
    fiber_eq ▸ child.2)

/--
The left component of the structure map for the free algebra.
-/
def polyFreeMStrLeft (A : Over X) (P : PolyEndo X) :
    ((polyEndoFunctor X P).obj (polyFreeMCarrier A P)).left →
    (polyFreeMCarrier A P).left :=
  fun ⟨x, elem⟩ => ⟨x, polyFreeMStrFamily A P x elem⟩

/--
The structure map commutes with the fiber projections.
-/
lemma polyFreeMStr_comm (A : Over X) (P : PolyEndo X) :
    polyFreeMStrLeft A P ≫ (polyFreeMCarrier A P).hom =
    ((polyEndoFunctor X P).obj (polyFreeMCarrier A P)).hom := rfl

/--
The structure map for the free P-algebra on A.

This takes a P-shaped structure with `PolyFreeM A P` children and produces
a `PolyFreeM A P` node by wrapping with the `Sum.inr` index.
-/
def polyFreeMStr (A : Over X) (P : PolyEndo X) :
    (polyEndoFunctor X P).obj (polyFreeMCarrier A P) ⟶ polyFreeMCarrier A P :=
  Over.homMk (polyFreeMStrLeft A P) (polyFreeMStr_comm A P)

/--
The free P-algebra on an object A : Over X.

The carrier is `polyFreeMCarrier A P` (trees with A-leaves).
The structure map folds a P-node into a tree.
-/
def polyFreeAlg (A : Over X) (P : PolyEndo X) : PolyAlg P where
  a := polyFreeMCarrier A P
  str := polyFreeMStr A P

/-! ### Free Functor on Morphisms

Given `f : A ⟶ B` in `Over X`, we get an algebra homomorphism from the free
algebra on A to the free algebra on B by mapping leaves: each A-leaf is
replaced by the corresponding B-leaf via f.
-/

/--
The fiber proof for mapping a leaf: if `a` is in fiber over `y` in A,
then `f.left a` is in fiber over `y` in B.
-/
lemma polyFreeMap_fiber_eq (A B : Over X) (f : A ⟶ B) {y : X}
    (a : { v : A.left // A.hom v = y }) : B.hom (f.left a.val) = y := by
  have hw := Over.w f
  calc B.hom (f.left a.val) = (f.left ≫ B.hom) a.val := rfl
    _ = A.hom a.val := congrFun hw a.val
    _ = y := a.property

def polyFreeMapAt (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) (x : X)
    (t : PolyFreeM A P x) : PolyFreeM B P x :=
  polyFreeMBind A B P t (fun _ a =>
    polyFreeMPure B P ⟨f.left a.val, polyFreeMap_fiber_eq A B f a⟩)

/--
The free functor map on the left component of carriers.
-/
def polyFreeMapLeft (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    (polyFreeMCarrier A P).left → (polyFreeMCarrier B P).left :=
  fun ⟨x, t⟩ => ⟨x, polyFreeMapAt A B P f x t⟩

/--
The free functor map commutes with fiber projections.
-/
lemma polyFreeMap_comm (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyFreeMapLeft A B P f ≫ (polyFreeMCarrier B P).hom =
    (polyFreeMCarrier A P).hom := rfl

/--
The free functor map as a morphism in `Over X`.
-/
def polyFreeMap (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyFreeMCarrier A P ⟶ polyFreeMCarrier B P :=
  Over.homMk (polyFreeMapLeft A B P f) (polyFreeMap_comm A B P f)

/--
Transport of a PolyFreeM value commutes with polyFreeMapAt.

When we transport a tree to a different fiber and then apply the map,
it's the same as first applying the map and then transporting.
-/
lemma polyFreeMapAt_transport (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x y : X} (hxy : x = y) (t : PolyFreeM A P x) :
    polyFreeMapAt A B P f y (hxy ▸ t) = hxy ▸ polyFreeMapAt A B P f x t := by
  subst hxy
  rfl

/--
Transport commutes with polyFreeMBind when the bind function respects fibers.
-/
lemma polyFreeMBind_transport (A B : Over X) (P : PolyEndo X)
    {x y : X} (hxy : x = y) (t : PolyFreeM A P x)
    (g : ∀ z, { a : A.left // A.hom a = z } → PolyFreeM B P z) :
    hxy ▸ polyFreeMBind A B P t g = polyFreeMBind A B P (hxy ▸ t) g := by
  subst hxy
  rfl

/--
Matching a sigma to apply a function to its second component and then
extracting snd gives the same as applying the function directly to snd.
-/
lemma sigma_match_snd {I : Type*} {F G : I → Type*}
    (f : ∀ i, F i → G i) (p : Σ i, F i) :
    (match p with | ⟨i, x⟩ => ⟨i, f i x⟩ : Σ i, G i).snd = f p.fst p.snd := rfl

/--
The effect of mapping a tree through polyFreeMapAt.

When we apply the map to a tree in a fiber y, and then transport to fiber x
(where y = x by the Over morphism), it equals applying polyFreeMBind
to the transported tree.
-/
lemma polyFreeMapAt_as_bind (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x y : X} (hxy : y = x) (t : PolyFreeM A P y) :
    hxy ▸ polyFreeMapAt A B P f y t =
    polyFreeMBind A B P (hxy ▸ t)
      (fun _ a => polyFreeMPure B P ⟨f.left a.val, polyFreeMap_fiber_eq A B f a⟩) := by
  subst hxy
  rfl

lemma polyFreeMapHom_comm (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    (polyEndoFunctor X P).map (polyFreeMap A B P f) ≫ polyFreeMStr B P =
    polyFreeMStr A P ≫ polyFreeMap A B P f := by
  apply Over.OverMorphism.ext
  funext ⟨x, elem⟩
  simp only [Over.comp_left, polyFreeMStr, Over.homMk_left, polyFreeMap,
    polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap]
  unfold polyFreeMStrLeft polyFreeMapLeft polyFreeMStrFamily
  simp only [types_comp_apply]
  obtain ⟨i, h⟩ := elem
  simp only [pbefIndex, pbefMor, ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor]
  simp only [Over.comp_left, Over.homMk_left]
  congr 1
  congr 1
  funext e
  simp only [types_comp_apply]
  unfold polyFreeMapAt
  rw [← polyFreeMBind_transport]
  rfl

/--
The free functor map as an algebra homomorphism.
-/
def polyFreeAlgMap (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyFreeAlg A P ⟶ polyFreeAlg B P where
  f := polyFreeMap A B P f
  h := polyFreeMapHom_comm A B P f

/--
Mapping by the identity morphism is the identity on trees.
-/
lemma polyFreeMapAt_id (A : Over X) (P : PolyEndo X) (x : X) (t : PolyFreeM A P x) :
    polyFreeMapAt A A P (𝟙 A) x t = t := by
  unfold polyFreeMapAt
  simp only [Over.id_left]
  convert polyFreeM_bind_pure A P t using 2

/--
The free functor map preserves identity morphisms in Over X.
-/
lemma polyFreeMap_id (A : Over X) (P : PolyEndo X) :
    polyFreeMap A A P (𝟙 A) = 𝟙 (polyFreeMCarrier A P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [polyFreeMap, Over.homMk_left, polyFreeMapLeft, Over.id_left,
    polyFreeMapAt_id, types_id_apply]

/--
Mapping by a composition equals the composition of maps.
-/
lemma polyFreeMapAt_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) (x : X) (t : PolyFreeM A P x) :
    polyFreeMapAt A C P (f ≫ g) x t =
    polyFreeMapAt B C P g x (polyFreeMapAt A B P f x t) := by
  unfold polyFreeMapAt
  rw [polyFreeM_bind_assoc]
  simp only [polyFreeM_pure_bind, Over.comp_left, types_comp_apply]

/--
The free functor map preserves composition in Over X.
-/
lemma polyFreeMap_comp (A B C : Over X) (P : PolyEndo X) (f : A ⟶ B) (g : B ⟶ C) :
    polyFreeMap A C P (f ≫ g) = polyFreeMap A B P f ≫ polyFreeMap B C P g := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [polyFreeMap, Over.homMk_left, polyFreeMapLeft, Over.comp_left,
    polyFreeMapAt_comp, types_comp_apply]

/--
The free functor on algebra homomorphisms preserves identity.
-/
lemma polyFreeAlgMap_id (A : Over X) (P : PolyEndo X) :
    polyFreeAlgMap A A P (𝟙 A) = 𝟙 (polyFreeAlg A P) := by
  apply Endofunctor.Algebra.Hom.ext
  exact polyFreeMap_id A P

/--
The free functor on algebra homomorphisms preserves composition.
-/
lemma polyFreeAlgMap_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) :
    polyFreeAlgMap A C P (f ≫ g) = polyFreeAlgMap A B P f ≫ polyFreeAlgMap B C P g := by
  apply Endofunctor.Algebra.Hom.ext
  exact polyFreeMap_comp A B C P f g

/--
The free functor from Over X to PolyAlg P.

This sends an object A to the free P-algebra on A (carrier = trees with A-leaves),
and a morphism f : A ⟶ B to the algebra homomorphism that maps leaves via f.
-/
def polyFreeFunctor (P : PolyEndo X) : Over X ⥤ PolyAlg P where
  obj := fun A => polyFreeAlg A P
  map := fun f => polyFreeAlgMap _ _ P f
  map_id := fun A => polyFreeAlgMap_id A P
  map_comp := fun f g => polyFreeAlgMap_comp _ _ _ P f g

/--
The forgetful functor from P-algebras to Over X.
This is just mathlib's Endofunctor.Algebra.forget applied to polyEndoFunctor.
-/
abbrev polyForgetFunctor (P : PolyEndo X) : PolyAlg P ⥤ Over X :=
  Endofunctor.Algebra.forget (polyEndoFunctor X P)

/-! ### Unit: Embedding as Leaves

The unit of the adjunction embeds an element of A as a leaf in the free algebra.
-/

/--
The left component of the unit: embeds elements of A.left as leaves.
-/
def polyFreeUnitLeft (A : Over X) (P : PolyEndo X) :
    A.left → (polyFreeMCarrier A P).left :=
  fun a => ⟨A.hom a, polyFreeMPure A P ⟨a, rfl⟩⟩

/--
The unit morphism preserves fiber projections.
-/
lemma polyFreeUnit_comm (A : Over X) (P : PolyEndo X) :
    polyFreeUnitLeft A P ≫ (polyFreeMCarrier A P).hom = A.hom := rfl

/--
The unit of the Free ⊣ Forget adjunction at object A.

This embeds elements of A as single-leaf trees in the free algebra.
-/
def polyFreeUnit (A : Over X) (P : PolyEndo X) :
    A ⟶ (polyForgetFunctor P).obj (polyFreeAlg A P) :=
  Over.homMk (polyFreeUnitLeft A P) (polyFreeUnit_comm A P)

/--
The unit is natural in A.
-/
lemma polyFreeUnit_naturality (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    f ≫ polyFreeUnit B P =
    polyFreeUnit A P ≫ (polyForgetFunctor P).map (polyFreeAlgMap A B P f) := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, polyFreeUnit, Over.homMk_left, polyFreeUnitLeft,
    polyForgetFunctor, Endofunctor.Algebra.forget_map, polyFreeAlgMap,
    polyFreeMap, polyFreeMapLeft, types_comp_apply]
  simp only [polyFreeMapAt]
  have hfib : B.hom (f.left a) = A.hom a := congrFun (Over.w f) a
  simp only [polyFreeMBind, polyFreeMPure]
  apply Sigma.ext hfib
  exact polyFreeMPure_fiber_heq B P hfib (f.left a) rfl hfib

/--
The unit as a natural transformation from the identity to Forget ∘ Free.
-/
def polyFreeUnitNat (P : PolyEndo X) :
    𝟭 (Over X) ⟶ polyFreeFunctor P ⋙ polyForgetFunctor P where
  app := fun A => polyFreeUnit A P
  naturality := fun A B f => polyFreeUnit_naturality A B P f

/-! #### Counit: Fold from Free Algebra to Target Algebra

The counit of the Free ⊣ Forget adjunction, at each algebra α,
is a homomorphism from Free(Forget(α)) to α. This is the fold
that interprets the free algebra structure using α's operations.
-/

/--
Fold a free monad value with fiber proof into an algebra value with fiber proof.
At leaves, returns the leaf value. At nodes, recursively folds children
and applies the algebra structure map.
-/
def polyFreeCounitFoldAt (P : PolyEndo X) (α : PolyAlg P) (x : X) :
    (t : PolyFreeM α.a P x) → { v : α.a.left // α.a.hom v = x }
  | PolyFix.mk _ (Sum.inl a) _ => a
  | PolyFix.mk _ (Sum.inr p) children =>
    let fam := polyBetweenFamily X X P x p
    let childrenFolded : fam ⟶ α.a := Over.homMk
      (fun e => (polyFreeCounitFoldAt P α (fam.hom e) (children e)).val)
      (by funext e; exact (polyFreeCounitFoldAt P α (fam.hom e) (children e)).property)
    let node := (⟨x, ⟨p, childrenFolded⟩⟩ : ((polyBetweenEvalFunctor X X P).obj α.a).left)
    let result := α.str.left node
    have hfib : α.a.hom result = x := congrFun (Over.w α.str) node
    ⟨result, hfib⟩

/--
Transporting a tree to a different fiber and then folding gives the same
underlying value as folding at the original fiber.
-/
lemma polyFreeCounitFoldAt_cast (P : PolyEndo X) (α : PolyAlg P) {x y : X}
    (eq : x = y) (t : PolyFreeM α.a P x) :
    (polyFreeCounitFoldAt P α y (eq ▸ t)).val =
    (polyFreeCounitFoldAt P α x t).val := by
  subst eq
  rfl

/--
The left component of the counit fold morphism.
-/
def polyFreeCounitFoldLeft (P : PolyEndo X) (α : PolyAlg P) :
    (polyFreeMCarrier α.a P).left → α.a.left :=
  fun ⟨x, t⟩ => (polyFreeCounitFoldAt P α x t).val

/--
The counit fold preserves fibers.
-/
lemma polyFreeCounitFoldLeft_fiber (P : PolyEndo X) (α : PolyAlg P)
    (t : (polyFreeMCarrier α.a P).left) :
    α.a.hom (polyFreeCounitFoldLeft P α t) = (polyFreeMCarrier α.a P).hom t :=
  (polyFreeCounitFoldAt P α t.1 t.2).property

/--
The counit fold as a morphism in Over X from Free(Forget(α)) to α.
-/
def polyFreeCounitFold (P : PolyEndo X) (α : PolyAlg P) :
    (polyFreeAlg α.a P).a ⟶ α.a :=
  Over.homMk (polyFreeCounitFoldLeft P α)
    (by funext ⟨x, t⟩; exact polyFreeCounitFoldLeft_fiber P α ⟨x, t⟩)

/--
Folding a pure tree returns the underlying value.
-/
lemma polyFreeCounitFoldAt_pure (P : PolyEndo X) (α : PolyAlg P) (x : X)
    (a : { v : α.a.left // α.a.hom v = x }) :
    polyFreeCounitFoldAt P α x (polyFreeMPure α.a P a) = a := rfl

/--
The counit fold commutes with the algebra structure maps.
-/
lemma polyFreeCounitFold_comm (P : PolyEndo X) (α : PolyAlg P) :
    (polyEndoFunctor X P).map (polyFreeCounitFold P α) ≫ α.str =
    (polyFreeAlg α.a P).str ≫ polyFreeCounitFold P α := by
  apply Over.OverMorphism.ext
  funext ⟨x, ⟨p, h⟩⟩
  simp only [Over.comp_left, polyEndoFunctor, polyBetweenEvalFunctor, types_comp_apply]
  simp only [polyFreeCounitFold, Over.homMk_left, polyFreeCounitFoldLeft]
  simp only [polyFreeAlg, polyFreeMStr, Over.homMk_left, polyFreeMStrLeft]
  simp only [polyToOverFunctor, polyToOverEvalMap_left, ccrEvalMap]
  simp only [polyFreeCounitFoldAt, polyFreeMStrFamily]
  simp only [pbefIndex, pbefMor, ptoefIndex, ptoefMor]
  simp only [ccrEvalIndex, ccrEvalMor]
  apply congrArg
  ext1
  · rfl
  · simp only [heq_eq_eq]
    apply congrArg
    apply Over.OverMorphism.ext
    funext e
    simp only [Over.homMk_left, Over.comp_left, types_comp_apply]
    simp only [polyFreeCounitFoldLeft]
    have hfib : (h.left e).fst = (polyBetweenFamily X X P x p).hom e :=
      congrFun (Over.w h) e
    rw [polyFreeCounitFoldAt_cast P α hfib (h.left e).snd]
    rfl

/--
The counit as an algebra homomorphism from Free(Forget(α)) to α.
-/
def polyFreeCounitHom (P : PolyEndo X) (α : PolyAlg P) :
    polyFreeAlg α.a P ⟶ α :=
  Endofunctor.Algebra.Hom.mk (polyFreeCounitFold P α) (polyFreeCounitFold_comm P α)

/--
Naturality of the counit fold at each fiber: mapping by an algebra homomorphism
then folding equals folding then applying the homomorphism.
-/
lemma polyFreeCounitFoldAt_natural (P : PolyEndo X) (α β : PolyAlg P)
    (f : α ⟶ β) (x : X) (t : PolyFreeM α.a P x) :
    (polyFreeCounitFoldAt P β x (polyFreeMapAt α.a β.a P f.f x t)).val =
    f.f.left (polyFreeCounitFoldAt P α x t).val := by
  induction t with
  | mk y data children ih =>
    cases data with
    | inl a =>
      simp only [polyFreeMapAt, polyFreeMBind, polyFreeCounitFoldAt, polyFreeMPure]
    | inr p =>
      simp only [polyFreeCounitFoldAt]
      let fam := polyBetweenFamily X X P y p
      let oldChildren : fam ⟶ α.a := Over.homMk
        (fun e => (polyFreeCounitFoldAt P α (fam.hom e) (children e)).val)
        (by funext e; exact (polyFreeCounitFoldAt P α (fam.hom e) (children e)).property)
      let newChildren : fam ⟶ β.a := Over.homMk
        (fun e => (polyFreeCounitFoldAt P β (fam.hom e)
          (polyFreeMapAt α.a β.a P f.f (fam.hom e) (children e))).val)
        (by funext e; exact (polyFreeCounitFoldAt P β (fam.hom e)
          (polyFreeMapAt α.a β.a P f.f (fam.hom e) (children e))).property)
      have hChildren : newChildren = oldChildren ≫ f.f := by
        apply Over.OverMorphism.ext
        funext e
        simp only [Over.comp_left, types_comp_apply]
        exact ih e
      change β.str.left ⟨y, ⟨p, newChildren⟩⟩ = f.f.left (α.str.left ⟨y, ⟨p, oldChildren⟩⟩)
      have hStr := congrFun (congrArg (·.left) f.h) ⟨y, ⟨p, oldChildren⟩⟩
      simp only [Over.comp_left, types_comp_apply, polyEndoFunctor,
        polyBetweenEvalFunctor, polyToOverFunctor, polyToOverEvalMap,
        familySliceForward, familySliceForwardMap, polyToOverEvalFamilyMap,
        ccrEvalMap, Over.homMk_left] at hStr
      rw [hChildren]
      exact hStr

/--
Naturality of the counit: mapping by an algebra homomorphism then applying the
counit equals applying the counit then the homomorphism.
-/
lemma polyFreeCounitHom_natural (P : PolyEndo X) (α β : PolyAlg P) (f : α ⟶ β) :
    polyFreeAlgMap α.a β.a P f.f ≫ polyFreeCounitHom P β =
    polyFreeCounitHom P α ≫ f := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Endofunctor.Algebra.comp_f, polyFreeCounitHom, polyFreeAlgMap,
    polyFreeCounitFold, polyFreeMap]
  exact polyFreeCounitFoldAt_natural P α β f x t

/--
The counit as a natural transformation from Free ∘ Forget to the identity.
-/
def polyFreeCounitNat (P : PolyEndo X) :
    polyForgetFunctor P ⋙ polyFreeFunctor P ⟶ 𝟭 (PolyAlg P) where
  app := fun α => polyFreeCounitHom P α
  naturality := fun _ _ f => polyFreeCounitHom_natural P _ _ f

/-! ### Cofree Coalgebra Structure

For an object `A : Over X`, the cofree P-coalgebra on A has:
- Carrier: `PolyCofreeM A P` (M-type streams with A-annotations at each node)
- Structure map: exposes the P-index from the head and the children
-/

/--
Build the children morphism for the cofree coalgebra structure map.
Maps each direction to the corresponding child M-type.
-/
def polyCofreeChildrenMor (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) :
    polyBetweenFamily X X P x m.head.2 ⟶ polyCofreeCarrier A P :=
  Over.homMk
    (fun e => ⟨(polyBetweenFamily X X P x m.head.2).hom e, m.children e⟩)
    rfl

/--
The destructor family for the cofree coalgebra: extracts the P-index and children.
This forgets the A-annotation at the root and exposes only the P-structure.
-/
def polyCofreeStrFamily (A : Over X) (P : PolyEndo X) (x : X)
    (m : PolyCofreeM A P x) :
    polyBetweenEvalFamily X X P (polyCofreeCarrier A P) x :=
  ⟨m.head.2, polyCofreeChildrenMor A P m⟩

/--
The underlying function of the cofree coalgebra structure map.
-/
def polyCofreeStrLeft (A : Over X) (P : PolyEndo X) :
    (polyCofreeCarrier A P).left →
    ((polyEndoFunctor X P).obj (polyCofreeCarrier A P)).left :=
  fun ⟨x, m⟩ => ⟨x, polyCofreeStrFamily A P x m⟩

/--
The cofree coalgebra structure map commutes with projections to X.
-/
lemma polyCofreeStr_comm (A : Over X) (P : PolyEndo X) :
    polyCofreeStrLeft A P ≫
    ((polyEndoFunctor X P).obj (polyCofreeCarrier A P)).hom =
    (polyCofreeCarrier A P).hom := rfl

/--
The structure map for the cofree P-coalgebra on A.
This exposes the P-structure while forgetting the A-annotation at the root.
-/
def polyCofreeStr (A : Over X) (P : PolyEndo X) :
    polyCofreeCarrier A P ⟶ (polyEndoFunctor X P).obj (polyCofreeCarrier A P) :=
  Over.homMk (polyCofreeStrLeft A P) (polyCofreeStr_comm A P)

/--
The cofree P-coalgebra on an object A : Over X.

The carrier is `polyCofreeCarrier A P` (M-type streams with A-annotations).
The structure map exposes the P-shaped children while forgetting the root annotation.
-/
def polyCofreeCoalg (A : Over X) (P : PolyEndo X) : PolyCoalg P where
  V := polyCofreeCarrier A P
  str := polyCofreeStr A P

/-! ### Cofree Functor on Morphisms

Given `f : A ⟶ B` in `Over X`, we get a coalgebra homomorphism from the cofree
coalgebra on A to the cofree coalgebra on B by mapping annotations: each
A-annotation is transformed to a B-annotation via f.
-/

/--
The fiber proof for mapping an annotation: if `a` is in fiber over `y` in A,
then `f.left a` is in fiber over `y` in B.
-/
lemma polyCofreeMap_fiber_eq (A B : Over X) (f : A ⟶ B) {y : X}
    (a : { v : A.left // A.hom v = y }) : B.hom (f.left a.val) = y := by
  have hw := Over.w f
  calc B.hom (f.left a.val) = (f.left ≫ B.hom) a.val := rfl
    _ = A.hom a.val := congrFun hw a.val
    _ = y := a.property

/--
Map annotations in an approximation from A to B via f.
-/
def polyCofreeMapApprox (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {x : X} :
    PolyCofixApprox (polyScale A P) n x →
    PolyCofixApprox (polyScale B P) n x
  | PolyCofixApprox.continue y => PolyCofixApprox.continue y
  | PolyCofixApprox.intro y ⟨aVal, pIdx⟩ children =>
    let bVal : { v : B.left // B.hom v = y } :=
      ⟨f.left aVal.val, polyCofreeMap_fiber_eq A B f aVal⟩
    PolyCofixApprox.intro y ⟨bVal, pIdx⟩
      (fun e => polyCofreeMapApprox A B P f (children e))

/--
The approximation map commutes with transport.
-/
lemma polyCofreeMapApprox_cast (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {x y : X} (h : x = y)
    (a : PolyCofixApprox (polyScale A P) n x) :
    polyCofreeMapApprox A B P f (h ▸ a) = h ▸ polyCofreeMapApprox A B P f a := by
  subst h
  rfl

/--
The approximation map preserves the agreement relation.
-/
theorem polyCofreeMapApprox_agree (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {x : X}
    {a : PolyCofixApprox (polyScale A P) n x}
    {b : PolyCofixApprox (polyScale A P) (n + 1) x}
    (h : PolyCofixAgree (polyScale A P) a b) :
    PolyCofixAgree (polyScale B P)
      (polyCofreeMapApprox A B P f a)
      (polyCofreeMapApprox A B P f b) := by
  induction h with
  | «continue» x' y' =>
    exact PolyCofixAgree.continue x' (polyCofreeMapApprox A B P f y')
  | intro childA childB child_agree ih' =>
    exact PolyCofixAgree.intro _ _ ih'

/--
Map annotations in a cofree comonad value from A to B via f.
-/
def polyCofreeMapAt (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) {x : X}
    (m : PolyCofreeM A P x) : PolyCofreeM B P x where
  approx := fun n => polyCofreeMapApprox A B P f (m.approx n)
  consistent := fun n => polyCofreeMapApprox_agree A B P f (m.consistent n)

/--
The cofree functor map on the left component of carriers.
-/
def polyCofreeMapLeft (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    (polyCofreeCarrier A P).left → (polyCofreeCarrier B P).left :=
  fun ⟨x, m⟩ => ⟨x, polyCofreeMapAt A B P f m⟩

/--
The cofree functor map commutes with fiber projections.
-/
lemma polyCofreeMap_comm (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyCofreeMapLeft A B P f ≫ (polyCofreeCarrier B P).hom =
    (polyCofreeCarrier A P).hom := rfl

/--
The cofree functor map as a morphism in `Over X`.
-/
def polyCofreeMap (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyCofreeCarrier A P ⟶ polyCofreeCarrier B P :=
  Over.homMk (polyCofreeMapLeft A B P f) (polyCofreeMap_comm A B P f)

/--
The head of a mapped cofree value preserves the P-index.
-/
lemma polyCofreeMapApprox_index_snd (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {x : X} (a : PolyCofixApprox (polyScale A P) (n + 1) x) :
    (polyCofreeMapApprox A B P f a).getIndex.2 = a.getIndex.2 := by
  cases a with
  | intro y i children => rfl

/--
The index of a mapped approximation has the expected form.
-/
lemma polyCofreeMapApprox_getIndex (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {x : X} (a : PolyCofixApprox (polyScale A P) (n + 1) x) :
    (polyCofreeMapApprox A B P f a).getIndex =
    ⟨⟨f.left a.getIndex.1.val, polyCofreeMap_fiber_eq A B f a.getIndex.1⟩, a.getIndex.2⟩ := by
  cases a with
  | intro y i children => rfl

/--
The head of a mapped cofree value preserves the P-index.
-/
lemma polyCofreeMapAt_head_snd (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (m : PolyCofreeM A P x) :
    (polyCofreeMapAt A B P f m).head.2 = m.head.2 := by
  simp only [PolyCofix.head, polyCofreeMapAt]
  exact polyCofreeMapApprox_index_snd A B P f (m.approx 1)

/--
Mapping commutes with `childApproxAt_succ_aux` for `.intro` nodes.

When we have an `.intro y idx children` approximation for `polyScale A P`, mapping
the result of `childApproxAt_succ_aux` equals applying `childApproxAt_succ_aux` to
the mapped approximation (with appropriately transported index and element).

The types work out because:
- `polyBetweenIndex X X (polyScale A P) x = polyScaleIndex A P x`
- `polyBetweenFamily X X (polyScale A P) x head = polyBetweenFamily X X P x head.2`
- Mapping preserves the P-index (`head.2`), so the element domain is unchanged
-/
lemma polyCofreeMapApprox_childApproxAt_succ_aux_eq (A B : Over X) (P : PolyEndo X)
    (f : A ⟶ B) {n : Nat} {x : X}
    (idx : polyBetweenIndex X X (polyScale A P) x)
    (children : ∀ e : (polyBetweenFamily X X (polyScale A P) x idx).left,
      PolyCofixApprox (polyScale A P) (n + 1)
        ((polyBetweenFamily X X (polyScale A P) x idx).hom e))
    (e : (polyBetweenFamily X X (polyScale A P) x idx).left) :
    let mappedIdx : polyBetweenIndex X X (polyScale B P) x :=
      ⟨⟨f.left idx.1.val, polyCofreeMap_fiber_eq A B f idx.1⟩, idx.2⟩
    polyCofreeMapApprox A B P f
      (PolyCofix.childApproxAt_succ_aux idx (.intro x idx children) rfl e) =
    PolyCofix.childApproxAt_succ_aux mappedIdx
      (polyCofreeMapApprox A B P f (.intro x idx children)) rfl e := rfl

/--
Mapping commutes with child approximation extraction at depth 0.
Both sides are `.continue` values, so HEq follows from fiber equality.
-/
lemma polyCofreeMapApprox_childApproxAt_zero_heq (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (m : PolyCofreeM A P x)
    (e1 : (polyBetweenFamily X X (polyScale A P) x m.head).left)
    (e2 : (polyBetweenFamily X X (polyScale B P) x (polyCofreeMapAt A B P f m).head).left)
    (hfibEq : (polyBetweenFamily X X (polyScale A P) x m.head).hom e1 =
              (polyBetweenFamily X X (polyScale B P) x
                (polyCofreeMapAt A B P f m).head).hom e2) :
    HEq (polyCofreeMapApprox A B P f (m.childApproxAt e1 0))
        ((polyCofreeMapAt A B P f m).childApproxAt e2 0) := by
  simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_zero]
  exact PolyCofixApprox.continue_heq hfibEq

/--
Mapping commutes with child approximation extraction at depth k+1.
This is the inductive step for `polyCofreeMapAt_children_heq`.
-/
lemma polyCofreeMapApprox_childApproxAt_succ_heq (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (m : PolyCofreeM A P x)
    (e1 : (polyBetweenFamily X X P x m.head.2).left)
    (e2 : (polyBetweenFamily X X P x (polyCofreeMapAt A B P f m).head.2).left)
    (he : HEq e1 e2)
    (_hfibEq : (polyBetweenFamily X X P x m.head.2).hom e1 =
              (polyBetweenFamily X X P x (polyCofreeMapAt A B P f m).head.2).hom e2)
    (k : Nat)
    (_ih : HEq (polyCofreeMapApprox A B P f ((m.children e1).approx k))
              (((polyCofreeMapAt A B P f m).children e2).approx k)) :
    HEq (polyCofreeMapApprox A B P f ((m.children e1).approx (k + 1)))
        (((polyCofreeMapAt A B P f m).children e2).approx (k + 1)) := by
  simp only [PolyCofix.children, polyCofreeMapAt, PolyCofix.childApproxAt,
    PolyCofix.childApproxAt_succ] at _ih
  have hidx := polyCofreeMapAt_head_snd A B P f m
  have heq1 : (m.approx (k + 2)).getIndex = m.head := m.index_eq_head (k + 1)
  match hm : m.approx (k + 2) with
  | .intro _ idx childFun =>
    rw [hm, PolyCofixApprox.getIndex] at heq1
    subst heq1
    simp only [PolyCofix.children, polyCofreeMapAt, PolyCofix.childApproxAt,
      PolyCofix.childApproxAt_succ, hm]
    let mappedIdx : polyBetweenIndex X X (polyScale B P) x :=
      ⟨⟨f.left m.head.1.val, polyCofreeMap_fiber_eq A B f m.head.1⟩, m.head.2⟩
    have hMappedHead : (polyCofreeMapAt A B P f m).head = mappedIdx := by
      simp only [polyCofreeMapAt, PolyCofix.head]
      exact polyCofreeMapApprox_getIndex A B P f (m.approx 1)
    have hRhsApprox : (polyCofreeMapAt A B P f m).approx (k + 2) =
        polyCofreeMapApprox A B P f (.intro x m.head childFun) := by
      simp only [polyCofreeMapAt, hm]
    have hhead_heq : HEq (polyCofreeMapAt A B P f m).head mappedIdx := heq_of_eq hMappedHead
    have happrox_heq : HEq ((polyCofreeMapAt A B P f m).approx (k + 2))
        (polyCofreeMapApprox A B P f (.intro x m.head childFun)) := heq_of_eq hRhsApprox
    have he1_heq : HEq e1 e1 := HEq.rfl
    have he2_heq : HEq e2 e2 := HEq.rfl
    have hLhsIndexProof : (.intro x m.head childFun :
        PolyCofixApprox (polyScale A P) (k + 2) x).getIndex = m.head := rfl
    have hLhsForm : PolyCofix.childApproxAt_succ_aux m.head (.intro x m.head childFun)
        hLhsIndexProof e1 = childFun e1 :=
      PolyCofix.childApproxAt_succ_aux_intro m.head childFun e1
    rw [hLhsForm]
    let mapped : PolyCofreeM B P x :=
      { approx := fun n => polyCofreeMapApprox A B P f (m.approx n),
        consistent := fun n => polyCofreeMapApprox_agree A B P f (m.consistent n) }
    have hMappedEq : mapped = polyCofreeMapAt A B P f m := rfl
    have hMappedApproxForm : polyCofreeMapApprox A B P f (.intro x m.head childFun) =
        .intro x mappedIdx (fun e => polyCofreeMapApprox A B P f (childFun e)) := rfl
    have hMappedHeadEq : mapped.head = mappedIdx := by
      simp only [PolyCofix.head]
      exact polyCofreeMapApprox_getIndex A B P f (m.approx 1)
    have hMappedApproxEq : mapped.approx (k + 2) =
        polyCofreeMapApprox A B P f (.intro x m.head childFun) :=
      congrArg (polyCofreeMapApprox A B P f) hm
    have hMappedIdxProof : (polyCofreeMapApprox A B P f (.intro x m.head childFun)
        ).getIndex = mappedIdx := rfl
    have hMappedIdxProof2 : (mapped.approx (k + 2)).getIndex = mapped.head :=
      mapped.index_eq_head (k + 1)
    have hheadHeq : HEq mapped.head mappedIdx := heq_of_eq hMappedHeadEq
    have happroxHeq : HEq (mapped.approx (k + 2))
        (PolyCofixApprox.intro x mappedIdx (fun e => polyCofreeMapApprox A B P f (childFun e))) :=
      heq_of_eq (hMappedApproxEq.trans hMappedApproxForm)
    have hE2Heq : HEq e2 e1 := he.symm
    have hRhsAux : HEq (PolyCofix.childApproxAt_succ_aux mapped.head (mapped.approx (k + 2))
        hMappedIdxProof2 e2)
        (PolyCofix.childApproxAt_succ_aux mappedIdx
          (.intro x mappedIdx (fun e => polyCofreeMapApprox A B P f (childFun e)))
          rfl e1) :=
      PolyCofix.childApproxAt_succ_aux_heq rfl _ _ hheadHeq _ _
        happroxHeq _ _ _ _ hE2Heq
    have hRhsSimp : PolyCofix.childApproxAt_succ_aux mappedIdx
        (.intro x mappedIdx (fun e => polyCofreeMapApprox A B P f (childFun e))) rfl e1 =
        polyCofreeMapApprox A B P f (childFun e1) :=
      PolyCofix.childApproxAt_succ_aux_intro mappedIdx
        (fun e => polyCofreeMapApprox A B P f (childFun e)) e1
    convert (hRhsAux.trans (heq_of_eq hRhsSimp)).symm using 2
    exact hMappedApproxEq.symm

/--
Mapping commutes with children extraction under appropriate HEq conditions.
-/
lemma polyCofreeMapAt_children_heq (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (m : PolyCofreeM A P x)
    (e1 : (polyBetweenFamily X X P x m.head.2).left)
    (e2 : (polyBetweenFamily X X P x (polyCofreeMapAt A B P f m).head.2).left)
    (he : HEq e1 e2) :
    HEq (polyCofreeMapAt A B P f (m.children e1))
        ((polyCofreeMapAt A B P f m).children e2) := by
  have hfibEq := overType_hom_heq
    (congrArg (polyBetweenFamily X X P x) (polyCofreeMapAt_head_snd A B P f m).symm)
    e1 e2 he
  apply PolyCofix.heq_of_approx_heq hfibEq
  intro n
  simp only [PolyCofix.children, polyCofreeMapAt]
  induction n with
  | zero =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_zero]
    have lhs_eq : polyCofreeMapApprox A B P f
        (PolyCofixApprox.continue ((polyBetweenFamily X X (polyScale A P) x m.head).hom e1)) =
        PolyCofixApprox.continue ((polyBetweenFamily X X (polyScale A P) x m.head).hom e1) :=
      rfl
    rw [lhs_eq]
    exact PolyCofixApprox.continue_heq hfibEq
  | succ k ih =>
    exact polyCofreeMapApprox_childApproxAt_succ_heq A B P f m e1 e2 he hfibEq k ih

lemma polyCofreeChildrenMor_map_heq (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (m : PolyCofreeM A P x) :
    HEq (polyCofreeChildrenMor A P m ≫
          Over.homMk (polyCofreeMapLeft A B P f) (polyCofreeMap_comm A B P f))
        (polyCofreeChildrenMor B P (polyCofreeMapAt A B P f m)) := by
  have hidx : m.head.2 = (polyCofreeMapAt A B P f m).head.2 :=
    (polyCofreeMapAt_head_snd A B P f m).symm
  apply polyBetweenFamily_mor_heq rfl _ _ (heq_of_eq hidx)
  simp only [Over.comp_left, polyCofreeChildrenMor, Over.homMk_left, polyCofreeMapAt]
  have hdomEq := congrArg (fun i => (polyBetweenFamily X X P x i).left) hidx
  apply funext_heq hdomEq rfl
  intro e1 e2 he
  simp only [types_comp_apply, polyCofreeMapLeft]
  have hfibEq := overType_hom_heq (congrArg (polyBetweenFamily X X P x) hidx) e1 e2 he
  apply heq_of_eq
  refine Sigma.ext hfibEq ?_
  exact polyCofreeMapAt_children_heq A B P f m e1 e2 he

/--
The cofree map commutes with coalgebra structure maps.
(Equation is: str_A ≫ F.map f = f ≫ str_B)

Proof strategy: After unfolding definitions, we need to show equality of nested sigmas:
  ⟨x, ⟨m.head.2, childrenMor ≫ map⟩⟩ = ⟨x, ⟨mapped.head.2, mapped_childrenMor⟩⟩
We prove this by:
1. First components are both x (rfl)
2. P-indices are equal (polyCofreeMapAt_head_snd)
3. Children morphisms are HEq (polyCofreeChildrenMor_map_heq)
-/
lemma polyCofreeMapHom_comm (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyCofreeStr A P ≫ (polyEndoFunctor X P).map (polyCofreeMap A B P f) =
    polyCofreeMap A B P f ≫ polyCofreeStr B P := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Over.comp_left, polyCofreeMap, Over.homMk_left, polyCofreeStr]
  simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left, types_comp_apply]
  simp only [polyCofreeStrLeft, polyCofreeStrFamily, polyCofreeMapLeft]
  have hidx := (polyCofreeMapAt_head_snd A B P f m).symm
  have hfam : polyBetweenFamily X X P x m.head.2 =
      polyBetweenFamily X X P x (polyCofreeMapAt A B P f m).head.2 :=
    congrArg (polyBetweenFamily X X P x) hidx
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  refine Sigma.ext hidx ?_
  dsimp only []
  exact polyCofreeChildrenMor_map_heq A B P f m

/--
The cofree functor map as a coalgebra homomorphism.
-/
def polyCofreeCoalgMap (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyCofreeCoalg A P ⟶ polyCofreeCoalg B P :=
  Endofunctor.Coalgebra.Hom.mk
    (polyCofreeMap A B P f)
    (polyCofreeMapHom_comm A B P f)

/--
Mapping by the identity morphism is the identity on approximations.
-/
lemma polyCofreeMapApprox_id (A : Over X) (P : PolyEndo X) {n : Nat} {x : X}
    (a : PolyCofixApprox (polyScale A P) n x) :
    polyCofreeMapApprox A A P (𝟙 A) a = a := by
  induction a with
  | «continue» y => rfl
  | intro y idx children ih =>
    obtain ⟨⟨aVal, aProof⟩, pIdx⟩ := idx
    simp only [polyCofreeMapApprox, Over.id_left]
    congr 1
    funext e
    exact ih e

/--
Mapping by identity is identity on cofree values.
-/
lemma polyCofreeMapAt_id (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) :
    polyCofreeMapAt A A P (𝟙 A) m = m := by
  apply PolyCofix.ext
  intro n
  simp only [polyCofreeMapAt]
  exact polyCofreeMapApprox_id A P (m.approx n)

/--
The cofree functor map preserves identity morphisms.
-/
lemma polyCofreeMap_id (A : Over X) (P : PolyEndo X) :
    polyCofreeMap A A P (𝟙 A) = 𝟙 (polyCofreeCarrier A P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [polyCofreeMap, Over.homMk_left, polyCofreeMapLeft, Over.id_left,
    polyCofreeMapAt_id, types_id_apply]

/--
Mapping by composition on approximations.
-/
lemma polyCofreeMapApprox_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) {n : Nat} {x : X}
    (a : PolyCofixApprox (polyScale A P) n x) :
    polyCofreeMapApprox A C P (f ≫ g) a =
    polyCofreeMapApprox B C P g (polyCofreeMapApprox A B P f a) := by
  induction a with
  | «continue» y => rfl
  | intro y idx children ih =>
    obtain ⟨⟨aVal, aProof⟩, pIdx⟩ := idx
    simp only [polyCofreeMapApprox, Over.comp_left]
    congr 1
    funext e
    exact ih e

/--
Mapping by composition equals composition of maps.
-/
lemma polyCofreeMapAt_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) {x : X} (m : PolyCofreeM A P x) :
    polyCofreeMapAt A C P (f ≫ g) m =
    polyCofreeMapAt B C P g (polyCofreeMapAt A B P f m) := by
  apply PolyCofix.ext
  intro n
  simp only [polyCofreeMapAt]
  exact polyCofreeMapApprox_comp A B C P f g (m.approx n)

/--
The cofree functor map preserves composition.
-/
lemma polyCofreeMap_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) :
    polyCofreeMap A C P (f ≫ g) =
    polyCofreeMap A B P f ≫ polyCofreeMap B C P g := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [polyCofreeMap, Over.homMk_left, polyCofreeMapLeft, Over.comp_left,
    types_comp_apply, polyCofreeMapAt_comp]

/--
The cofree functor on coalgebra homomorphisms preserves identity.
-/
lemma polyCofreeCoalgMap_id (A : Over X) (P : PolyEndo X) :
    polyCofreeCoalgMap A A P (𝟙 A) = 𝟙 (polyCofreeCoalg A P) := by
  apply Endofunctor.Coalgebra.Hom.ext
  exact polyCofreeMap_id A P

/--
The cofree functor on coalgebra homomorphisms preserves composition.
-/
lemma polyCofreeCoalgMap_comp (A B C : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (g : B ⟶ C) :
    polyCofreeCoalgMap A C P (f ≫ g) =
    polyCofreeCoalgMap A B P f ≫ polyCofreeCoalgMap B C P g := by
  apply Endofunctor.Coalgebra.Hom.ext
  exact polyCofreeMap_comp A B C P f g

/--
The cofree functor from Over X to PolyCoalg P.

This sends an object A to the cofree P-coalgebra on A (carrier = M-type streams
with A-annotations), and a morphism f : A ⟶ B to the coalgebra homomorphism
that maps annotations via f.
-/
def polyCofreeFunctor (P : PolyEndo X) : Over X ⥤ PolyCoalg P where
  obj := fun A => polyCofreeCoalg A P
  map := fun f => polyCofreeCoalgMap _ _ P f
  map_id := fun A => polyCofreeCoalgMap_id A P
  map_comp := fun f g => polyCofreeCoalgMap_comp _ _ _ P f g

/--
The forgetful functor from P-coalgebras to Over X.
-/
abbrev polyCoalgForgetFunctor (P : PolyEndo X) : PolyCoalg P ⥤ Over X :=
  Endofunctor.Coalgebra.forget (polyEndoFunctor X P)

/--
The left component of the counit: extracts root annotation from cofree carrier.
-/
def polyCofreeCounitLeft (A : Over X) (P : PolyEndo X) :
    (polyCofreeCarrier A P).left → A.left :=
  fun ⟨_, m⟩ => (polyCofreeExtract A P m).val

/--
The counit commutes with projection to X.
-/
lemma polyCofreeCounit_comm (A : Over X) (P : PolyEndo X) :
    polyCofreeCounitLeft A P ≫ A.hom = (polyCofreeCarrier A P).hom := by
  funext ⟨x, m⟩
  simp only [types_comp_apply, polyCofreeCounitLeft, polyCofreeCarrier]
  exact (polyCofreeExtract A P m).property

/--
The counit morphism: Cofree(A) → A in Over X.
Extracts the root A-annotation from a cofree coalgebra element.
-/
def polyCofreeCounit (A : Over X) (P : PolyEndo X) :
    polyCofreeCarrier A P ⟶ A :=
  Over.homMk (polyCofreeCounitLeft A P) (polyCofreeCounit_comm A P)

/--
The counit is natural: extracting root then mapping equals mapping then extracting.
-/
lemma polyCofreeCounit_naturality (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyCofreeMap A B P f ≫ polyCofreeCounit B P =
    polyCofreeCounit A P ≫ f := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Over.comp_left, polyCofreeMap, Over.homMk_left, polyCofreeCounit,
    polyCofreeCounitLeft, types_comp_apply, polyCofreeMapLeft]
  simp only [polyCofreeExtract, polyCofreeMapAt, PolyCofix.head]
  rw [polyCofreeMapApprox_getIndex]

/--
The counit as a natural transformation.
-/
def polyCofreeCounitNat (P : PolyEndo X) :
    polyCofreeFunctor P ⋙ polyCoalgForgetFunctor P ⟶ 𝟭 (Over X) where
  app := fun A => polyCofreeCounit A P
  naturality := fun A B f => polyCofreeCounit_naturality A B P f

/--
Build approximations for the unit anamorphism.
Given a coalgebra β and a state s, unfolds s into an M-type where each node is
annotated by the state at that point.
-/
def polyCoalgUnitApprox (P : PolyEndo X) (β : PolyCoalg P) (n : Nat) (x : X)
    (s : { a : β.V.left // β.V.hom a = x }) :
    PolyCofixApprox (polyScale β.V P) n x :=
  match n with
  | 0 => .continue x
  | n + 1 =>
    let strResult := β.str.left s.val
    have hx : strResult.1 = x := by
      have h := congrFun (Over.w β.str) s.val
      simp only at h
      rw [s.property] at h
      exact h
    let elem : polyBetweenEvalFamily X X P β.V strResult.1 := strResult.2
    let pIdx := elem.1
    let childMor := elem.2
    let sAtFiber : { a : β.V.left // β.V.hom a = strResult.1 } :=
      ⟨s.val, hx.symm ▸ s.property⟩
    hx ▸ .intro strResult.1 ⟨sAtFiber, pIdx⟩ (fun e =>
      let childVal := childMor.left e
      have hChild : β.V.hom childVal =
          (polyBetweenFamily X X P strResult.1 pIdx).hom e :=
        congrFun (Over.w childMor) e
      polyCoalgUnitApprox P β n _ ⟨childVal, hChild⟩)

/--
Successive approximations agree.
-/
lemma polyCoalgUnitApprox_consistent (P : PolyEndo X) (β : PolyCoalg P) (n : Nat)
    (x : X) (s : { a : β.V.left // β.V.hom a = x }) :
    PolyCofixAgree (polyScale β.V P)
      (polyCoalgUnitApprox P β n x s)
      (polyCoalgUnitApprox P β (n + 1) x s) := by
  induction n generalizing x s with
  | zero =>
    simp only [polyCoalgUnitApprox]
    exact PolyCofixAgree.continue _ _
  | succ n ih =>
    simp only [polyCoalgUnitApprox]
    apply PolyCofixAgree.transport
    exact PolyCofixAgree.intro _ _ (fun e => ih _ _)

/--
Transporting `polyCoalgUnitApprox` along a fiber equality gives the same result
as computing at the transported fiber point.
-/
lemma polyCoalgUnitApprox_cast (P : PolyEndo X) (β : PolyCoalg P) (n : Nat)
    (x y : X) (hxy : x = y)
    (s : { a : β.V.left // β.V.hom a = x }) :
    hxy ▸ polyCoalgUnitApprox P β n x s =
      polyCoalgUnitApprox P β n y ⟨s.val, s.property.trans hxy⟩ := by
  subst hxy
  rfl

/--
HEq version: `polyCoalgUnitApprox` applied to the same element at equal fiber
points gives HEq results.
-/
lemma polyCoalgUnitApprox_heq (P : PolyEndo X) (β : PolyCoalg P) (n : Nat)
    (x y : X) (hxy : x = y)
    (s1 : { a : β.V.left // β.V.hom a = x })
    (s2 : { a : β.V.left // β.V.hom a = y })
    (hs : s1.val = s2.val) :
    HEq (polyCoalgUnitApprox P β n x s1) (polyCoalgUnitApprox P β n y s2) := by
  subst hxy
  have heq : s1 = s2 := Subtype.ext hs
  rw [heq]

/--
Build the M-type for a state in the unit construction.
-/
def polyCoalgUnitAt (P : PolyEndo X) (β : PolyCoalg P) (x : X)
    (s : { a : β.V.left // β.V.hom a = x }) :
    PolyCofreeM β.V P x where
  approx n := polyCoalgUnitApprox P β n x s
  consistent n := polyCoalgUnitApprox_consistent P β n x s

/--
The left component of the unit morphism.
-/
def polyCoalgUnitLeft (P : PolyEndo X) (β : PolyCoalg P) :
    β.V.left → (polyCofreeCarrier β.V P).left :=
  fun a => ⟨β.V.hom a, polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩⟩

/--
The unit commutes with projection to X.
-/
lemma polyCoalgUnit_comm (P : PolyEndo X) (β : PolyCoalg P) :
    polyCoalgUnitLeft P β ≫ (polyCofreeCarrier β.V P).hom = β.V.hom := rfl

/--
The unit morphism: β.V → Cofree(β.V) in Over X.
-/
def polyCoalgUnit (P : PolyEndo X) (β : PolyCoalg P) :
    β.V ⟶ polyCofreeCarrier β.V P :=
  Over.homMk (polyCoalgUnitLeft P β) (polyCoalgUnit_comm P β)

/--
The type of elements in `(polyEndoFunctor X P).obj (polyCofreeCarrier A P)`.
-/
abbrev PolyEndoCofreeObjLeft (A : Over X) (P : PolyEndo X) :=
  (Σ x : X, polyBetweenEvalFamily X X P (polyCofreeCarrier A P) x)

/--
The LHS of the unit coalgebra homomorphism at point `a`:
applying `β.str` then the functor map of the unit.
-/
def polyCoalgUnit_coalg_comm_lhs (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) : PolyEndoCofreeObjLeft β.V P :=
  let strResult := β.str.left a
  ⟨strResult.1, strResult.2.1,
    strResult.2.2 ≫ polyCoalgUnit P β⟩

/--
The RHS of the unit coalgebra homomorphism at point `a`:
applying the unit then the cofree structure map.
-/
def polyCoalgUnit_coalg_comm_rhs (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) : PolyEndoCofreeObjLeft β.V P :=
  let m := polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩
  ⟨β.V.hom a, m.head.2, polyCofreeChildrenMor β.V P m⟩

/--
First component of LHS equals `(β.str.left a).1`.
-/
lemma polyCoalgUnit_coalg_comm_lhs_fst (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    (polyCoalgUnit_coalg_comm_lhs P β a).1 = (β.str.left a).1 := rfl

/--
First component of RHS equals `β.V.hom a`.
-/
lemma polyCoalgUnit_coalg_comm_rhs_fst (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    (polyCoalgUnit_coalg_comm_rhs P β a).1 = β.V.hom a := rfl

/--
The structure map commutes with the projection.
-/
lemma polyCoalgUnit_coalg_comm_fst_eq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) : (β.str.left a).1 = β.V.hom a :=
  congrFun (Over.w β.str) a

/--
First components of LHS and RHS are equal.
-/
lemma polyCoalgUnit_coalg_comm_fst (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    (polyCoalgUnit_coalg_comm_lhs P β a).1 =
    (polyCoalgUnit_coalg_comm_rhs P β a).1 :=
  polyCoalgUnit_coalg_comm_fst_eq P β a

/--
The head of the unit M-type.
-/
lemma polyCoalgUnit_head (P : PolyEndo X) (β : PolyCoalg P) (a : β.V.left) :
    let m := polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩
    let hx := polyCoalgUnit_coalg_comm_fst_eq P β a
    m.head = hx ▸ ⟨⟨a, hx.symm ▸ rfl⟩, (β.str.left a).2.1⟩ := by
  simp only [polyCoalgUnitAt, PolyCofix.head, polyCoalgUnitApprox]
  exact PolyCofixApprox.getIndex_cast _ _ _

/--
Transport distributes to the second component of polyScale indices.
-/
lemma polyScaleIndex_transport_snd {A : Over X} {P : PolyEndo X} {x y : X}
    (h : x = y) (s : { a : A.left // A.hom a = x }) (i : polyBetweenIndex X X P x) :
    (h ▸ (s, i) : polyBetweenIndex X X (polyScale A P) y).2 = h ▸ i := by
  subst h
  rfl

/--
The second component of the unit M-type head equals the transported index.
-/
lemma polyCoalgUnit_head_snd (P : PolyEndo X) (β : PolyCoalg P) (a : β.V.left) :
    (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2 =
    (polyCoalgUnit_coalg_comm_fst_eq P β a) ▸ (β.str.left a).2.1 := by
  have h := polyCoalgUnit_head P β a
  simp only at h
  rw [h]
  exact polyScaleIndex_transport_snd _ _ _

/--
Transport a `polyBetweenFamily` index along an equality of fiber points.
-/
lemma polyBetweenFamily_transport {P : PolyEndo X} {y1 y2 : X}
    (h : y1 = y2) (i : polyBetweenIndex X X P y1) :
    polyBetweenFamily X X P y1 i = polyBetweenFamily X X P y2 (h ▸ i) := by
  subst h
  rfl

/--
The families on both sides of the coalgebra homomorphism equation are equal.
-/
lemma polyCoalgUnit_family_eq (P : PolyEndo X) (β : PolyCoalg P) (a : β.V.left) :
    polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1 =
    polyBetweenFamily X X P (β.V.hom a)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2) := by
  have hfst := polyCoalgUnit_coalg_comm_fst_eq P β a
  have hsnd := polyCoalgUnit_head_snd P β a
  simp only [hsnd]
  exact polyBetweenFamily_transport hfst _

/--
HEq of elements in polyBetweenEvalFamily for cofree carriers when the fiber points are equal.
-/
lemma polyCofreeBetweenEvalFamily_heq {A : Over X} {P : PolyEndo X} {x y : X}
    (heq : x = y)
    (i : polyBetweenIndex X X P x)
    (mor : polyBetweenFamily X X P x i ⟶ polyCofreeCarrier A P)
    (j : polyBetweenIndex X X P y)
    (mor' : polyBetweenFamily X X P y j ⟶ polyCofreeCarrier A P)
    (hi : HEq i j)
    (hmor : HEq mor mor') :
    HEq (⟨i, mor⟩ : polyBetweenEvalFamily X X P (polyCofreeCarrier A P) x)
        (⟨j, mor'⟩ : polyBetweenEvalFamily X X P (polyCofreeCarrier A P) y) := by
  subst heq
  simp only [heq_eq_eq] at hi hmor
  subst hi hmor
  rfl

/--
HEq of indices for the coalgebra homomorphism proof.
-/
lemma polyCoalgUnit_coalg_comm_index_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    HEq (β.str.left a).2.1
        (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2 := by
  have hfst := polyCoalgUnit_coalg_comm_fst_eq P β a
  have hsnd := polyCoalgUnit_head_snd P β a
  have step1 : HEq (β.str.left a).2.1 (hfst ▸ (β.str.left a).2.1) :=
    heq_eqRec (motive := fun x => polyBetweenIndex X X P x) hfst (β.str.left a).2.1
  have step2 : hfst ▸ (β.str.left a).2.1 =
      (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2 := hsnd.symm
  exact step1.trans (heq_of_eq step2)

/--
The LHS transport is HEq to polyCoalgUnitApprox at the target fiber.
-/
lemma polyCoalgUnitAt_child_approx_lhs_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hchildFib : β.V.hom ((β.str.left a).2.2.left e1) =
        (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1)
    (e2 : (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left)
    (hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
        (polyBetweenFamily X X P (β.V.hom a)
          ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2) :
    let childVal := (β.str.left a).2.2.left e1
    let parentHead := (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
    let fiberPt := (polyBetweenFamily X X P (β.V.hom a) parentHead.2).hom e2
    HEq ((hchildFib.trans hfib) ▸
      polyCoalgUnitApprox P β (n + 1) (β.V.hom childVal) ⟨childVal, rfl⟩)
    (polyCoalgUnitApprox P β (n + 1) fiberPt ⟨childVal, hchildFib.trans hfib⟩) := by
  intro childVal parentHead fiberPt
  apply heq_of_eq
  exact polyCoalgUnitApprox_cast P β (n + 1) (β.V.hom childVal) fiberPt
    (hchildFib.trans hfib) ⟨childVal, rfl⟩

/--
Extracting a child from `polyCoalgUnitApprox` at the original fiber gives
`polyCoalgUnitApprox` at the child value.
-/
lemma polyCoalgUnitApprox_child_extract (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left) :
    let strResult := β.str.left a
    let hx : β.V.hom a = strResult.1 := (polyCoalgUnit_coalg_comm_fst_eq P β a).symm
    let origIdx : polyBetweenIndex X X (polyScale β.V P) strResult.1 :=
      ⟨⟨a, hx⟩, strResult.2.1⟩
    let childMor := strResult.2.2
    let childVal := childMor.left e
    let hChild : β.V.hom childVal =
        (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e :=
      congrFun (Over.w childMor) e
    let fibPt := (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e
    PolyCofix.childApproxAt_succ_aux origIdx
      (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hx⟩)
      rfl e =
    polyCoalgUnitApprox P β (n + 1) fibPt ⟨childVal, hChild⟩ := by
  intro strResult hx origIdx childMor childVal hChild fibPt
  simp only [polyCoalgUnitApprox, PolyCofix.childApproxAt_succ_aux]
  rfl

/--
The extraction via childApproxAt_succ_aux is HEq to polyCoalgUnitApprox.
-/
lemma polyCoalgUnitAt_child_extract_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (e2 : (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left)
    (he1e2 : e1 ≍ e2)
    (hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
        (polyBetweenFamily X X P (β.V.hom a)
          ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2) :
    let childVal := (β.str.left a).2.2.left e1
    let parentHead := (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
    let fiberPt := (polyBetweenFamily X X P (β.V.hom a) parentHead.2).hom e2
    HEq (PolyCofix.childApproxAt_succ_aux parentHead
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1)) e2)
    (polyCoalgUnitApprox P β (n + 1) fiberPt
      ⟨childVal, (congrFun (Over.w (β.str.left a).2.2) e1).trans hfib⟩) := by
  intro childVal parentHead fiberPt
  let strResult := β.str.left a
  let hx : strResult.1 = β.V.hom a := polyCoalgUnit_coalg_comm_fst_eq P β a
  let hxInv : β.V.hom a = strResult.1 := hx.symm
  let origIdx : polyBetweenIndex X X (polyScale β.V P) strResult.1 :=
    ⟨⟨a, hxInv⟩, strResult.2.1⟩
  let childMor := strResult.2.2
  let hChild : β.V.hom childVal =
      (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e1 :=
    congrFun (Over.w childMor) e1
  let fibPtOrig := (polyBetweenFamily X X P strResult.1 strResult.2.1).hom e1
  have hfibPt : fibPtOrig = fiberPt := hfib
  have hhelper := polyCoalgUnitApprox_child_extract P β a n e1
  dsimp only at hhelper
  have hhelper' : PolyCofix.childApproxAt_succ_aux origIdx
      (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hxInv⟩) rfl e1 =
      polyCoalgUnitApprox P β (n + 1) fibPtOrig ⟨childVal, hChild⟩ := hhelper
  have hparentHead : parentHead = hx ▸ origIdx := polyCoalgUnit_head P β a
  have happrox_heq : HEq (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hxInv⟩)
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩) :=
    polyCoalgUnitApprox_heq P β (n + 2) strResult.1 (β.V.hom a) hx
      ⟨a, hxInv⟩ ⟨a, rfl⟩ rfl
  have horigIdx_heq : origIdx ≍ parentHead := by
    rw [hparentHead]
    exact heq_eqRec_iff_heq.mpr HEq.rfl
  have hlhs_heq : HEq
      (PolyCofix.childApproxAt_succ_aux origIdx
        (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hxInv⟩) rfl e1)
      (PolyCofix.childApproxAt_succ_aux parentHead
        (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1)) e2) :=
    PolyCofix.childApproxAt_succ_aux_heq hx origIdx parentHead
      horigIdx_heq
      (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hxInv⟩)
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      happrox_heq rfl
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1))
      e1 e2 he1e2
  have hrhs_heq : HEq
      (polyCoalgUnitApprox P β (n + 1) fibPtOrig ⟨childVal, hChild⟩)
      (polyCoalgUnitApprox P β (n + 1) fiberPt
        ⟨childVal, (congrFun (Over.w (β.str.left a).2.2) e1).trans hfib⟩) :=
    polyCoalgUnitApprox_heq P β (n + 1) fibPtOrig fiberPt hfibPt
      ⟨childVal, hChild⟩
      ⟨childVal, (congrFun (Over.w (β.str.left a).2.2) e1).trans hfib⟩ rfl
  have h1 : PolyCofix.childApproxAt_succ_aux origIdx
      (polyCoalgUnitApprox P β (n + 2) strResult.1 ⟨a, hxInv⟩) rfl e1 ≍
      polyCoalgUnitApprox P β (n + 1) fiberPt
        ⟨childVal, (congrFun (Over.w (β.str.left a).2.2) e1).trans hfib⟩ :=
    (heq_of_eq hhelper').trans hrhs_heq
  exact hlhs_heq.symm.trans h1

/--
The RHS extraction via childApproxAt_succ_aux is HEq to polyCoalgUnitApprox.
-/
lemma polyCoalgUnitAt_child_approx_rhs_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hchildFib : β.V.hom ((β.str.left a).2.2.left e1) =
        (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1)
    (e2 : (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left)
    (he1e2 : e1 ≍ e2)
    (hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
        (polyBetweenFamily X X P (β.V.hom a)
          ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2) :
    let childVal := (β.str.left a).2.2.left e1
    let parentHead := (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
    let fiberPt := (polyBetweenFamily X X P (β.V.hom a) parentHead.2).hom e2
    HEq (PolyCofix.childApproxAt_succ_aux parentHead
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1)) e2)
    (polyCoalgUnitApprox P β (n + 1) fiberPt ⟨childVal, hchildFib.trans hfib⟩) := by
  intro childVal parentHead fiberPt
  have hchildFib_eq : hchildFib = (congrFun (Over.w (β.str.left a).2.2) e1) :=
    Subsingleton.elim _ _
  rw [hchildFib_eq]
  exact polyCoalgUnitAt_child_extract_heq P β a n e1 e2 he1e2 hfib

/--
The extraction via `childApproxAt_succ_aux` is HEq to the direct approximation.
-/
lemma polyCoalgUnitAt_child_approx_aux_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hchildFib : β.V.hom ((β.str.left a).2.2.left e1) =
        (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1)
    (e2 : (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left)
    (he1e2 : e1 ≍ e2)
    (hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
        (polyBetweenFamily X X P (β.V.hom a)
          ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2) :
    let childVal := (β.str.left a).2.2.left e1
    let parentHead := (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
    HEq ((hchildFib.trans hfib) ▸
      polyCoalgUnitApprox P β (n + 1) (β.V.hom childVal) ⟨childVal, rfl⟩)
    (PolyCofix.childApproxAt_succ_aux parentHead
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1)) e2) := by
  intro childVal parentHead
  have hLHS := polyCoalgUnitAt_child_approx_lhs_heq P β a n e1 hchildFib e2 hfib
  have hRHS := polyCoalgUnitAt_child_approx_rhs_heq P β a n e1 hchildFib e2 he1e2 hfib
  exact hLHS.trans hRHS.symm

/--
The child approximation extracted via `childApproxAt_succ_aux` equals the direct
approximation after transport.
-/
lemma polyCoalgUnitAt_child_approx_aux (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) (n : Nat)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hchildFib : β.V.hom ((β.str.left a).2.2.left e1) =
        (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1)
    (e2 : (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left)
    (he1e2 : e1 ≍ e2)
    (hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
        (polyBetweenFamily X X P (β.V.hom a)
          ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2) :
    (hchildFib.trans hfib) ▸
      polyCoalgUnitApprox P β (n + 1)
        (β.V.hom ((β.str.left a).2.2.left e1))
        ⟨(β.str.left a).2.2.left e1, rfl⟩ =
    PolyCofix.childApproxAt_succ_aux
      (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1))
      e2 := by
  apply eq_of_heq
  exact polyCoalgUnitAt_child_approx_aux_heq P β a n e1 hchildFib e2 he1e2 hfib

/--
At level n+1, extracting a child from polyCoalgUnitApprox equals polyCoalgUnitApprox
applied to the child element.
-/
lemma polyCoalgUnitAt_child_approx_eq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hfibEq : β.V.hom ((β.str.left a).2.2.left e1) =
      (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom
        (cast (congrArg (fun F => F.left)
          (polyCoalgUnit_family_eq P β a)) e1))
    (n : Nat) :
    hfibEq ▸ polyCoalgUnitApprox P β (n + 1)
      (β.V.hom ((β.str.left a).2.2.left e1))
      ⟨(β.str.left a).2.2.left e1, rfl⟩ =
    PolyCofix.childApproxAt_succ_aux
      (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
      (polyCoalgUnitApprox P β (n + 2) (β.V.hom a) ⟨a, rfl⟩)
      ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).index_eq_head (n + 1))
      (cast (congrArg (fun F => F.left) (polyCoalgUnit_family_eq P β a)) e1) := by
  let childVal := (β.str.left a).2.2.left e1
  let e2 := cast (congrArg (fun F => F.left) (polyCoalgUnit_family_eq P β a)) e1
  have he1e2 : e1 ≍ e2 := (cast_heq _ e1).symm
  let parentHead := (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head
  have hchildFib : β.V.hom childVal =
      (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 :=
    congrFun (Over.w (β.str.left a).2.2) e1
  have hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
      (polyBetweenFamily X X P (β.V.hom a) parentHead.2).hom e2 := by
    exact overType_hom_heq (polyCoalgUnit_family_eq P β a) e1 e2 he1e2
  have hfibEq' : hchildFib.trans hfib = hfibEq := Subsingleton.elim _ _
  rw [← hfibEq']
  exact polyCoalgUnitAt_child_approx_aux P β a n e1 hchildFib e2 he1e2 hfib

/--
Children of polyCoalgUnitAt are polyCoalgUnitAt applied to child elements.
This is the coinductive unfolding property.
-/
lemma polyCoalgUnitAt_children_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left)
    (e1 : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left)
    (hfibEq : β.V.hom ((β.str.left a).2.2.left e1) =
      (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom
        (cast (congrArg (fun F => F.left)
          (polyCoalgUnit_family_eq P β a)) e1)) :
    HEq (polyCoalgUnitAt P β (β.V.hom ((β.str.left a).2.2.left e1))
          ⟨(β.str.left a).2.2.left e1, rfl⟩)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).children
          (cast (congrArg (fun F => F.left)
            (polyCoalgUnit_family_eq P β a)) e1)) := by
  let childVal := (β.str.left a).2.2.left e1
  have hTransport := heq_eqRec hfibEq
    (polyCoalgUnitAt P β (β.V.hom childVal) ⟨childVal, rfl⟩)
  apply hTransport.trans
  apply heq_of_eq
  apply PolyCofix.ext
  intro n
  simp only [PolyCofix.children, polyCoalgUnitAt]
  rw [PolyCofix.approx_cast hfibEq]
  match n with
  | 0 =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_zero, polyCoalgUnitApprox]
    rw [PolyCofixApprox.continue_cast hfibEq]
    rfl
  | n + 1 =>
    simp only [PolyCofix.childApproxAt, PolyCofix.childApproxAt_succ]
    exact polyCoalgUnitAt_child_approx_eq P β a e1 hfibEq n

/--
HEq of morphisms for the coalgebra homomorphism proof.
-/
lemma polyCoalgUnit_coalg_comm_mor_heq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    HEq ((β.str.left a).2.2 ≫ polyCoalgUnit P β)
        (polyCofreeChildrenMor β.V P (polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩)) := by
  have hfst := polyCoalgUnit_coalg_comm_fst_eq P β a
  have hindexHeq := polyCoalgUnit_coalg_comm_index_heq P β a
  apply polyBetweenFamily_mor_heq hfst _ _ hindexHeq
  simp only [Over.comp_left, polyCoalgUnit, Over.homMk_left, polyCofreeChildrenMor]
  have hfam := polyCoalgUnit_family_eq P β a
  have hdomHeq := polyBetweenFamily_left_heq hfst _ _ hindexHeq
  apply funext_heq (eq_of_heq hdomHeq) rfl
  intro e1 e2 he
  simp only [types_comp_apply, polyCoalgUnitLeft]
  apply heq_of_eq
  have hfib : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 =
      (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).hom e2 := by
    exact overType_hom_heq hfam e1 e2 he
  have hdom_eq : (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).left =
      (polyBetweenFamily X X P (β.V.hom a)
        ((polyCoalgUnitAt P β (β.V.hom a) ⟨a, rfl⟩).head.2)).left :=
    congrArg (fun F => F.left) hfam
  have he2_eq : e2 = cast hdom_eq e1 := by
    apply eq_of_heq
    exact he.symm.trans (cast_heq hdom_eq e1).symm
  let childVal := (β.str.left a).2.2.left e1
  have hChildFib : β.V.hom childVal =
      (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1 :=
    congrFun (Over.w (β.str.left a).2.2) e1
  rw [Sigma.mk.inj_iff]
  constructor
  · trans (polyBetweenFamily X X P (β.str.left a).1 (β.str.left a).2.1).hom e1
    · exact hChildFib
    · exact hfib
  · subst he2_eq
    have hfibEq := hChildFib.trans hfib
    exact polyCoalgUnitAt_children_heq P β a e1 hfibEq

/--
Second components of LHS and RHS are heterogeneously equal.
-/
lemma polyCoalgUnit_coalg_comm_snd (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    HEq (polyCoalgUnit_coalg_comm_lhs P β a).2
        (polyCoalgUnit_coalg_comm_rhs P β a).2 := by
  simp only [polyCoalgUnit_coalg_comm_lhs, polyCoalgUnit_coalg_comm_rhs]
  have hfst := polyCoalgUnit_coalg_comm_fst_eq P β a
  apply polyCofreeBetweenEvalFamily_heq hfst
  · exact polyCoalgUnit_coalg_comm_index_heq P β a
  · exact polyCoalgUnit_coalg_comm_mor_heq P β a

/--
LHS and RHS are equal.
-/
lemma polyCoalgUnit_coalg_comm_eq (P : PolyEndo X) (β : PolyCoalg P)
    (a : β.V.left) :
    polyCoalgUnit_coalg_comm_lhs P β a = polyCoalgUnit_coalg_comm_rhs P β a :=
  Sigma.ext_iff.mpr ⟨polyCoalgUnit_coalg_comm_fst P β a,
    polyCoalgUnit_coalg_comm_snd P β a⟩

/--
The unit morphism commutes with coalgebra structure maps.
-/
lemma polyCoalgUnit_coalg_comm (P : PolyEndo X) (β : PolyCoalg P) :
    β.str ≫ (polyEndoFunctor X P).map (polyCoalgUnit P β) =
    polyCoalgUnit P β ≫ polyCofreeStr β.V P := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, types_comp_apply]
  dsimp only [polyCoalgUnit, Over.homMk_left, polyCoalgUnitLeft,
    polyCofreeStr, polyCofreeStrLeft, polyCofreeStrFamily,
    polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap, familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap, ccrEvalMap]
  exact polyCoalgUnit_coalg_comm_eq P β a

/--
The unit as a coalgebra homomorphism from β to Cofree(β.V).
-/
def polyCoalgUnitHom (P : PolyEndo X) (β : PolyCoalg P) :
    β ⟶ polyCofreeCoalg β.V P where
  f := polyCoalgUnit P β
  h := polyCoalgUnit_coalg_comm P β

/--
Naturality for approximations: the mapped unit approx equals the direct unit approx.
-/
lemma polyCoalgUnit_naturality_approx (P : PolyEndo X) (β γ : PolyCoalg P)
    (g : β ⟶ γ) (a : β.V.left) (n : Nat)
    (hfib : γ.V.hom (g.f.left a) = β.V.hom a) :
    HEq (polyCofreeMapApprox β.V γ.V P g.f
          (polyCoalgUnitApprox P β n (β.V.hom a) ⟨a, rfl⟩))
        (polyCoalgUnitApprox P γ n (γ.V.hom (g.f.left a)) ⟨g.f.left a, rfl⟩) := by
  induction n generalizing a with
  | zero =>
    simp only [polyCoalgUnitApprox, polyCofreeMapApprox]
    exact PolyCofixApprox.continue_heq hfib.symm
  | succ n ih =>
    simp only [polyCoalgUnitApprox]
    have hCoalgHom := g.h
    have hCoalgAt : ((polyEndoFunctor X P).map g.f).left (β.str.left a) =
        γ.str.left (g.f.left a) := by
      have h := congrFun (congrArg (·.left) hCoalgHom) a
      simp only [types_comp_apply, Over.comp_left] at h
      exact h
    simp only [polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
      polyToOverEvalMap, familySliceForward, familySliceForwardMap,
      polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left] at hCoalgAt
    have hfib1 : (β.str.left a).fst = (γ.str.left (g.f.left a)).fst :=
      congrArg (·.fst) hCoalgAt
    have hTypeEq : polyBetweenEvalFamily X X P γ.V (β.str.left a).fst =
        polyBetweenEvalFamily X X P γ.V (γ.str.left (g.f.left a)).fst :=
      congrArg (polyBetweenEvalFamily X X P γ.V) hfib1
    have hsnd_heq : (⟨(β.str.left a).snd.fst, (β.str.left a).snd.snd ≫ g.f⟩ :
        polyBetweenEvalFamily X X P γ.V (β.str.left a).fst) ≍
        (γ.str.left (g.f.left a)).snd := sigma_snd_heq_of_eq hCoalgAt
    have hpIdx : (β.str.left a).snd.fst ≍ (γ.str.left (g.f.left a)).snd.fst :=
      @sigma_fst_heq_of_heq_diff_base X (fun y => ccrIndex (P y))
        (fun y i => ccrFamily (P y) i ⟶ γ.V) _ _ hfib1 _ _ hsnd_heq
    have hpIdx_eq : (β.str.left a).snd.fst =
        cast (congrArg (fun y => ccrIndex (P y)) hfib1.symm)
          (γ.str.left (g.f.left a)).snd.fst :=
      eq_of_heq (hpIdx.trans (cast_heq _ _).symm)
    have hChildMorEq : (β.str.left a).snd.snd ≫ g.f ≍
        (γ.str.left (g.f.left a)).snd.snd :=
      @sigma_snd_heq_of_heq_diff_base X (fun y => ccrIndex (P y))
        (fun y i => ccrFamily (P y) i ⟶ γ.V) _ _ hfib1 _ _ hsnd_heq
    rw [polyCofreeMapApprox_cast]
    simp only [polyCofreeMapApprox]
    apply PolyCofixApprox.intro_cast_heq' _ _ hfib.symm hfib1
    · apply prod_mk_heq
      · have hβfib : (β.str.left a).fst = β.V.hom a :=
          congrFun (Over.w β.str) a
        have hγfib : (γ.str.left (g.f.left a)).fst = γ.V.hom (g.f.left a) :=
          congrFun (Over.w γ.str) (g.f.left a)
        have hi : γ.V.hom (g.f.left a) = (β.str.left a).fst :=
          hfib.trans hβfib.symm
        have hj : γ.V.hom (g.f.left a) = (γ.str.left (g.f.left a)).fst :=
          hγfib.symm
        exact @subtype_heq_of_pred_index_eq γ.V.left X
          (fun idx x => γ.V.hom x = idx) _ _ hfib1 _ hi hj
      · exact hpIdx
    · have hβfib' : β.V.hom a = (β.str.left a).fst :=
        (congrFun (Over.w β.str) a).symm
      have hγfib' : γ.V.hom (g.f.left a) = (γ.str.left (g.f.left a)).fst :=
        (congrFun (Over.w γ.str) (g.f.left a)).symm
      have hdomEq : (polyBetweenFamily X X (polyScale β.V P) (β.str.left a).fst
            (⟨a, hβfib'⟩, (β.str.left a).snd.fst)).left =
          (polyBetweenFamily X X (polyScale γ.V P) (γ.str.left (g.f.left a)).fst
            (⟨g.f.left a, hγfib'⟩, (γ.str.left (g.f.left a)).snd.fst)).left := by
        simp only [polyBetweenFamily, polyToOverFamily, ccrFamily, polyScale, polyScaleAt]
        exact eq_of_heq (polyBetweenFamily_left_heq hfib1 _ _ hpIdx)
      have hCodEq : ∀ (e1 : (polyBetweenFamily X X (polyScale β.V P)
              (β.str.left a).fst (⟨a, hβfib'⟩, (β.str.left a).snd.fst)).left)
            (e2 : (polyBetweenFamily X X (polyScale γ.V P)
              (γ.str.left (g.f.left a)).fst
              (⟨g.f.left a, hγfib'⟩, (γ.str.left (g.f.left a)).snd.fst)).left),
            HEq e1 e2 →
            PolyCofixApprox (polyScale γ.V P) n
              ((polyBetweenFamily X X (polyScale β.V P)
                (β.str.left a).fst (⟨a, hβfib'⟩, (β.str.left a).snd.fst)).hom e1) =
            PolyCofixApprox (polyScale γ.V P) n
              ((polyBetweenFamily X X (polyScale γ.V P)
                (γ.str.left (g.f.left a)).fst
                (⟨g.f.left a, hγfib'⟩, (γ.str.left (g.f.left a)).snd.fst)).hom e2) := by
        intro e1 e2 he12
        congr 1
        simp only [polyBetweenFamily, polyToOverFamily, ccrFamily, polyScale, polyScaleAt]
        exact polyBetweenFamily_hom_eq_of_heq hfib1 _ _ hpIdx e1 e2 he12
      apply funext_heq_dep hdomEq hCodEq
      intro e1 e2 he
      let child1 := (β.str.left a).snd.snd.left e1
      have hChildFib : γ.V.hom (g.f.left child1) = β.V.hom child1 :=
        congrFun (Over.w g.f) _
      have hBetaFib : (polyBetweenFamily X X (polyScale β.V P)
            (β.str.left a).fst (⟨a, hβfib'⟩, (β.str.left a).snd.fst)).hom e1 =
          β.V.hom child1 :=
        (congrFun (Over.w (β.str.left a).snd.snd) e1).symm
      have he12 : (cast hdomEq e1) = e2 := eq_of_heq ((cast_heq hdomEq e1).trans he)
      have hChild2 : (γ.str.left (g.f.left a)).snd.snd.left e2 = g.f.left child1 := by
        rw [← he12]
        have hMorApply : g.f.left ((β.str.left a).snd.snd.left e1) =
            (γ.str.left (g.f.left a)).snd.snd.left (cast hdomEq e1) := by
          have hMorTypeEq := type_eq_of_heq hChildMorEq
          have hMorEq : (β.str.left a).snd.snd ≫ g.f =
              cast hMorTypeEq.symm (γ.str.left (g.f.left a)).snd.snd :=
            eq_of_heq (hChildMorEq.trans (cast_heq hMorTypeEq.symm _).symm)
          have hSrcEq : (ccrFamily (P (γ.str.left (g.f.left a)).fst)
                (γ.str.left (g.f.left a)).snd.fst) =
              (ccrFamily (P (β.str.left a).fst) (β.str.left a).snd.fst) := by
            simp only [ccrFamily]
            exact eq_of_heq (polyBetweenFamily_heq hfib1.symm _ _ hpIdx.symm)
          have hLeftEq := congrArg CommaMorphism.left hMorEq
          simp only [Over.comp_left] at hLeftEq
          have h1 : g.f.left ((β.str.left a).snd.snd.left e1) =
              (cast hMorTypeEq.symm (γ.str.left (g.f.left a)).snd.snd).left e1 :=
            congrFun hLeftEq e1
          rw [h1]
          rw [over_cast_left hSrcEq (γ.str.left (g.f.left a)).snd.snd e1]
        exact hMorApply.symm
      have hGammaFib : (polyBetweenFamily X X (polyScale γ.V P)
            (γ.str.left (g.f.left a)).fst
            (⟨g.f.left a, hγfib'⟩, (γ.str.left (g.f.left a)).snd.fst)).hom e2 =
          γ.V.hom (g.f.left child1) := by
        rw [← hChild2]
        exact (congrFun (Over.w (γ.str.left (g.f.left a)).snd.snd) e2).symm
      have hIH := ih child1 hChildFib
      convert hIH using 2
      · exact @polyCoalgUnitApprox_heq X P β n _ _ hBetaFib
          ⟨(β.str.left a).snd.snd.left e1, _⟩ ⟨child1, _⟩ rfl
      · apply subtype_heq_of_val_eq
        · funext _; rw [hGammaFib]
        · exact hChild2

/--
The unit is natural with respect to coalgebra morphisms.
For `g : β ⟶ γ`, we have:
  `g.f ≫ polyCoalgUnit P γ = polyCoalgUnit P β ≫ polyCofreeMap β.V γ.V P g.f`
-/
lemma polyCoalgUnit_naturality (P : PolyEndo X) (β γ : PolyCoalg P) (g : β ⟶ γ) :
    g.f ≫ polyCoalgUnit P γ =
    polyCoalgUnit P β ≫ polyCofreeMap β.V γ.V P g.f := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, types_comp_apply, polyCoalgUnit, Over.homMk_left,
    polyCoalgUnitLeft, polyCofreeMap, polyCofreeMapLeft]
  have hfib : γ.V.hom (g.f.left a) = β.V.hom a := congrFun (Over.w g.f) a
  apply Sigma.ext
  · exact hfib
  · apply PolyCofix.heq_of_approx_heq hfib
    intro n
    simp only [polyCofreeMapAt]
    exact (polyCoalgUnit_naturality_approx P β γ g a n hfib).symm

/--
The unit as a natural transformation from the identity to Forget ∘ Cofree.
-/
def polyCoalgUnitNat (P : PolyEndo X) :
    𝟭 (PolyCoalg P) ⟶ PolyCoalg.forget P ⋙ polyCofreeFunctor P where
  app := fun β => polyCoalgUnitHom P β
  naturality := fun β γ g => by
    apply Endofunctor.Coalgebra.Hom.ext
    simp only [Functor.comp_obj, Functor.id_obj, PolyCoalg.forget,
      Endofunctor.Coalgebra.forget_obj, Functor.comp_map, Functor.id_map,
      Endofunctor.Coalgebra.forget_map, polyCofreeFunctor, polyCofreeCoalgMap,
      polyCoalgUnitHom]
    exact polyCoalgUnit_naturality P β γ g

/-! ### Free ⊣ Forget Adjunction

The free algebra functor is left adjoint to the forgetful functor.
-/

/--
Left triangle identity for Free ⊣ Forget:
Applying the unit then the counit (on the Forget side) is the identity.

For α : PolyAlg P, we have:
  polyFreeUnit α.a P ≫ Forget(polyFreeCounitHom P α) = 𝟙 α.a
-/
lemma polyFree_left_triangle (P : PolyEndo X) (α : PolyAlg P) :
    polyFreeUnit α.a P ≫ (polyForgetFunctor P).map (polyFreeCounitHom P α) =
    𝟙 α.a := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, polyForgetFunctor, Endofunctor.Algebra.forget_map,
    polyFreeCounitHom, polyFreeUnit, Over.homMk_left, polyFreeUnitLeft,
    polyFreeCounitFold, polyFreeCounitFoldLeft, Over.id_left, types_id_apply,
    types_comp_apply]
  rfl

/--
Right triangle identity for Free ⊣ Forget:
Applying the unit (on the Free side) then the counit is the identity.

For A : Over X, we have:
  Free(polyFreeUnit A P) ≫ polyFreeCounitHom P (polyFreeAlg A P) = 𝟙 (polyFreeAlg A P)
-/
lemma polyFree_right_triangle (P : PolyEndo X) (A : Over X) :
    (polyFreeFunctor P).map (polyFreeUnit A P) ≫
      polyFreeCounitHom P (polyFreeAlg A P) =
    𝟙 (polyFreeAlg A P) := by
  apply Endofunctor.Algebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Endofunctor.Algebra.comp_f, polyFreeFunctor, polyFreeAlgMap,
    polyFreeCounitHom, polyFreeCounitFold, Endofunctor.Algebra.id_f, Over.id_left,
    types_id_apply, polyFreeMap, Over.comp_left, Over.homMk_left, types_comp_apply,
    polyFreeMapLeft, polyFreeCounitFoldLeft]
  induction t with
  | mk _ i children ih =>
    cases i with
    | inl a =>
      unfold polyFreeMapAt polyFreeMBind
      simp only [polyFreeUnit, Over.homMk_left, polyFreeUnitLeft,
        polyFreeMPure, polyFreeCounitFoldAt]
      obtain ⟨a_val, rfl⟩ := a
      apply Sigma.ext
      · rfl
      · simp only [heq_eq_eq]
        congr 1
        funext e
        exact PEmpty.elim e
    | inr p =>
      unfold polyFreeMapAt polyFreeMBind polyFreeCounitFoldAt
      simp only [polyFreeAlg, polyFreeMStr, Over.homMk_left, polyFreeMStrLeft,
        polyFreeMStrFamily, pbefIndex, pbefMor]
      apply Sigma.ext
      · rfl
      · simp only [heq_eq_eq]
        congr 1
        funext e
        have h := ih e
        rw [Sigma.ext_iff] at h
        obtain ⟨hfst, hsnd_heq⟩ := h
        simp only at hsnd_heq
        simp only [ptoefMor, ccrEvalMor, polyForgetFunctor, Over.homMk_left]
        exact eq_of_heq ((heq_eqRec _ _).symm.trans hsnd_heq)

/--
The adjunction Free ⊣ Forget for P-algebras.

For a polynomial endofunctor P on Over X:
- The free algebra functor polyFreeFunctor P : Over X → PolyAlg P is left adjoint
- The forgetful functor polyForgetFunctor P : PolyAlg P → Over X is right adjoint

The unit η : Id → Forget ∘ Free embeds objects into their free algebras.
The counit ε : Free ∘ Forget → Id folds free algebra trees using algebra structure.
-/
def polyFreeForgetAdjunction (P : PolyEndo X) :
    polyFreeFunctor P ⊣ polyForgetFunctor P :=
  Adjunction.mkOfUnitCounit {
    unit := polyFreeUnitNat P
    counit := polyFreeCounitNat P
    left_triangle := by
      ext A : 2
      simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
        NatTrans.id_app', Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.whiskerLeft_app, Category.id_comp,
        polyFreeUnitNat, polyFreeCounitNat]
      exact polyFree_right_triangle P A
    right_triangle := by
      ext α : 2
      simp only [NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
        NatTrans.id_app', Functor.whiskerLeft_app, Functor.associator_inv_app,
        Functor.whiskerRight_app, Category.id_comp,
        polyFreeUnitNat, polyFreeCounitNat]
      exact polyFree_left_triangle P α
  }

/--
Left triangle identity for Forget ⊣ Cofree:
Applying the unit then the counit (on the Forget side) is the identity.

For β : PolyCoalg P, we have:
  polyCoalgUnit P β ≫ polyCofreeCounit β.V P = 𝟙 β.V

The unit embeds β.V elements into their cofree anamorphism trees,
and the counit extracts the root annotation, recovering the original element.
-/
lemma polyCofree_left_triangle (P : PolyEndo X) (β : PolyCoalg P) :
    polyCoalgUnit P β ≫ polyCofreeCounit β.V P = 𝟙 β.V := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, polyCoalgUnit, Over.homMk_left, polyCoalgUnitLeft,
    polyCofreeCounit, polyCofreeCounitLeft, types_comp_apply,
    Over.id_left, types_id_apply]
  simp only [polyCofreeExtract]
  simp only [PolyCofix.head, polyCoalgUnitAt, polyCoalgUnitApprox]
  have hx : (β.str.left a).fst = β.V.hom a := by
    have h := congrFun (Over.w β.str) a
    simp only at h
    exact h
  simp only [PolyCofixApprox.getIndex_cast _ _ hx]
  simp only [polyBetweenIndex, polyToOverIndex, polyScale, polyScaleAt, ccrIndex,
    ccrObjMk, polyScaleIndex]
  exact @prod_fst_val_transport' β.V.left X (fun v x => β.V.hom v = x)
    (fun x => (P x).base) _ _ hx a hx.symm (β.str.left a).snd.fst

/--
Right triangle identity for Forget ⊣ Cofree:
Applying the unit (on the Cofree side) then the counit is the identity.

For A : Over X, we have:
  polyCoalgUnitHom P (polyCofreeCoalg A P) ≫
    (polyCofreeFunctor P).map (polyCofreeCounit A P) = 𝟙 (polyCofreeCoalg A P)
-/
lemma polyCofree_right_triangle_approx (P : PolyEndo X) (A : Over X) (x : X)
    (m : PolyCofreeM A P x) (n : Nat) :
    polyCofreeMapApprox (polyCofreeCarrier A P) A P (polyCofreeCounit A P)
      (polyCoalgUnitApprox P (polyCofreeCoalg A P) n x ⟨⟨x, m⟩, rfl⟩) =
    m.approx n := by
  induction n generalizing x m with
  | zero =>
    simp only [polyCofreeMapApprox, polyCoalgUnitApprox]
    cases m.approx 0
    rfl
  | succ n ih =>
    have hidx_eq : (m.approx (n + 1)).getIndex = m.head := m.index_eq_head n
    generalize ha : m.approx (n + 1) = a at hidx_eq
    match a, hidx_eq with
    | .intro _ idx childFun, hidx_eq =>
      subst hidx_eq
      unfold polyCofreeMapApprox polyCoalgUnitApprox
      simp only [polyCofreeCoalg, polyCofreeStr, Over.homMk_left, polyCofreeStrLeft,
        polyCofreeStrFamily]
      congr 1
      funext e
      simp only [polyCofreeCounit, Over.homMk_left, polyCofreeCounitLeft]
      have hchildApprox : (m.children e).approx n = childFun e := by
        simp only [PolyCofix.children, PolyCofix.childApproxAt]
        cases n with
        | zero =>
          simp only [PolyCofix.childApproxAt_zero]
          exact (PolyCofixApprox.approx_zero_eq_continue (childFun e)).symm
        | succ k' =>
          simp only [PolyCofix.childApproxAt_succ]
          have heq1 : (m.approx (k' + 2)).getIndex = m.head := m.index_eq_head (k' + 1)
          conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head
            (m.approx (k' + 2)) (m.index_eq_head (k' + 1)) heq1 e]
          generalize haa : m.approx (k' + 2) = aa at heq1
          rw [ha] at haa
          subst haa
          conv_lhs => rw [PolyCofix.childApproxAt_succ_aux_proof_irrel m.head
            (.intro x m.head childFun) heq1 rfl e]
          exact PolyCofix.childApproxAt_succ_aux_intro m.head childFun e
      have h_child := ih ((polyBetweenFamily X X (polyScale A P) x
          (PolyCofix.head m)).hom e) (PolyCofix.children m e)
      rw [← hchildApprox]
      exact h_child

lemma polyCofree_right_triangle (P : PolyEndo X) (A : Over X) :
    polyCoalgUnitHom P (polyCofreeCoalg A P) ≫
      (polyCofreeFunctor P).map (polyCofreeCounit A P) =
    𝟙 (polyCofreeCoalg A P) := by
  apply Endofunctor.Coalgebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Endofunctor.Coalgebra.comp_f, polyCoalgUnitHom, polyCofreeFunctor,
    polyCofreeCoalgMap, Endofunctor.Coalgebra.id_f, Over.id_left,
    types_id_apply, Over.comp_left, Over.homMk_left, types_comp_apply,
    polyCoalgUnit, polyCoalgUnitLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofreeMap, Over.homMk_left, polyCofreeMapLeft]
    simp only [polyCofreeMapAt, polyCoalgUnitAt]
    apply PolyCofix.ext
    intro n
    exact polyCofree_right_triangle_approx P A x m n

/--
The adjunction Forget ⊣ Cofree for P-coalgebras.

For a polynomial endofunctor P on Over X:
- The forgetful functor polyCoalgForgetFunctor P : PolyCoalg P → Over X is left adjoint
- The cofree coalgebra functor polyCofreeFunctor P : Over X → PolyCoalg P is right adjoint

The unit η : Id → Cofree ∘ Forget unfolds coalgebra elements into their anamorphism trees.
The counit ε : Forget ∘ Cofree → Id extracts root annotations from cofree elements.
-/
def polyForgetCofreeAdjunction (P : PolyEndo X) :
    polyCoalgForgetFunctor P ⊣ polyCofreeFunctor P :=
  Adjunction.mkOfUnitCounit {
    unit := polyCoalgUnitNat P
    counit := polyCofreeCounitNat P
    left_triangle := by
      ext β : 2
      simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
        NatTrans.id_app', Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.whiskerLeft_app, Category.id_comp,
        polyCoalgUnitNat, polyCofreeCounitNat, polyCoalgForgetFunctor,
        Endofunctor.Coalgebra.forget_map, polyCoalgUnitHom]
      exact polyCofree_left_triangle P β
    right_triangle := by
      ext A : 2
      simp only [NatTrans.comp_app, Functor.id_obj, Functor.comp_obj,
        NatTrans.id_app', Functor.whiskerLeft_app, Functor.associator_inv_app,
        Functor.whiskerRight_app, Category.id_comp,
        polyCoalgUnitNat, polyCofreeCounitNat, polyCoalgForgetFunctor,
        polyCofreeFunctor, polyCofreeCoalgMap]
      exact polyCofree_right_triangle P A
  }

end Adjunctions

/-! ## Free Monad Monad and Cofree Comonad Comonad

The construction `P ↦ polyFreeMPoly P` (free monad) is itself a monad on the
category of polynomial endofunctors. Dually, `P ↦ polyCofreeMPoly P` (cofree
comonad) is a comonad on polynomial endofunctors.

These structures arise from the adjunctions Free ⊣ Forget and Forget ⊣ Cofree.
-/

section FreeMonadMonad

variable {X : Type u}

/-! ### Unit of the Free Monad Monad

The unit embeds each P-operation as a single-node tree in the free monad.
For each position `i` of P at fiber x, we get a tree shape consisting of
one internal node labeled `i` with leaves at all child positions.
-/

/--
Build a leaf node in a tree shape at the given fiber.
The leaf carries the fiber value itself (since overTerminal X has left = X).
-/
def polyFreeMShapeLeaf (P : PolyEndo X) (x : X) : PolyFreeMShape P x :=
  PolyFix.mk x (Sum.inl ⟨x, rfl⟩) (fun e => PEmpty.elim e)

/--
The leaf positions in a leaf node are exactly PUnit (one position).
-/
lemma polyFreeMShapeLeaf_leafPos (P : PolyEndo X) (x : X) :
    PolyFreeMLeafPos P (polyFreeMShapeLeaf P x) = PUnit := rfl

/--
Build a single-node tree shape from a P-position.
The tree has one internal node labeled by the position, with leaves at all
child positions.
-/
def polyFreeMShapeSingleNode (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x) : PolyFreeMShape P x :=
  PolyFix.mk x (Sum.inr i) fun e =>
    polyFreeMShapeLeaf P ((polyBetweenFamily X X P x i).hom e)

/--
The leaf positions in a single-node tree are a sigma of PUnits.
-/
lemma polyFreeMShapeSingleNode_leafPos (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x) :
    PolyFreeMLeafPos P (polyFreeMShapeSingleNode P i) =
    (Σ (e : (polyBetweenFamily X X P x i).left),
      PolyFreeMLeafPos P (polyFreeMShapeLeaf P
        ((polyBetweenFamily X X P x i).hom e))) := rfl

/--
Convert a child index and unit to a leaf position in a single-node tree.
-/
def polyFreeMShapeSingleNode_leafPos_mk (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x)
    (e : (polyBetweenFamily X X P x i).left) :
    PolyFreeMLeafPos P (polyFreeMShapeSingleNode P i) :=
  ⟨e, PUnit.unit⟩

/--
Extract the child index from a leaf position in a single-node tree.
-/
def polyFreeMShapeSingleNode_leafPos_fst (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x)
    (pos : PolyFreeMLeafPos P (polyFreeMShapeSingleNode P i)) :
    (polyBetweenFamily X X P x i).left :=
  pos.1

/--
The leaf positions in a single-node tree correspond exactly to the children
of that node (since each child is a leaf with exactly one position).
-/
def polyFreeMShapeSingleNode_leafPos_equiv (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x) :
    PolyFreeMLeafPos P (polyFreeMShapeSingleNode P i) ≃
    (polyBetweenFamily X X P x i).left where
  toFun := polyFreeMShapeSingleNode_leafPos_fst P i
  invFun := polyFreeMShapeSingleNode_leafPos_mk P i
  left_inv := fun pos => by
    simp only [polyFreeMShapeSingleNode_leafPos_fst, polyFreeMShapeSingleNode_leafPos_mk]
    cases pos.2
    rfl
  right_inv := fun _ => rfl

/--
The fiber of a leaf position in a single-node tree is the fiber of the
corresponding child.
-/
lemma polyFreeMShapeSingleNode_leafFiber (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x)
    (pos : PolyFreeMLeafPos P (polyFreeMShapeSingleNode P i)) :
    PolyFreeMLeafFiber P (polyFreeMShapeSingleNode P i) pos =
    (polyBetweenFamily X X P x i).hom
      ((polyFreeMShapeSingleNode_leafPos_equiv P i).toFun pos) := by
  simp only [polyFreeMShapeSingleNode_leafPos_equiv,
    polyFreeMShapeSingleNode_leafPos_fst]
  rfl

/--
The family at a single-node position equals the original P family.
This is the isomorphism that makes the unit work.
-/
def polyFreeMShapeSingleNode_family_iso (P : PolyEndo X) {x : X}
    (i : polyBetweenIndex X X P x) :
    polyFreeMFamily P x (polyFreeMShapeSingleNode P i) ≅
    polyBetweenFamily X X P x i :=
  Over.isoMk
    (Equiv.toIso (polyFreeMShapeSingleNode_leafPos_equiv P i))
    (by
      ext pos
      simp only [types_comp_apply, Equiv.toIso_hom, polyFreeMFamily, Over.mk_hom]
      exact polyFreeMShapeSingleNode_leafFiber P i pos)

/--
The left component of the free monad monad unit at a specific fiber.
Maps each P-evaluation element to a polyFreeMPoly P evaluation by embedding
as a single-node tree.
-/
def polyFreeMMonadUnitAtLeft (P : PolyEndo X) (A : Over X) (x : X)
    (elem : polyBetweenEvalFamily X X P A x) :
    polyBetweenEvalFamily X X (polyFreeMPoly P) A x :=
  let i := pbefIndex elem
  let mor := pbefMor elem
  let treeShape := polyFreeMShapeSingleNode P i
  let newMor : polyFreeMFamily P x treeShape ⟶ A :=
    (polyFreeMShapeSingleNode_family_iso P i).hom ≫ mor
  ⟨treeShape, newMor⟩

/--
The left component of the unit as a function on total spaces.
-/
def polyFreeMMonadUnitLeft (P : PolyEndo X) (A : Over X) :
    ((polyEndoFunctor X P).obj A).left →
    ((polyEndoFunctor X (polyFreeMPoly P)).obj A).left :=
  fun ⟨x, elem⟩ => ⟨x, polyFreeMMonadUnitAtLeft P A x elem⟩

/--
The unit commutes with fiber projections.
-/
lemma polyFreeMMonadUnit_comm (P : PolyEndo X) (A : Over X) :
    polyFreeMMonadUnitLeft P A ≫
    ((polyEndoFunctor X (polyFreeMPoly P)).obj A).hom =
    ((polyEndoFunctor X P).obj A).hom := rfl

/--
The unit of the free monad monad at a specific polynomial P.
Maps P(A) → (polyFreeMPoly P)(A) naturally in A.
-/
def polyFreeMMonadUnit (P : PolyEndo X) :
    polyEndoFunctor X P ⟶ polyEndoFunctor X (polyFreeMPoly P) where
  app := fun A => Over.homMk (polyFreeMMonadUnitLeft P A)
    (polyFreeMMonadUnit_comm P A)
  naturality := fun A B f => by
    apply Over.OverMorphism.ext
    funext ⟨x, ⟨i, mor⟩⟩
    simp only [types_comp_apply, Over.comp_left,
      polyEndoFunctor, polyBetweenEvalFunctor, polyToOverFunctor,
      polyToOverEvalMap, familySliceForward, familySliceForwardMap,
      polyToOverEvalFamilyMap, ccrEvalMap, Over.homMk_left,
      polyFreeMMonadUnitLeft, polyFreeMMonadUnitAtLeft,
      pbefIndex, pbefMor, ptoefIndex, ptoefMor, ccrEvalIndex, ccrEvalMor,
      Category.assoc]

/--
The shape is preserved by polyFreeMapAt: mapping only changes leaf values,
not tree structure.
-/
theorem polyFreeMToShape_map (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X} (t : PolyFreeM A P x) :
    polyFreeMToShape B P (polyFreeMapAt A B P f x t) = polyFreeMToShape A P t := by
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      simp only [polyFreeMapAt, polyFreeMBind, polyFreeMPure, polyFreeMToShape]
    | inr p =>
      simp only [polyFreeMapAt, polyFreeMBind, polyFreeMToShape]
      congr 1
      funext e
      exact ih e

/-! ### Multiplication of the Free Monad Monad

The multiplication flattens trees-of-trees into trees. We first define a
"graft" operation that substitutes subtrees at the leaves of a shape, then
use this to define the join operation.
-/

/--
Graft subtrees at the leaves of a tree shape.
Given a shape `s` and a function `f` assigning a subtree to each leaf position,
produce a tree by substituting each leaf with its corresponding subtree.
-/
def polyFreeMGraft (A : Over X) (P : PolyEndo X) {x : X}
    (s : PolyFreeMShape P x)
    (f : ∀ pos : PolyFreeMLeafPos P s, PolyFreeM A P (PolyFreeMLeafFiber P s pos)) :
    PolyFreeM A P x :=
  match s with
  | PolyFix.mk _ (Sum.inl _) _ => f PUnit.unit
  | PolyFix.mk _ (Sum.inr p) children =>
    PolyFix.mk x (Sum.inr p) fun e =>
      polyFreeMGraft A P (children e) fun pos => f ⟨e, pos⟩

/--
The join operation for the free monad monad.
Flattens a tree over `polyFreeMPoly P` into a tree over P by grafting
the inner P-tree structures at each node.
-/
def polyFreeMJoin (A : Over X) (P : PolyEndo X) {x : X} :
    PolyFreeM A (polyFreeMPoly P) x → PolyFreeM A P x
  | PolyFix.mk _ (Sum.inl a) _ => polyFreeMPure A P a
  | PolyFix.mk _ (Sum.inr s) children =>
    polyFreeMGraft A P s fun pos =>
      polyFreeMJoin A P (children pos)

/--
Grafting commutes with bind: the bind distributes through a graft.
-/
theorem polyFreeMGraft_bind (A B : Over X) (P : PolyEndo X)
    (g : ∀ y, { a : A.left // A.hom a = y } → PolyFreeM B P y) {x : X}
    (s : PolyFreeMShape P x)
    (h : ∀ pos : PolyFreeMLeafPos P s, PolyFreeM A P (PolyFreeMLeafFiber P s pos)) :
    polyFreeMBind A B P (polyFreeMGraft A P s h) g =
    polyFreeMGraft B P s (fun pos => polyFreeMBind A B P (h pos) g) := by
  induction s with
  | mk y idx children ih =>
    cases idx with
    | inl label =>
      simp only [polyFreeMGraft]
    | inr p =>
      simp only [polyFreeMGraft, polyFreeMBind]
      congr 1
      funext e
      exact ih e (fun pos => h ⟨e, pos⟩)

/--
Join is natural in A: polyFreeMapAt commutes with polyFreeMJoin.
-/
theorem polyFreeMJoin_natural (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) {x : X}
    (t : PolyFreeM A (polyFreeMPoly P) x) :
    polyFreeMapAt A B P f x (polyFreeMJoin A P t) =
    polyFreeMJoin B P (polyFreeMapAt A B (polyFreeMPoly P) f x t) := by
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      simp only [polyFreeMJoin, polyFreeMPure, polyFreeMapAt, polyFreeMBind]
    | inr s =>
      simp only [polyFreeMJoin, polyFreeMapAt, polyFreeMBind]
      rw [polyFreeMGraft_bind]
      congr 1
      funext pos
      exact ih pos

/--
polyFreeMFromShape with composed morphism equals polyFreeMapAt applied to the original.
-/
theorem polyFreeMFromShape_map (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) {x : X}
    (shape : PolyFreeMShape P x)
    (leafData : (pos : PolyFreeMLeafPos P shape) →
      { a : A.left // A.hom a = PolyFreeMLeafFiber P shape pos }) :
    polyFreeMFromShape B P shape
      (fun pos => ⟨f.left (leafData pos).val,
        (congrFun (Over.w f) (leafData pos).val).trans (leafData pos).property⟩) =
    polyFreeMapAt A B P f x (polyFreeMFromShape A P shape leafData) := by
  induction shape with
  | mk y idx children ih =>
    cases idx with
    | inl label =>
      simp only [polyFreeMFromShape, polyFreeMapAt, polyFreeMBind, polyFreeMPure]
    | inr p =>
      simp only [polyFreeMFromShape, polyFreeMapAt, polyFreeMBind]
      congr 1
      funext e
      exact ih e (fun pos => leafData ⟨e, pos⟩)

end FreeMonadMonad

end GebLean
