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

lemma PolyCofixApprox.approx_zero_eq_continue {P : PolyEndo X} {x : X}
    (a : PolyCofixApprox P 0 x) : a = PolyCofixApprox.continue x := by
  match a with
  | .continue _ => rfl

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

end PolyCofixTerminal

end GebLean
