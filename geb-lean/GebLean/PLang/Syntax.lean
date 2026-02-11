import GebLean.PolyAlg
import GebLean.Utilities.Slice

/-!
# Programming Language Syntax

Defines a generic syntax for programming languages based on
binary trees.

Binary trees with labels from a type `A` form the free monad of
the product functor applied to `A`. The product functor
(`A ↦ A ×_X A` in the slice category `Over X`) is polynomial:
at each fiber point `x : X`, there is one position with a
two-element fiber (`PUnit ⊕ PUnit`) mapping constantly to `x`.

This module defines:
- `polyProd`: the product polynomial endofunctor on `Over X`
- Natural isomorphism between the polynomial evaluation and
  the self-product functor (from `Utilities/Slice.lean`)
- Specialization to `Type` via `X = PUnit`
-/

namespace GebLean

open CategoryTheory Limits

universe u

/-! ## The product polynomial endofunctor -/

section PolyProd

variable (X : Type u)

/--
The product polynomial endofunctor on `Over X`.

At each `x : X`, there is one position (`PUnit`) with a
two-element fiber (`PUnit ⊕ PUnit`) mapping constantly to `x`.
Evaluation at `(A, f)` yields pairs of elements in `f⁻¹(x)`.
-/
def polyProd : PolyEndo X :=
  fun x => ccrObjMk
    (fun _ : PUnit.{u + 1} =>
      Over.mk
        (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} => x))

lemma polyProd_index (x : X) :
    polyBetweenIndex X X (polyProd X) x =
      PUnit.{u + 1} := rfl

lemma polyProd_family (x : X)
    (i : polyBetweenIndex X X (polyProd X) x) :
    polyBetweenFamily X X (polyProd X) x i =
      Over.mk
        (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
          x) := rfl

end PolyProd

/-! ## Equivalence between polynomial evaluation and
self-product

We show that `polyBetweenEval X X (polyProd X) A` is
isomorphic to `overSelfProd A` in `Over X`, following the
pattern of `polyBetweenId_eval_iso`.
-/

section PolyProdEquiv

variable {X : Type u}

/--
Fiber-level equivalence: at each `x : X`, the polynomial
evaluation family is equivalent to the product of fibers.
-/
def polyProd_eval_fiberEquiv (A : Over X) (x : X) :
    polyBetweenEvalFamily X X (polyProd X) A x ≃
      ({ a : A.left // A.hom a = x } ×
       { a : A.left // A.hom a = x }) where
  toFun := fun ⟨_, f⟩ =>
    (⟨f.left (Sum.inl PUnit.unit),
      congrFun (Over.w f) (Sum.inl PUnit.unit)⟩,
     ⟨f.left (Sum.inr PUnit.unit),
      congrFun (Over.w f) (Sum.inr PUnit.unit)⟩)
  invFun := fun ⟨⟨a₁, h₁⟩, ⟨a₂, h₂⟩⟩ =>
    ⟨PUnit.unit, Over.homMk
      (fun s => match s with
        | Sum.inl _ => a₁
        | Sum.inr _ => a₂)
      (by funext s; cases s <;> assumption)⟩
  left_inv := fun ⟨i, f⟩ => by
    cases i
    simp only [polyBetweenEvalFamily, polyProd,
      ccrObjMk, ccrIndex, ccrFamily]
    congr 1
    apply Over.OverMorphism.ext
    funext s
    cases s <;> rfl
  right_inv := fun ⟨_, _⟩ => rfl

/--
Equivalence between the left component of the polynomial
evaluation and the left component of the self-product.
-/
def polyProd_eval_leftEquiv (A : Over X) :
    (polyBetweenEval X X (polyProd X) A).left ≃
      (overSelfProd A).left where
  toFun := fun ⟨x, ⟨_, f⟩⟩ =>
    ⟨⟨f.left (Sum.inl PUnit.unit),
      f.left (Sum.inr PUnit.unit)⟩,
     (congrFun (Over.w f) (Sum.inl PUnit.unit)).trans
       (congrFun (Over.w f) (Sum.inr PUnit.unit)).symm⟩
  invFun := fun ⟨⟨a₁, a₂⟩, h⟩ =>
    ⟨A.hom a₁, ⟨PUnit.unit, Over.homMk
      (fun s => match s with
        | Sum.inl _ => a₁
        | Sum.inr _ => a₂)
      (by funext s; cases s with
        | inl => rfl
        | inr => exact h.symm)⟩⟩
  left_inv := fun ⟨x, ⟨i, f⟩⟩ => by
    cases i
    simp only [polyBetweenEval, polyProd,
      ccrObjMk, ccrIndex, ccrFamily]
    have hw : A.hom (f.left (Sum.inl PUnit.unit)) =
        x :=
      congrFun (Over.w f) (Sum.inl PUnit.unit)
    refine Sigma.ext hw ?_
    simp only
    congr 1
    · funext _; simp only [hw]
    · have hsrc :
          (Over.mk (Y := PUnit.{u + 1} ⊕ PUnit.{u + 1})
            (fun _ =>
              A.hom
                (f.left (Sum.inl PUnit.unit)))
            : Over X) =
          Over.mk
            (fun _ : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
              x) := by
        simp only [hw]
      have hfl :
          f.left = fun s => match s with
            | Sum.inl _ =>
              f.left (Sum.inl PUnit.unit)
            | Sum.inr _ =>
              f.left (Sum.inr PUnit.unit) := by
        funext s; cases s <;> rfl
      refine heq_of_cast_eq ?_ ?_
      · exact congrArg (fun s => s ⟶ A) hsrc
      · apply Over.OverMorphism.ext
        funext p
        rw [congrFun hfl p]
        rw [GebLean.over_cast_left hsrc]
        simp only [Over.homMk_left]
        cases p <;> rfl
  right_inv := fun _ => rfl

/--
The evaluation of the product polynomial at `A : Over X` is
isomorphic to `overSelfProd A` in the slice category `Over X`.
-/
def polyProd_eval_iso (A : Over X) :
    polyBetweenEval X X (polyProd X) A ≅
      overSelfProd A :=
  Over.isoMk (polyProd_eval_leftEquiv A).toIso (by
    funext ⟨x, ⟨_, f⟩⟩
    exact congrFun (Over.w f) (Sum.inl PUnit.unit))

end PolyProdEquiv

/-! ## Natural isomorphism -/

section PolyProdNatIso

variable (X : Type u)

/--
The polynomial evaluation functor for `polyProd X` is
naturally isomorphic to the self-product functor on `Over X`.
-/
def polyProdNatIso :
    polyEndoFunctor X (polyProd X) ≅
      overSelfProdFunctor X :=
  NatIso.ofComponents
    (fun A => polyProd_eval_iso A)
    (fun {A B} f => by
      apply (overSelfProdIsLimit B).hom_ext
      intro ⟨j⟩
      apply Over.OverMorphism.ext
      funext p
      simp only [overSelfProdFunctor,
        overSelfProdMap, polyEndoFunctor,
        polyBetweenEvalFunctor]
      cases j <;> rfl)

end PolyProdNatIso

/-! ## PUnit specialization -/

section PUnitSpecialization

/--
The product polynomial endofunctor specialized to `PUnit`.
-/
abbrev polyProdType : PolyEndo PUnit.{u + 1} :=
  polyProd PUnit.{u + 1}

end PUnitSpecialization

end GebLean
