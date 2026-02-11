import GebLean.PolyAlg
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

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
- Constructive fiber product infrastructure via mathlib pullbacks
- `overSelfProdFunctor`: the self-product functor `A ↦ A ×_X A`
- Natural isomorphism between the polynomial evaluation and
  the self-product functor
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

/-! ## Constructive self-product in Over X

Products in `Over X` are pullbacks in the base category.
For `A : Over X`, the self-product `A ×_X A` has underlying
type `{ p : A.left × A.left // A.hom p.1 = A.hom p.2 }`.

We build the product constructively using:
- `Types.pullbackCone` / `Types.pullbackLimitCone` for
  the computable pullback in `Type`
- `pullbackConeEquivBinaryFan` to convert to a binary fan
  in `Over X`
- `IsLimit.pullbackConeEquivBinaryFanFunctor` to transfer
  the limit property
-/

section OverSelfProd

variable {X : Type u}

/--
The pullback cone for `A.hom` with itself in `Type`.
-/
def overSelfPullbackCone (A : Over X) :
    PullbackCone A.hom A.hom :=
  Types.pullbackCone A.hom A.hom

/--
The pullback cone `overSelfPullbackCone A` is a limit.
-/
def overSelfPullbackIsLimit (A : Over X) :
    IsLimit (overSelfPullbackCone A) :=
  (Types.pullbackLimitCone A.hom A.hom).isLimit

/--
The binary fan in `Over X` corresponding to the self-pullback
of `A`.
-/
def overSelfProdFan (A : Over X) :
    BinaryFan A A :=
  pullbackConeEquivBinaryFan.functor.obj
    (overSelfPullbackCone A)

/--
The binary fan `overSelfProdFan A` is a limit in `Over X`.
-/
def overSelfProdIsLimit (A : Over X) :
    IsLimit (overSelfProdFan A) :=
  IsLimit.pullbackConeEquivBinaryFanFunctor
    (overSelfPullbackIsLimit A)

/--
The self-product object `A ×_X A` in `Over X`.
-/
abbrev overSelfProd (A : Over X) : Over X :=
  (overSelfProdFan A).pt

/--
First projection `A ×_X A ⟶ A`.
-/
abbrev overSelfProdFst (A : Over X) :
    overSelfProd A ⟶ A :=
  (overSelfProdFan A).fst

/--
Second projection `A ×_X A ⟶ A`.
-/
abbrev overSelfProdSnd (A : Over X) :
    overSelfProd A ⟶ A :=
  (overSelfProdFan A).snd

/--
Lift a morphism `f : A ⟶ B` to the self-product via the
universal property: `(fst ≫ f, snd ≫ f)`.
-/
def overSelfProdMap {A B : Over X} (f : A ⟶ B) :
    overSelfProd A ⟶ overSelfProd B :=
  (overSelfProdIsLimit B).lift
    (BinaryFan.mk
      (overSelfProdFst A ≫ f)
      (overSelfProdSnd A ≫ f))

end OverSelfProd

/-! ## The self-product functor -/

section OverSelfProdFunctor

variable (X : Type u)

/--
The self-product functor `A ↦ A ×_X A` on `Over X`.

On morphisms, `f : A ⟶ B` maps to the universal lift of
`(fst ≫ f, snd ≫ f)` into `B ×_X B`.
-/
def overSelfProdFunctor : Over X ⥤ Over X where
  obj := overSelfProd
  map := overSelfProdMap
  map_id := fun A => by
    apply (overSelfProdIsLimit A).hom_ext
    intro ⟨j⟩
    simp only [Category.id_comp]
    exact (overSelfProdIsLimit A).fac _ _
  map_comp := fun {A B C} f g => by
    symm
    apply (overSelfProdIsLimit C).hom_ext
    intro ⟨j⟩
    simp only [overSelfProdMap, Category.assoc,
      (overSelfProdIsLimit C).fac,
      BinaryFan.mk]
    cases j
    all_goals {
      simp only []
      rw [← Category.assoc,
        (overSelfProdIsLimit B).fac]
      simp only [Category.assoc]
    }

end OverSelfProdFunctor

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

/-! ## PUnit specialization

When `X = PUnit`, the fiber condition `A.hom a₁ = A.hom a₂`
is trivially satisfied, so the self-product reduces to the
ordinary product.
-/

section PUnitSpecialization

/--
The product polynomial endofunctor specialized to `PUnit`.
-/
abbrev polyProdType : PolyEndo PUnit.{u + 1} :=
  polyProd PUnit.{u + 1}

/--
When `X = PUnit`, the self-product type is equivalent to
the ordinary product, since the fiber condition is trivially
satisfied.
-/
def overSelfProd_punit_equiv
    (A : Over PUnit.{u + 1}) :
    (overSelfProd A).left ≃ A.left × A.left where
  toFun := fun ⟨⟨a₁, a₂⟩, _⟩ => (a₁, a₂)
  invFun := fun ⟨a₁, a₂⟩ =>
    ⟨⟨a₁, a₂⟩, by
      have : ∀ (x y : PUnit.{u + 1}), x = y :=
        fun x y => by cases x; cases y; rfl
      exact this _ _⟩
  left_inv := fun ⟨_, _⟩ => by
    rfl
  right_inv := fun _ => rfl

end PUnitSpecialization

end GebLean
