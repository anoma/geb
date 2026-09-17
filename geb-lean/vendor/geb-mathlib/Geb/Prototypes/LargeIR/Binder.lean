/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LargeIR.General

set_option doc.verso true in
/-!
# Prototype: the binder of a universe is not a walking-arrow functor

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

A universe closed under dependent products is an inductive-recursive
definition whose product former takes a code {lit}`a` and a family of codes
{lit}`b : T a → U` indexed by the terms of {lit}`a`, decoding to the
dependent product {lit}`Π x : T a, T (b x)`. As a code it is
{lit}`δ 1 (fun T₀ ↦ δ (T₀ ()) (fun T₁ ↦ ι (Π T₁)))`, whose inner {lit}`δ` has
the arity {lit}`T₀ ()`, a decoding rather than a fixed set. On families this
is the assignment {lit}`(U, T) ↦ Σ (a : U), Σ (b : T a → U), Π (x : T a), T (b x)`,
whose component {lit}`b : T a → U` is contravariant in the fibre {lit}`T a`,
so it is not a covariant functor on {lit}`Fam(Type)` with its morphisms
proper, and the interpretation of large inductive-recursive definitions of
\[GhaniNordvallForsbergMalatesta2015\] accordingly reaches it only over
{lit}`Fam(Cᵒᵖ)` or over groupoids. The repository's
{name}`PresheafIRUniv.univPsh` met the same obstruction: its formers are
binary, the family of codes under the binder dropped.

This module states the obstruction against walking-arrow presheaf polynomial
functors, whose values {name}`GebProto.LargeIR.elemEquiv` computes as a shape
with a base assignment on a fixed set of level-{lit}`0` directions and an
assignment on a fixed set of level-{lit}`1` directions. At the presheaf
{lit}`termsPsh n` with one code and {lit}`n` terms, the product former's
level-{lit}`1` value is {lit}`Fin n → Fin n`, {lit}`piFormerEquiv`, a family
of types no fixed direction sets produce: {lit}`not_piFormer` shows that no
walking-arrow presheaf polynomial functor has level-{lit}`1` values in
bijection with the product former's at every {lit}`termsPsh n`, the bijections
at {lit}`n = 0` and {lit}`n = 1` forcing a single level-{lit}`1` shape with no
level-{lit}`1` directions, whose value at {lit}`n = 2` is then a point rather
than the four functions {lit}`Fin 2 → Fin 2`. The bijections are not asked to
be natural.

## Main definitions

* {lit}`termsPsh` — the walking-arrow presheaf with one code and {lit}`n`
  terms.
* {lit}`PiFormerValue` — the level-{lit}`1` value of the dependent-product
  former at a walking-arrow presheaf.

## Main statements

* {lit}`piFormerEquiv` — at {lit}`termsPsh n` the product former's value is
  {lit}`Fin n → Fin n`.
* {lit}`not_piFormer` — no walking-arrow presheaf polynomial functor has the
  product former's values.

## References

* \[GhaniNordvallForsbergMalatesta2015\]
* \[DybjerSetzer2003\]

## Tags

prototype, universe, dependent product, inductive-recursive, walking arrow,
variance
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec

namespace GebProto.LargeIR

/-- The walking-arrow presheaf with one code and {lit}`n` terms. -/
def termsPsh (n : ℕ) : (Fin 2)ᵒᵖ ⥤ Type :=
  ofSlice fun _ : Fin n ↦ ()

/-- The code fibre of {lit}`termsPsh n` is a point. -/
theorem termsPsh_zero_eq {n : ℕ} (x y : (termsPsh n).obj ⟨0⟩) : x = y :=
  Subsingleton.elim (α := Unit) x y

/-- The level-{lit}`1` value of the dependent-product former at a walking-arrow
presheaf: a code, a family of codes indexed by its terms, and a term of each
member of the family. -/
def PiFormerValue (Z : (Fin 2)ᵒᵖ ⥤ Type) : Type :=
  Σ a : Z.obj ⟨0⟩, Σ b : (famOfPsh Z).2 a → Z.obj ⟨0⟩, ∀ x, (famOfPsh Z).2 (b x)

/-- At {lit}`termsPsh n` the product former's value is {lit}`Fin n → Fin n`. -/
def piFormerEquiv (n : ℕ) : PiFormerValue (termsPsh n) ≃ (Fin n → Fin n) where
  toFun v i := (v.2.2 ⟨i, termsPsh_zero_eq _ _⟩).1
  invFun f := ⟨(), fun _ ↦ (), fun x ↦ ⟨f x.1, rfl⟩⟩
  left_inv v := by
    obtain ⟨a, b, t⟩ := v
    obtain rfl : a = () := termsPsh_zero_eq _ _
    obtain rfl : b = fun _ ↦ () := funext fun _ ↦ termsPsh_zero_eq _ _
    rfl
  right_inv _ := rfl

/-- The level-{lit}`1` elements of a functor's value at {lit}`termsPsh n` in
dependent-type terms. -/
abbrev TermsElem (F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2)) (n : ℕ) : Type :=
  ElemAt F (termsPsh n) 1

/-- An element at a level-{lit}`1` shape with every term the term {lit}`0`. -/
def termsElemMk (F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2)) (a : F.Shape 1) :
    TermsElem F 1 :=
  ⟨a, fun _ ↦ (), fun _ ↦ ⟨(0 : Fin 1), rfl⟩⟩

/-- No walking-arrow presheaf polynomial functor has level-{lit}`1` values in
bijection with the dependent-product former's at every {lit}`termsPsh n`. -/
theorem not_piFormer (F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2))
    (e : ∀ n : ℕ, { x : F.obj (termsPsh n) // F.q x.shape = 1 } ≃ PiFormerValue (termsPsh n)) :
    False := by
  have e' : ∀ n, TermsElem F n ≃ (Fin n → Fin n) := fun n ↦
    (objLevel F (termsPsh n) 1).symm.trans ((e n).trans (piFormerEquiv n))
  -- At `n = 1` the value is a point, so there is one level-`1` shape.
  have hshape : ∀ a a' : F.Shape 1, a = a' := by
    intro a a'
    have h : (e' 1) (termsElemMk F a) = (e' 1) (termsElemMk F a') :=
      funext fun _ ↦ Subsingleton.elim _ _
    exact congrArg Sigma.fst ((e' 1).injective h)
  -- At `n = 0` the value is a point, so that shape has no level-`1` directions.
  have hdir : ∀ (a : F.Shape 1), F.Direction a.1 1 → False := by
    intro a d
    have x₀ : TermsElem F 0 := (e' 0).symm fun i ↦ i
    have h : x₀.1 = a := hshape _ _
    subst h
    exact (x₀.2.2 d).1.elim0
  -- Then the value at every `n` is a point.
  have hsub : ∀ x y : TermsElem F 2, x = y := by
    intro x y
    obtain ⟨a, g, w⟩ := x
    obtain ⟨a', g', w'⟩ := y
    obtain rfl : a = a' := hshape a a'
    obtain rfl : g = g' := funext fun _ ↦ termsPsh_zero_eq _ _
    exact congrArg (fun w ↦ (⟨a, g, w⟩ : TermsElem F 2)) (funext fun d ↦ (hdir a d).elim)
  -- But `Fin 2 → Fin 2` is not.
  exact Fin.zero_ne_one
    (congrFun ((e' 2).symm.injective (a₁ := fun i ↦ i) (a₂ := fun _ ↦ 0) (hsub _ _)) 1).symm

end GebProto.LargeIR
