/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Carrier
public import Geb.Prototypes.QuotientPRA.Basic


set_option doc.verso true in
/-!
# Endpoints of presheaf W-type constructors are constructor applications

Restricting a tree of a carrier presheaf ({name}`PresheafPFunctor.carrier`), the
W-type or the M-type of a presheaf polynomial endofunctor, along a morphism
{lit}`g` rebuilds its root: the restricted tree's root shape is {lit}`shapeRestr g`
of the original root shape, and its children are children of the original
({name}`PresheafPFunctor.restrTree`).
So the root shape of a restriction depends only on the root shape of the tree
({lit}`head_map`). If a family of trees all have one root shape, their restrictions
along {lit}`g` all have one root shape too ({lit}`head_map_of_head_eq`).

In a quotient presheaf polynomial functor ({lit}`GebProto.QuotientPRA.W`) the
endpoints of a witness are its restrictions along the two parallel morphisms, and the
index of a dependent term is its restriction along a morphism of the base. A
constructor of fixed shape therefore has endpoints, and gives terms indices, whose
root shapes are fixed. Reflexivity, symmetry, transitivity and transport require
endpoints or indices that are arguments of the constructor, whose root shapes vary,
so as soon as two arguments have different root shapes none of them is a constructor
of fixed shape: {lit}`no_uniform_refl`, {lit}`no_uniform_symm`,
{lit}`no_uniform_trans` and {lit}`no_uniform_transport`.

## Main definitions

* {lit}`head` — the root shape of a tree of a carrier presheaf.

## Main statements

* {lit}`head_map` — the root shape of a restriction is the restriction of the root
  shape.
* {lit}`head_map_of_head_eq` — restriction sends trees of one root shape to trees of
  one root shape.
* {lit}`no_uniform_refl`, {lit}`no_uniform_symm`, {lit}`no_uniform_trans`,
  {lit}`no_uniform_transport` — reflexivity, symmetry, transitivity and transport
  are not constructors of fixed shape once two arguments differ in root shape.

## Implementation notes

The statements quantify over an arbitrary function into the W-type rather than over
shapes of the functor, so they exclude any constructor whose applications all have
one root shape, however its arguments are arranged. Constructors indexed by the root
shape of an argument escape the argument: reflexivity at a term whose root shape is
{lit}`c` can be a witness constructor whose two endpoints are both {lit}`c` applied to
the constructor's arguments.

The statements hold over every carrier presheaf, so they exclude the same
constructors from the coinductive variant, whose trees are those of the M-type.

## References

* \[Weber2007\]

## Tags

W-type, presheaf, parametric right adjoint, restriction, quotient,
quotient inductive-inductive type
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

universe uC uA uB vC uI vI u

section Head

variable {C : Type uC} [Category.{vC} C] {F : PresheafPFunctor.{uC, uC, uA, uB, vC, vC} C C}
  {S : SlicePFunctor.FixedPoint.{max uA uB} F.toSlicePFunctor} (N : F.HereditaryNaturality S)

/-- The root shape of a tree of the carrier presheaf. -/
def head {c : C} (w : (F.carrier N).obj ⟨c⟩) : F.A := (S.dest w.down.1).1.1

/-- The root shape of a restriction along {lit}`g` is {lit}`shapeRestr g` of the root
shape. -/
theorem head_map {c c' : C} (g : c' ⟶ c) (w : (F.carrier N).obj ⟨c⟩) :
    head N ((F.carrier N).map g.op w) =
      (F.shapeRestr g ⟨head N w, (F.q_dest S w.down.1).trans w.down.2.1⟩).1 :=
  congrArg (fun x ↦ x.1.1) (S.dest_mk _)

/-- Restriction along {lit}`g` sends a family of trees all of root shape {lit}`ρ` to a
family of trees all of root shape {lit}`shapeRestr g ρ`. -/
theorem head_map_of_head_eq {A : Sort u} {c c' : C} (g : c' ⟶ c)
    (s : A → (F.carrier N).obj ⟨c⟩) (ρ : F.Shape c) (hs : ∀ a, head N (s a) = ρ.1) (a : A) :
    head N ((F.carrier N).map g.op (s a)) = (F.shapeRestr g ρ).1 :=
  (head_map N g (s a)).trans
    (congrArg (fun r ↦ (F.shapeRestr g r).1) (Subtype.ext (hs a)))

end Head

variable {I : Type uI} [Category.{vI} I]
  {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} (I × WalkingParallelPair)
    (I × WalkingParallelPair)}
  {S : SlicePFunctor.FixedPoint.{max uA uB} F.toSlicePFunctor} (N : F.HereditaryNaturality S)

/-- Reflexivity is not a witness constructor of fixed shape: a function sending each
term to a witness with that term as source, all of one root shape, makes all terms
have one root shape. -/
theorem no_uniform_refl {i : I} (t₁ t₂ : (F.carrier N).obj ⟨termObj i⟩)
    (h : head N t₁ ≠ head N t₂) :
    ¬ ∃ (ρ : F.Shape (eqObj i))
      (refl : (F.carrier N).obj ⟨termObj i⟩ → (F.carrier N).obj ⟨eqObj i⟩),
      (∀ t, head N (refl t) = ρ.1) ∧ ∀ t, src (F.carrier N) i (refl t) = t := by
  rintro ⟨ρ, refl, hρ, hsrc⟩
  have key := head_map_of_head_eq N (srcHom i) refl ρ hρ
  exact h (((congrArg (head N) (hsrc t₁)).symm.trans (key t₁)).trans
    ((key t₂).symm.trans (congrArg (head N) (hsrc t₂))))

/-- Symmetry is not a witness constructor of fixed shape: a function sending each
witness to one whose source is the original's target, all of one root shape, makes
the targets of all witnesses have one root shape. -/
theorem no_uniform_symm {i : I} (e₁ e₂ : (F.carrier N).obj ⟨eqObj i⟩)
    (h : head N (tgt (F.carrier N) i e₁) ≠ head N (tgt (F.carrier N) i e₂)) :
    ¬ ∃ (ρ : F.Shape (eqObj i))
      (symm : (F.carrier N).obj ⟨eqObj i⟩ → (F.carrier N).obj ⟨eqObj i⟩),
      (∀ e, head N (symm e) = ρ.1) ∧
        ∀ e, src (F.carrier N) i (symm e) = tgt (F.carrier N) i e := by
  rintro ⟨ρ, symm, hρ, hsrc⟩
  have key := head_map_of_head_eq N (srcHom i) symm ρ hρ
  exact h (((congrArg (head N) (hsrc e₁)).symm.trans (key e₁)).trans
    ((key e₂).symm.trans (congrArg (head N) (hsrc e₂))))

/-- Transitivity is not a witness constructor of fixed shape: a function sending each
composable pair of witnesses to one whose source is the first witness's source, all
of one root shape, makes the sources of all first witnesses of composable pairs have
one root shape. -/
theorem no_uniform_trans {i : I}
    (p₁ p₂ : {p : (F.carrier N).obj ⟨eqObj i⟩ × (F.carrier N).obj ⟨eqObj i⟩ //
      tgt (F.carrier N) i p.1 = src (F.carrier N) i p.2})
    (h : head N (src (F.carrier N) i p₁.1.1) ≠ head N (src (F.carrier N) i p₂.1.1)) :
    ¬ ∃ (ρ : F.Shape (eqObj i))
      (trans : {p : (F.carrier N).obj ⟨eqObj i⟩ × (F.carrier N).obj ⟨eqObj i⟩ //
        tgt (F.carrier N) i p.1 = src (F.carrier N) i p.2} → (F.carrier N).obj ⟨eqObj i⟩),
      (∀ p, head N (trans p) = ρ.1) ∧
        ∀ p, src (F.carrier N) i (trans p) = src (F.carrier N) i p.1.1 := by
  rintro ⟨ρ, trans, hρ, hsrc⟩
  have key := head_map_of_head_eq N (srcHom i) trans ρ hρ
  exact h (((congrArg (head N) (hsrc p₁)).symm.trans (key p₁)).trans
    ((key p₂).symm.trans (congrArg (head N) (hsrc p₂))))

/-- Transport along a morphism {lit}`f : i' ⟶ i` is not a term constructor of fixed
shape: a function sending a witness {lit}`e` over {lit}`i'` and a term over {lit}`i`
whose index along {lit}`f` is the source of {lit}`e` to a term whose index along
{lit}`f` is the target of {lit}`e`, all of one root shape, makes the targets of all
such witnesses have one root shape. -/
theorem no_uniform_transport {i' i : I} (f : i' ⟶ i)
    (p₁ p₂ : {p : (F.carrier N).obj ⟨eqObj i'⟩ × (F.carrier N).obj ⟨termObj i⟩ //
      restr (F.carrier N) f p.2 = src (F.carrier N) i' p.1})
    (h : head N (tgt (F.carrier N) i' p₁.1.1) ≠ head N (tgt (F.carrier N) i' p₂.1.1)) :
    ¬ ∃ (ρ : F.Shape (termObj i))
      (transport : {p : (F.carrier N).obj ⟨eqObj i'⟩ × (F.carrier N).obj ⟨termObj i⟩ //
        restr (F.carrier N) f p.2 = src (F.carrier N) i' p.1} → (F.carrier N).obj ⟨termObj i⟩),
      (∀ p, head N (transport p) = ρ.1) ∧
        ∀ p, restr (F.carrier N) f (transport p) = tgt (F.carrier N) i' p.1.1 := by
  rintro ⟨ρ, transport, hρ, hidx⟩
  have key := head_map_of_head_eq N (termHom f) transport ρ hρ
  exact h (((congrArg (head N) (hidx p₁)).symm.trans (key p₁)).trans
    ((key p₂).symm.trans (congrArg (head N) (hidx p₂))))

end GebProto.QuotientPRA
