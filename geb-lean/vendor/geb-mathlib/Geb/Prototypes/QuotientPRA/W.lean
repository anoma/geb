/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Geb.Prototypes.QuotientPRA.Basic


set_option doc.verso true in
/-!
# Quotient presheaf polynomial functors and their quotient W-types

A quotient presheaf polynomial functor over a category {lit}`I` is a presheaf
polynomial endofunctor over {lit}`I × WalkingParallelPair`. Its shapes over
{lit}`(i, zero)` are the constructors of terms of sort {lit}`i`; its shapes over
{lit}`(i, one)` are the constructors of witnesses of equality between terms of sort
{lit}`i`. Restriction along the two parallel morphisms gives each witness constructor
two endpoints, each a term constructor applied to the witness constructor's
arguments; restriction along a morphism of {lit}`I` sends a witness between terms to a
witness between their restrictions. Arguments of a constructor may lie over witness
objects, so a constructor may take equalities as premises.

The W-type {name}`PresheafPFunctor.W` of such a functor is a graph in the presheaves on
{lit}`I` ({lit}`GebProto.QuotientPRA.Basic`): terms and witnesses, built together.
Its quotient, {lit}`quotient`, is the coequalizer of the two endpoint maps, whose
value at {lit}`i` is a {name}`Quot` of the terms of sort {lit}`i` by the existence of a
witness. Two terms have the same class exactly when they are related by the
equivalence relation the witnesses generate, so the equivalence closure is taken by
{name}`Quot` itself rather than by constructors of witnesses.

A model is a presheaf {lit}`P` on {lit}`I` with an algebra structure on the discrete
graph on {lit}`P`: an interpretation of every term constructor in {lit}`P` such that
the two endpoints of every witness constructor receive equal interpretations
({lit}`model_sound`). The eliminator {lit}`elim` into a model is the transpose, across
the adjunction {lit}`coeqHomEquiv`, of the W-type's eliminator into the discrete graph,
and {lit}`elim_intro` is its computation rule on the constructors {lit}`intro` of the
quotient.

## Main definitions

* {lit}`quotient` — the quotient W-type, a presheaf on {lit}`I`.
* {lit}`quotientMk` — the class of a term.
* {lit}`intro` — the term constructors, landing in the quotient.
* {lit}`elim` — the eliminator into a model.
* {lit}`IsModelHom` — a morphism of models.

## Main statements

* {lit}`quotientMk_src` — the endpoints of every witness have the same class.
* {lit}`quotientMk_eq_iff` — two terms have the same class exactly when the
  witnesses relate them by a finite zig-zag.
* {lit}`intro_surjective` — every class is a constructor applied to terms.
* {lit}`model_sound` — a model interprets the endpoints of every witness constructor
  equally.
* {lit}`elim_quotientMk`, {lit}`elim_intro` — the eliminator on classes and its
  computation rule.

## Implementation notes

The quotient is taken of the W-type as a whole, so the eliminator exists for every
functor, and its computation rule holds. That the quotient is itself a model, that
the term constructors descend to classes of arguments, is a separate property. It
requires every witness between arguments to lift to a witness between the
constructed terms, and a choice of representatives for the arguments: finitely many
choices are constructive, while infinitary arities need a choice principle, as
\[FiorePittsSteenkamp2020\] records for W-types with equations and
\[Dijkstra2017\] records for quotient inductive-inductive definitions. For a
finitary functor with free arities and congruences the quotient is a model, the
initial one ({lit}`GebProto.QuotientPRA.InitialModel`), and in particular for a
finitary signature with one-step equations ({lit}`GebProto.QuotientPRA.Initial`).

The endpoints of a witness constructor are single term constructors applied to the
witness constructor's arguments, since restriction in a presheaf W-type rebuilds the
root of a tree with the shape {lit}`shapeRestr` assigns to the root's shape. An
equation whose side is an argument, as a unit law, or a nested term, as an
associativity law, is therefore not a witness constructor; neither are reflexivity,
symmetry and transitivity, whose endpoints are arguments
({lit}`GebProto.QuotientPRA.Obstruction`). The generated equivalence relation is
taken by the quotient instead.

## References

* \[AltenkirchCapriottiDijkstraKrausNordvallForsberg2018\]
* \[Dijkstra2017\]
* \[FiorePittsSteenkamp2020\]
* \[Weber2007\]

## Tags

quotient inductive-inductive type, quotient, W-type, polynomial functor, presheaf,
parametric right adjoint, coequalizer
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

universe uI uA uB vI

variable {I : Type uI} [Category.{vI} I]
  (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} (I × WalkingParallelPair)
    (I × WalkingParallelPair))

/-- The quotient W-type: the quotient of the W-type's terms by its witnesses. -/
abbrev quotient : Iᵒᵖ ⥤ Type (max uI uA uB) := coeq F.W

/-- The class of a term of the W-type. -/
abbrev quotientMk {i : I} (t : F.W.obj ⟨termObj i⟩) : (quotient F).obj ⟨i⟩ := coeqMk F.W t

/-- The term constructors, landing in the quotient: a node of the functor over the
W-type, sent to the class of the tree it builds. -/
def intro {i : I} (x : (F.objPresheaf F.W).obj ⟨termObj i⟩) : (quotient F).obj ⟨i⟩ :=
  quotientMk F (PresheafPFunctor.W.mk x)

/-- The endpoints of every witness have the same class. -/
theorem quotientMk_src {i : I} (e : F.W.obj ⟨eqObj i⟩) :
    quotientMk F (src F.W i e) = quotientMk F (tgt F.W i e) :=
  coeqMk_src F.W e

/-- Two terms have the same class exactly when the witnesses relate them by the
equivalence relation they generate. -/
theorem quotientMk_eq_iff {i : I} (t t' : F.W.obj ⟨termObj i⟩) :
    quotientMk F t = quotientMk F t' ↔
      Relation.EqvGen (Function.Coequalizer.Rel (src F.W i) (tgt F.W i)) t t' :=
  coeqMk_eq_iff F.W t t'

/-- Every class is a term constructor applied to terms. -/
theorem intro_surjective {i : I} (q : (quotient F).obj ⟨i⟩) :
    ∃ x : (F.objPresheaf F.W).obj ⟨termObj i⟩, intro F x = q :=
  Quot.ind (β := fun q ↦ ∃ x, intro F x = q)
    (fun t ↦ ⟨PresheafPFunctor.W.dest t,
      congrArg (quotientMk F) (PresheafPFunctor.W.mk_dest t)⟩) q

variable {F}

/-- A model interprets the two endpoints of every witness constructor equally: the
algebra's value on a witness node lies in the discrete graph, whose endpoint maps
are identities. -/
theorem model_sound {P : Iᵒᵖ ⥤ Type (max uI uA uB)}
    (α : NatTrans (F.objPresheaf (discrete P)) (discrete P)) {i : I}
    (x : (F.objPresheaf (discrete P)).obj ⟨eqObj i⟩) :
    α.app ⟨termObj i⟩ (src (F.objPresheaf (discrete P)) i x) =
      α.app ⟨termObj i⟩ (tgt (F.objPresheaf (discrete P)) i x) :=
  app_src_eq_app_tgt α x

/-- A morphism of models {lit}`(P, α) → (P', α')`: a morphism of presheaves on {lit}`I`
whose discrete graph commutes with the algebras. -/
def IsModelHom {P P' : Iᵒᵖ ⥤ Type (max uI uA uB)}
    (α : NatTrans (F.objPresheaf (discrete P)) (discrete P))
    (α' : NatTrans (F.objPresheaf (discrete P')) (discrete P')) (h : NatTrans P P') : Prop :=
  ∀ c x, (discreteMap h).app c (α.app c x) = α'.app c ((F.mapPresheaf (discreteMap h)).app c x)

variable (F)

/-- The eliminator of the quotient W-type into a model {lit}`(P, α)`: the transpose,
across {lit}`coeqHomEquiv`, of the W-type's eliminator into the discrete graph on
{lit}`P`. -/
def elim (P : Iᵒᵖ ⥤ Type (max uI uA uB))
    (α : NatTrans (F.objPresheaf (discrete P)) (discrete P)) : NatTrans (quotient F) P :=
  coeqDesc (PresheafPFunctor.W.elim F (discrete P) α)

/-- The eliminator sends the class of a term to the W-type eliminator's value on it. -/
theorem elim_quotientMk (P : Iᵒᵖ ⥤ Type (max uI uA uB))
    (α : NatTrans (F.objPresheaf (discrete P)) (discrete P)) {i : I} (t : F.W.obj ⟨termObj i⟩) :
    (elim F P α).app ⟨i⟩ (quotientMk F t) =
      (PresheafPFunctor.W.elim F (discrete P) α).app ⟨termObj i⟩ t :=
  rfl

/-- The computation rule: the eliminator applied to a constructed class is the model's
algebra applied to the node whose arguments are the eliminator's values. -/
theorem elim_intro (P : Iᵒᵖ ⥤ Type (max uI uA uB))
    (α : NatTrans (F.objPresheaf (discrete P)) (discrete P)) {i : I}
    (x : (F.objPresheaf F.W).obj ⟨termObj i⟩) :
    (elim F P α).app ⟨i⟩ (intro F x) =
      α.app ⟨termObj i⟩
        ((F.mapPresheaf (PresheafPFunctor.W.elim F (discrete P) α)).app ⟨termObj i⟩ x) :=
  PresheafPFunctor.W.elim_mk F (discrete P) α x

end GebProto.QuotientPRA
