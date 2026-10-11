/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeLCCC.Theory
public import Geb.Prototypes.PartialHorn.Initial

set_option doc.verso true in
/-!
# Terms modulo the categorical equations

The term model of {name}`Geb.FreeLCCC.theory` supplies mutually generated objects and arrows.
Both are quotients of the existing W-type syntax by derivable equality. Formation conditions
and equality premises are checked by {name}`Geb.PartialHorn.check`; no induction-induction
principle or equality decision procedure is assumed.

## Main definitions

* {lit}`model` — the closed term model.
* {lit}`Derives` — equality derivable from the categorical axioms in a context.

## Main statements

* {lit}`isModel` — the term model satisfies the categorical theory.
* {lit}`existsUnique_interpretation` — there is a unique homomorphism into any model.
* {lit}`derives_iff_valid` — its equational calculus is sound and complete for these models.

## Tags

syntactic category, partial Horn logic, term model, locally cartesian closed category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeLCCC

open PartialHorn

/-- A decidable check of scope and the common sort of a sequent's conclusion. -/
def wellFormed (a : Seq) : Bool :=
  a.Scoped && (sortOf sig a.ctx a.concl.lhs).isSome &&
    (sortOf sig a.ctx a.concl.lhs == sortOf sig a.ctx a.concl.rhs)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Reduction checks scope and sorts throughout the finite list of axioms.
/-- Every axiom is in scope and equates terms of the same sort. -/
theorem axioms_wellFormed : ∀ a ∈ theory.axioms, a.Scoped = true ∧ SidesSorted sig a := by
  have h : axioms.all wellFormed = true := by decide
  intro a ha
  have h' := List.all_eq_true.mp h a ha
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h'.1.2
  exact ⟨h'.1.1, s, hs, h'.2 ▸ hs⟩

/-- Derivable equality in the categorical theory, in a context under equations. -/
abbrev Derives (Γ : List ℕ) (H : List Eqn) (q : Eqn) : Prop :=
  Derivable theory #[] Γ H q

/-- The model of closed, defined terms modulo derivable equality. -/
def model : PartialHorn.Model.{0} sig := TermModel.termModel theory #[] [] []

/-- The class of a closed, defined term of a specified sort. -/
def ofTerm {s : ℕ} (t : Tree) (hs : sortOf sig [] t = some s)
    (hd : Derives [] [] (dfd t)) : model.Car s := ⟨⟦⟨(s, t), hs, hd⟩⟧, rfl⟩

/-- A closed term evaluates in the syntactic model to its class. -/
theorem eval_ofTerm {s : ℕ} (t : Tree) (hs : sortOf sig [] t = some s)
    (hd : Derives [] [] (dfd t)) :
    eval model [] t = Part.some ⟨s, ofTerm t hs hd⟩ := TermModel.eval_generic t hs hd

/-- Two closed terms of one sort have equal classes exactly when their equality is derivable. -/
theorem ofTerm_eq_iff {s : ℕ} {t u : Tree} (ht : sortOf sig [] t = some s)
    (hu : sortOf sig [] u = some s) (dt : Derives [] [] (dfd t))
    (du : Derives [] [] (dfd u)) :
    ofTerm t ht dt = ofTerm u hu du ↔ Derives [] [] ⟨t, u⟩ := by
  constructor
  · intro h
    exact (Quotient.exact (congrArg Subtype.val h)).2
  · intro h
    exact Subtype.ext (Quotient.sound ⟨rfl, h⟩)

/-- The quotient of syntax satisfies all the categorical axioms. -/
theorem isModel : IsModel theory model := TermModel.isModel _ _ _ _ axioms_wellFormed

/-- The free model has a unique interpretation in every model, in any universe. -/
theorem existsUnique_interpretation.{v} (M : PartialHorn.Model.{v} sig) (hM : IsModel theory M) :
    ∃! _f : ModelHom model M, True := TermModel.existsUnique_hom (T := theory) M hM

/-- Derivability is validity in every small model of the categorical theory. -/
theorem derives_iff_valid {Γ : List ℕ} {H : List Eqn} {q : Eqn}
    (hH : ∀ h ∈ H, SidesSorted sig ⟨Γ, [], h⟩) :
    Derives Γ H q ↔ ∀ M : PartialHorn.Model.{0} sig, IsModel theory M → Valid M Γ H q :=
  derivable_iff_valid (by simp) axioms_wellFormed hH

end Geb.FreeLCCC

end
