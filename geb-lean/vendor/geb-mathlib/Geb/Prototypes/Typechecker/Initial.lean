/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker

set_option doc.verso true in
/-!
# Initial decision problems

A decision checker accepting no inputs is initial. The identity endomorphism
represents a map to every target, since preservation is vacuous. All such maps
agree on the empty accepted fiber, so they define the same quotient morphism.

For distinct truth values, a checker has empty accepted fiber exactly when it
is constant false. Admissibility of constant false therefore suffices for an
initial object. Once that checker is available, every initial object has empty
accepted fiber, as its map to the rejecting checker shows.

## Main definitions

* {lit}`DecisionProblem.HasFalseChecker` requires distinct truth values and
  admissibility of constant false.
* {lit}`DecisionProblem.rejectAll` is the corresponding decision problem.
* {lit}`DecisionProblem.uniqueFromEmpty` supplies the initial universal property.
* {lit}`DecisionProblem.uniqueFromFalse` specializes to the constant-false checker.

## Main statements

* {lit}`DecisionProblem.exists_empty_iff_hasFalseChecker` characterizes existence
  of an empty accepted fiber by the condition on the admissible submonoid.
* {lit}`DecisionProblem.unique_from_iff_empty` characterizes initial objects
  when the constant-false checker is available.

## Tags

decision problem, typechecker, initial object, quotient, empty fiber
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- The truth values are distinct and constant false is an admissible endomorphism. -/
def HasFalseChecker (S : Submonoid (Function.End B)) (t f : B) : Prop :=
  t ≠ f ∧ (fun _ : B ↦ f) ∈ S

/-- The admissible decision problem rejecting every input. -/
def rejectAll (h : HasFalseChecker S t f) : DecisionProblem S t f :=
  ⟨⟨fun _ ↦ f, h.2⟩, h.1, fun _ ↦ Or.inr rfl⟩

/-- An empty accepted fiber supplies an initial object. -/
@[instance_reducible]
def uniqueFromEmpty (I : DecisionProblem S t f)
    (hI : ∀ x : B, I.checker.val x ≠ t) (X : DecisionProblem S t f) : Unique (I ⟶ X) where
  default := Representative.toHom ⟨1, fun x hx ↦ (hI x hx).elim⟩
  uniq r := Quotient.inductionOn r fun _ ↦
    (Representative.toHom_eq_iff _ _).mpr fun x hx ↦ (hI x hx).elim

/-- The constant-false checker is initial whenever it is admissible. -/
@[instance_reducible]
def uniqueFromFalse (h : HasFalseChecker S t f) (X : DecisionProblem S t f) :
    Unique (rejectAll h ⟶ X) :=
  uniqueFromEmpty (rejectAll h) (fun _ hx ↦ h.1 hx.symm) X

/-- An empty decision checker exists exactly when the distinct truth values admit constant
false in the submonoid. -/
theorem exists_empty_iff_hasFalseChecker :
    (∃ I : DecisionProblem S t f, ∀ x : B, I.checker.val x ≠ t) ↔
      HasFalseChecker S t f := by
  constructor
  · rintro ⟨I, hI⟩
    have hif : I.checker.val = fun _ ↦ f :=
      funext fun x ↦ (I.twoValued.2 x).resolve_left (hI x)
    exact ⟨I.twoValued.1, hif ▸ I.checker.property⟩
  · intro h
    exact ⟨rejectAll h, fun _ hx ↦ h.1 hx.symm⟩

/-- When constant false is available, a decision problem is initial exactly when it accepts
no inputs. Necessity follows by mapping to the rejecting checker. -/
theorem unique_from_iff_empty (h : HasFalseChecker S t f) (I : DecisionProblem S t f) :
    Nonempty (∀ X : DecisionProblem S t f, Unique (I ⟶ X)) ↔
      ∀ x : B, I.checker.val x ≠ t := by
  constructor
  · rintro ⟨hI⟩ x hx
    have hft : f = t := ((hI (rejectAll h)).default.restrict ⟨x, hx⟩).property
    exact h.1 hft.symm
  · intro hI
    exact ⟨uniqueFromEmpty I hI⟩

end GebProto.EndomorphismCategory.DecisionProblem
