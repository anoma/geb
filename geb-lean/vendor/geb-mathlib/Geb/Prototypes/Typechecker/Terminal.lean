/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker

set_option doc.verso true in
/-!
# Terminal decision problems

A decision checker accepting exactly the true value is terminal. Each source
checker sends its accepted inputs to that value, supplying an admissible map.
Every map into the singleton fiber has the same restriction, so the quotient
identifies all such maps.

More generally, a checker accepting exactly one element is terminal if an
admissible endomorphism sends the true value to that element. When the
constant-true function is admissible, a singleton checker is terminal exactly
when the constant function returning its accepted element is admissible.
Thus a singleton fiber alone need not supply the maps required for terminality.

A constant-true checker accepts the whole base, and cannot be terminal because
the truth values are distinct.

## Main definitions

* {lit}`DecisionProblem.HasTrueSingletonChecker` names the sufficient condition
  that a checker accepting exactly true is admissible.
* {lit}`DecisionProblem.uniqueToSingleton` constructs terminal data from a
  singleton accepted fiber and an admissible map to its element.
* {lit}`DecisionProblem.uniqueToTrueSingleton` specializes to the true value,
  requiring only that its singleton checker exists.

## Main statements

* {lit}`DecisionProblem.unique_to_singleton_iff_constant_mem` gives a necessary
  and sufficient condition when the constant-true function is admissible.
* {lit}`DecisionProblem.not_unique_to_constant` rules out a checker accepting
  every input as a terminal object.

## Implementation notes

The universal property is carried as {name}`Unique` on each incoming morphism
type, retaining both the chosen morphism and its uniqueness proof.

## Tags

decision problem, typechecker, terminal object, quotient, singleton
-/
set_option doc.verso true

@[expose] public section

universe u

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {B : Type u} {S : Submonoid (Function.End B)} {t f : B}

/-- The admissible decision checkers include one accepting exactly the true value. -/
def HasTrueSingletonChecker (S : Submonoid (Function.End B)) (t f : B) : Prop :=
  ∃ T : DecisionProblem S t f, ∀ x : B, T.checker.val x = t ↔ x = t

/-- A singleton accepted fiber is terminal if an admissible function sends true to its element.
The map from a source is its checker followed by that admissible function. -/
@[instance_reducible]
def uniqueToSingleton (T : DecisionProblem S t f) (a : B)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = a)
    (r : AdmissibleEndomorphism S) (hr : r.val t = a) (X : DecisionProblem S t f) :
    Unique (X ⟶ T) where
  default := Representative.toHom
    ⟨r * X.checker, fun _ hx ↦ (hT _).mpr ((congrArg r.val hx).trans hr)⟩
  uniq q := Quotient.inductionOn q fun q ↦
    (Representative.toHom_eq_iff _ _).mpr fun x hx ↦
      ((hT _).mp (q.property x hx)).trans ((congrArg r.val hx).trans hr).symm

/-- A decision checker accepting exactly the true value is terminal. -/
@[instance_reducible]
def uniqueToTrueSingleton (T : DecisionProblem S t f)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = t) (X : DecisionProblem S t f) :
    Unique (X ⟶ T) :=
  uniqueToSingleton T t hT 1 rfl X

/-- If constant true is admissible, a singleton checker is terminal exactly when the constant
function returning its accepted element is admissible. -/
theorem unique_to_singleton_iff_constant_mem (T : DecisionProblem S t f) (a : B)
    (hT : ∀ x : B, T.checker.val x = t ↔ x = a) (ht : (fun _ : B ↦ t) ∈ S) :
    Nonempty (∀ X : DecisionProblem S t f, Unique (X ⟶ T)) ↔ (fun _ : B ↦ a) ∈ S := by
  constructor
  · rintro ⟨h⟩
    let all : DecisionProblem S t f :=
      ⟨⟨fun _ ↦ t, ht⟩, T.twoValued.1, fun _ ↦ Or.inl rfl⟩
    exact Quotient.inductionOn (h all).default fun r ↦ by
      have hr : r.val.val = fun _ ↦ a :=
        funext fun x ↦ (hT _).mp (r.property x rfl)
      exact hr ▸ r.val.property
  · intro ha
    exact ⟨uniqueToSingleton T a hT ⟨fun _ ↦ a, ha⟩ rfl⟩

/-- A checker accepting every input cannot be terminal, since the truth values are distinct. -/
theorem not_unique_to_constant (T : DecisionProblem S t f)
    (hT : ∀ x : B, T.checker.val x = t) :
    ¬Nonempty (∀ X : DecisionProblem S t f, Unique (X ⟶ T)) := by
  rintro ⟨h⟩
  let r : Representative T T := ⟨T.checker, fun _ _ ↦ hT _⟩
  have heq := ((h T).uniq (Representative.id T).toHom).trans ((h T).uniq r.toHom).symm
  have hft : f = t := ((Representative.toHom_eq_iff _ _).mp heq f (hT f)).trans (hT f)
  exact T.twoValued.1 hft.symm

end GebProto.EndomorphismCategory.DecisionProblem
