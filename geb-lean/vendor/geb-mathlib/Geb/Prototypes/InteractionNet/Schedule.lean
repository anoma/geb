/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Relation

set_option doc.verso true in
/-!
# Consequences of the interaction-net diamond

Two distinct one-step results of an interaction net can each take one further step to
the same net, up to the chosen equality of nets. This strict diamond is stronger than
joinability by arbitrarily many steps. Besides confluence, it transports accessibility
backwards along a reduction. Consequently, the existence of a normalizing schedule implies
termination of every schedule. Normal-form agreement and termination are separate results.

This module proves the relation-theoretic consequences. A net reduction must establish
the strict diamond before these theorems apply to it.

## Main definitions

* {lit}`Schedule.StrongDiamond` — coincident results or a strict one-step join.
* {lit}`Schedule.Normal` — no reduction leaves the state.

## Main statements

* {lit}`Schedule.confluent` — finite schedules from the same state can be joined.
* {lit}`Schedule.normal_unique` — normal results of two schedules coincide.
* {lit}`Schedule.acc_of_reaches_normal` — one normalizing schedule makes all reductions accessible.

## References

* \[DeFalco2010\], Definition 5.2, Proposition 5.3 and Corollary 5.4, give the strict
  diamond used for interaction nets, modulo renaming of fresh ports.

## Tags

interaction net, confluence, schedule, diamond, termination, accessibility
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Schedule

open Relation

universe u

variable {A : Type u} {r : A → A → Prop}

/-- Distinct one-step results admit a join by one step from each result. -/
def StrongDiamond (r : A → A → Prop) : Prop :=
  ∀ ⦃a b c⦄, r a b → r a c → b = c ∨ Join r b c

/-- A normal state has no outgoing proper reduction. -/
def Normal (r : A → A → Prop) (a : A) : Prop := ∀ b, ¬r a b

/-- A finite schedule and one competing step admit a join with at most one residual step. -/
theorem strip (hd : StrongDiamond r) {a b : A} (hab : ReflTransGen r a b) :
    ∀ c, r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d := by
  refine hab.head_induction_on ?_ ?_
  · intro c hbc
    exact ⟨c, .single hbc, .refl⟩
  · intro a m ham hmb ih c hac
    rcases hd ham hac with h | ⟨v, hmv, hcv⟩
    · subst c
      exact ⟨b, .refl, hmb⟩
    · obtain ⟨d, hbd, hvd⟩ := ih v hmv
      exact ⟨d, hbd, hvd.head hcv⟩

/-- The strict diamond gives confluence of finite schedules. -/
theorem confluent (hd : StrongDiamond r) {a c : A} (hac : ReflTransGen r a c) :
    ∀ b, ReflTransGen r a b → Join (ReflTransGen r) b c := by
  refine hac.head_induction_on ?_ ?_
  · intro b hcb
    exact ⟨b, .refl, hcb⟩
  · intro a m ham _ ih b hab
    obtain ⟨d, hbd, hmd⟩ := strip hd hab m ham
    obtain ⟨e, hde, hce⟩ := ih d hmd
    cases hbd with
    | refl => exact ⟨e, hde, hce⟩
    | single hbd => exact ⟨e, hde.head hbd, hce⟩

/-- A finite schedule from a normal state cannot leave that state. -/
theorem eq_of_normal_reaches {a b : A} (hab : ReflTransGen r a b) :
    Normal r a → a = b := by
  refine hab.head_induction_on (fun _ ↦ rfl) ?_
  intro a c hac _ _ ha
  exact (ha c hac).elim

/-- Two normal results of schedules from the same source coincide. -/
theorem normal_unique (hd : StrongDiamond r) {a b c : A}
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c)
    (hb : Normal r b) (hc : Normal r c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := confluent hd hac b hab
  exact (eq_of_normal_reaches hbd hb).trans (eq_of_normal_reaches hcd hc).symm

/-- A normal state is accessible for the converse reduction relation. -/
theorem acc_of_normal {a : A} (ha : Normal r a) : Acc (fun b a ↦ r a b) a :=
  .intro a (fun b h ↦ (ha b h).elim)

/-- Under the strict diamond, accessibility propagates backwards through one reduction. -/
theorem acc_of_step (hd : StrongDiamond r) {a b : A}
    (hb : Acc (fun y x ↦ r x y) b) (hab : r a b) : Acc (fun y x ↦ r x y) a := by
  refine Acc.rec (motive := fun b _ ↦ ∀ a, r a b → Acc (fun y x ↦ r x y) a) ?_ hb a hab
  intro b hb ih a hab
  refine Acc.intro a ?_
  intro c hac
  rcases hd hab hac with h | ⟨d, hbd, hcd⟩
  · subst c
    exact Acc.intro b hb
  · exact ih d hbd c hcd

/-- A normalizing schedule makes every reduction from its source accessible. -/
theorem acc_of_reaches_normal (hd : StrongDiamond r) {a b : A}
    (hab : ReflTransGen r a b) (hb : Normal r b) : Acc (fun y x ↦ r x y) a := by
  exact hab.head_induction_on (acc_of_normal hb) (fun h _ ih ↦ acc_of_step hd ih h)

/-- Every state reached by a competing finite schedule still reaches the same normal result. -/
theorem reaches_normal (hd : StrongDiamond r) {a b c : A}
    (hab : ReflTransGen r a b) (hb : Normal r b) (hac : ReflTransGen r a c) :
    ReflTransGen r c b := by
  obtain ⟨d, hcd, hbd⟩ := confluent hd hab c hac
  have h := eq_of_normal_reaches hbd hb
  subst d
  exact hcd

end Geb.InteractionNet.Schedule

end
