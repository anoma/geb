/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Notation

set_option doc.verso true in
/-!
# Finite sums for wire counting

Wire multiplicities are sums over finite port indices. The sums here are list folds, with
their splitting and selection laws proved directly by the natural-number and finite-index
recursors. The proofs therefore do not need an arbitrary choice of an enumeration.

## Main definitions

* {lit}`finSum` — sum a natural-number-valued function over its finite domain.

## Main statements

* {lit}`finSum_succ`, {lit}`finSum_append` — split a sum into its first entry or two blocks.
* {lit}`finSum_add` — sum a pointwise addition.
* {lit}`finSum_ite_eq` — select one port's contribution.

## Tags

finite sum, port, wire, counting, constructive
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

/-- Sum the entries in finite-index order. -/
def finSum {n : ℕ} (f : Fin n → ℕ) : ℕ := (List.ofFn f).sum

/-- A list sum over the finite enumeration is a finite-index sum. -/
theorem finSum_ofFn {n : ℕ} (f : Fin n → ℕ) : (List.ofFn f).sum = finSum f := rfl

/-- The sum over no ports is zero. -/
@[simp] theorem finSum_zero (f : Fin 0 → ℕ) : finSum f = 0 := rfl

/-- Split off the first port. -/
theorem finSum_succ {n : ℕ} (f : Fin (n + 1) → ℕ) :
    finSum f = f 0 + finSum (fun i ↦ f i.succ) := by
  simp only [finSum, List.ofFn_succ, List.sum_cons]

/-- The sum over one port is its contribution. -/
@[simp] theorem finSum_one (f : Fin 1 → ℕ) : finSum f = f 0 := by
  rw [finSum_succ, finSum_zero, Nat.add_zero]

/-- A zero contribution at every port sums to zero. -/
@[simp] theorem finSum_const_zero (n : ℕ) : finSum (fun _ : Fin n ↦ 0) = 0 := by
  exact Nat.rec rfl (fun n ih ↦ by rw [finSum_succ, ih, Nat.zero_add]) n

/-- A pointwise sum splits into the sums of its two contributions. -/
@[simp] theorem finSum_add {n : ℕ} (f g : Fin n → ℕ) :
    finSum (fun i ↦ f i + g i) = finSum f + finSum g := by
  apply Nat.rec (motive := fun n ↦ ∀ f g : Fin n → ℕ,
    finSum (fun i ↦ f i + g i) = finSum f + finSum g)
    (fun _ _ ↦ rfl) (fun n ih f g ↦ ?_) n f g
  rw [finSum_succ, finSum_succ f, finSum_succ g, ih]
  omega

/-- A conditional independent of the port can be taken outside the sum. -/
@[simp] theorem finSum_ite {n : ℕ} (p : Prop) [Decidable p] (f g : Fin n → ℕ) :
    finSum (fun i ↦ if p then f i else g i) = if p then finSum f else finSum g := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

/-- A condition selecting one port returns that port's contribution. -/
@[simp] theorem finSum_ite_eq {n : ℕ} (j : Fin n) (f : Fin n → ℕ) :
    finSum (fun i ↦ if i = j then f i else 0) = f j := by
  apply Nat.rec (motive := fun n ↦ ∀ (j : Fin n) (f : Fin n → ℕ),
    finSum (fun i ↦ if i = j then f i else 0) = f j)
    (fun j ↦ j.elim0) (fun n ih j f ↦ ?_) n j f
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · rw [finSum_succ]
    simp
  · rw [finSum_succ]
    simp [Ne.symm (Fin.succ_ne_zero j), ih]

/-- The same selection with the equality written in the opposite direction. -/
@[simp] theorem finSum_ite_eq' {n : ℕ} (j : Fin n) (f : Fin n → ℕ) :
    finSum (fun i ↦ if j = i then f i else 0) = f j := by
  simpa only [eq_comm] using finSum_ite_eq j f

/-- Split a port array at a specified boundary. -/
theorem finSum_append {m n : ℕ} (f : Fin (m + n) → ℕ) :
    finSum f = finSum (fun i : Fin m ↦ f (Fin.castAdd n i)) +
      finSum (fun i : Fin n ↦ f (Fin.natAdd m i)) := by
  simp only [finSum, List.ofFn_add, List.sum_append]
  rfl

/-- Count occurrences in a finite array by summing the contributions of its ports. -/
theorem count_ofFn_eq_finSum {ν : Type} [DecidableEq ν] [BEq ν] [LawfulBEq ν]
    {n : ℕ} (f : Fin n → ν) (x : ν) :
    (List.ofFn f).count x = finSum (fun i ↦ if f i = x then 1 else 0) := by
  rw [← List.flatMap_singleton' (List.ofFn f), List.count_flatMap, List.map_ofFn]
  simp only [Function.comp_def, List.count_singleton, beq_iff_eq, finSum_ofFn]

/-- An entry of an injectively indexed rectangle occurs exactly once in its enumeration. -/
theorem count_matrix {m k : ℕ} (w : Fin m → Fin k → ℕ)
    (hw : ∀ i i' j j', w i j = w i' j' ↔ i = i' ∧ j = j') (i : Fin m) (j : Fin k) :
    (List.ofFn fun a ↦ List.ofFn (w a)).flatten.count (w i j) = 1 := by
  simp only [List.count_flatten, List.map_ofFn, Function.comp_def,
    count_ofFn_eq_finSum, finSum_ofFn, hw]
  have hi : ∀ a, (finSum fun b ↦ if a = i ∧ b = j then 1 else 0) =
      if a = i then 1 else 0 := by
    intro a
    by_cases h : a = i <;> simp [h]
  simp only [hi, finSum_ite_eq]

/-- An injectively indexed rectangle has no repeated entries. -/
theorem nodup_matrix {m k : ℕ} (w : Fin m → Fin k → ℕ)
    (hw : ∀ i i' j j', w i j = w i' j' ↔ i = i' ∧ j = j') :
    (List.ofFn fun i ↦ List.ofFn (w i)).flatten.Nodup := by
  apply List.nodup_iff_count_eq_one.mpr
  intro x hx
  obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact count_matrix w hw i j

end Geb.InteractionNet

end
