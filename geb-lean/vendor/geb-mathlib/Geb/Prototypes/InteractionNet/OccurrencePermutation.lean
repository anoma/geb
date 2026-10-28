/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Aesop
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

set_option doc.verso true in
/-!
# Occurrence bijections for permuted lists

A list permutation preserves occurrences, including separate occurrences with equal values.
Its constructors provide an explicit position bijection: preserve a new head, exchange two
heads, or compose earlier bijections. The existence proof uses no choice principle.

## Main statements

* {lit}`OccurrencePermutation.exists_get_equiv` — a permutation has a value-preserving
  bijection of its occurrence positions.

## Tags

interaction net, syntax, permutation, occurrence, constructive
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.OccurrencePermutation

private def consEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (.inl ()) Sum.inr
  invFun := Sum.elim (fun _ ↦ 0) Fin.succ
  left_inv i := Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := by rcases p with u | i <;> rfl

private def consMap {n m : ℕ} (e : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) :=
  (consEquiv n).trans ((Equiv.sumCongr (Equiv.refl Unit) e).trans (consEquiv m).symm)

private def swapBranches (n : ℕ) : Unit ⊕ (Unit ⊕ Fin n) ≃ Unit ⊕ (Unit ⊕ Fin n) where
  toFun p := match p with
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  invFun p := match p with
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  left_inv p := by rcases p with u | (u | i) <;> rfl
  right_inv p := by rcases p with u | (u | i) <;> rfl

private def twoConsEquiv (n : ℕ) : Fin (n + 1 + 1) ≃ Unit ⊕ (Unit ⊕ Fin n) :=
  (consEquiv (n + 1)).trans (Equiv.sumCongr (Equiv.refl Unit) (consEquiv n))

private def swapTwo (n : ℕ) : Fin (n + 1 + 1) ≃ Fin (n + 1 + 1) :=
  (twoConsEquiv n).trans ((swapBranches n).trans (twoConsEquiv n).symm)

/-- Every list permutation supplies a bijection matching each individual occurrence's value. -/
theorem exists_get_equiv {X : Type} {xs ys : List X} (h : xs.Perm ys) :
    ∃ e : Fin xs.length ≃ Fin ys.length, ∀ i, ys.get (e i) = xs.get i := by
  refine List.Perm.rec (motive := fun xs ys _ ↦
    ∃ e : Fin xs.length ≃ Fin ys.length, ∀ i, ys.get (e i) = xs.get i)
      ?_ (fun a {xs ys} _ ih ↦ ?_) (fun a b xs ↦ ?_)
      (fun {_ _ _} _ _ ih ih' ↦ ?_) h
  · exact ⟨Equiv.refl _, fun i ↦ Fin.elim0 i⟩
  · obtain ⟨e, he⟩ := ih
    refine ⟨consMap e, fun i ↦ ?_⟩
    exact Fin.cases rfl (fun i ↦ he i) i
  · refine ⟨swapTwo xs.length, fun i ↦ ?_⟩
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i) i
  · obtain ⟨e, he⟩ := ih
    obtain ⟨f, hf⟩ := ih'
    exact ⟨e.trans f, fun i ↦ (hf (e i)).trans (he i)⟩

end Geb.InteractionNet.OccurrencePermutation

end
