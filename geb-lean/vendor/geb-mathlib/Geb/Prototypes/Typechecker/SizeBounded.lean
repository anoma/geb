/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.RepresentationLowerBound
public import Geb.Prototypes.Computability.SizeBounded.Basic
public import Geb.Prototypes.Typechecker.Coproducts

set_option doc.verso true in
/-!
# The size bound obstructs products and coproducts

An injective word endomorphism whose output length is bounded by the maximum of
its input length and a fixed constant is surjective. On every sufficiently large
finite set of words of bounded length, it is an injective self-map, hence a
permutation.

But a product or coproduct of the everywhere-accepting decision problem with itself would
require an admissible injection that is not surjective. Consequently, a submonoid
consisting of unary functions represented by {name}`Geb.SizeBounded.SOf` cannot
provide either construction. This also applies to the successor-free and Kristiansen
subalgebras. The obstruction concerns output length, independently of their
completeness for decision problems.

## Main statements

* {lit}`Geb.SizeBounded.surjective_of_injective_of_length_le` proves the finite-set argument.
* {lit}`Geb.SizeBounded.sem_surjective_of_injective` applies the algebra's size bound.
* {lit}`DecisionProblem.not_pairing_of_sizeBounded` rules out even existence of pairing maps.
* {lit}`DecisionProblem.not_copairing_of_sizeBounded` gives the corresponding
  obstruction for copairing maps.

## Tags

decision problem, binary product, binary coproduct, non-size-increasing, logspace
-/
set_option doc.verso true

@[expose] public section

namespace Geb.SizeBounded

open Geb.BitTree.Elias

/-- An injective word function that eventually does not increase length is surjective. -/
theorem surjective_of_injective_of_length_le (r : List Bool → List Bool) (k : ℕ)
    (hbound : ∀ w, (r w).length ≤ max w.length k) (hinj : Function.Injective r) :
    Function.Surjective r := by
  intro w
  let n := max w.length k + 1
  let s := shortWords n
  -- Structural recursion avoids the choice dependency of `List.nodup_range`.
  have hrange : ∀ n, (List.range n).Nodup := by
    refine Nat.rec (by simp) (fun n ih ↦ ?_)
    rw [List.range_succ_eq_map, List.nodup_cons]
    exact ⟨by simp, ih.map Nat.succ_injective⟩
  have hnodup : s.Nodup := by
    change (shortWords n).Nodup
    rw [shortWords, List.nodup_flatMap]
    refine ⟨fun i _ ↦ nodup_words i, (hrange n).imp ?_⟩
    intro a b hab
    apply List.disjoint_left.mpr
    intro v ha hb
    exact hab (((mem_words a v).mp ha).symm.trans ((mem_words b v).mp hb))
  have hsub : s.map r ⊆ s := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    apply (mem_shortWords n _).mpr
    have hx := (mem_shortWords n x).mp hx
    have hb := hbound x
    omega
  have hperm : (s.map r).Perm s :=
    (List.subperm_of_subset (hnodup.map hinj) hsub).perm_of_length_le
      (by simp only [List.length_map, le_refl])
  have hw : w ∈ s.map r := hperm.mem_iff.mpr ((mem_shortWords n w).mpr (by omega))
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hw
  exact ⟨x, hx⟩

/-- Every injective unary function represented by the size-bounded algebra is surjective. -/
theorem sem_surjective_of_injective (e : SOf 1)
    (hinj : Function.Injective (fun w ↦ e.sem (fun _ ↦ w))) :
    Function.Surjective (fun w ↦ e.sem (fun _ ↦ w)) :=
  surjective_of_injective_of_length_le _ (nsiConst e.1.1)
    (fun w ↦ nsi_sem e (fun _ ↦ w) w.length (fun _ ↦ le_rfl)) hinj

end Geb.SizeBounded

namespace GebProto.EndomorphismCategory.DecisionProblem

open CategoryTheory

variable {S : Submonoid (Function.End (List Bool))} {t f : List Bool}

/-- An admissible injection is surjective if every admissible function has a unary
size-bounded representation. -/
theorem surjective_of_injective_of_sizeBounded
    (hS : ∀ r : S, ∃ e : Geb.SizeBounded.SOf 1, ∀ w, e.sem (fun _ ↦ w) = r.val w)
    (r : S) (hinj : Function.Injective r.val) : Function.Surjective r.val := by
  obtain ⟨e, he⟩ := hS r
  have heq : (fun w ↦ e.sem (fun _ ↦ w)) = r.val := funext he
  exact heq ▸ Geb.SizeBounded.sem_surjective_of_injective e (heq ▸ hinj)

/-- If every admissible unary function is represented by the size-bounded algebra, an
everywhere-accepting object cannot have pairing maps for all pairs of endomorphisms. -/
theorem not_pairing_of_sizeBounded
    (hS : ∀ r : S, ∃ e : Geb.SizeBounded.SOf 1, ∀ w, e.sem (fun _ ↦ w) = r.val w)
    (U P : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) (p q : P ⟶ U) :
    ¬(∀ r s : U ⟶ U, ∃ m : U ⟶ P, m ≫ p = r ∧ m ≫ q = s) := by
  intro hlift
  obtain ⟨r, hinj, hsurj⟩ := exists_injective_not_surjective U P hU p q hlift
  exact hsurj (surjective_of_injective_of_sizeBounded hS r hinj)

/-- Unary size-bounded functions cannot supply all copairing maps for an
everywhere-accepting object, regardless of the choice of injections. -/
theorem not_copairing_of_sizeBounded
    (hS : ∀ r : S, ∃ e : Geb.SizeBounded.SOf 1, ∀ w, e.sem (fun _ ↦ w) = r.val w)
    (U P : DecisionProblem S t f) (hU : ∀ x, U.checker.val x = t) (i j : U ⟶ P) :
    ¬(∀ r s : U ⟶ U, ∃ m : P ⟶ U, i ≫ m = r ∧ j ≫ m = s) := by
  intro hdesc
  obtain ⟨r, hinj, hsurj⟩ := exists_injective_not_surjective_of_copairing U P hU i j hdesc
  exact hsurj (surjective_of_injective_of_sizeBounded hS r hinj)

end GebProto.EndomorphismCategory.DecisionProblem
