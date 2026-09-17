/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Basic
public import Geb.Mathlib.Data.Vector.OfFn
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Bound.Init

set_option doc.verso true in
/-!
# Iterative simultaneous recursion on words

Simultaneous recursion can retain a vector of the current results instead of a history of
results. Reading the recursion word in reverse order reconstructs its successive suffixes;
each step evaluates all components against the same previous vector.

## Main definitions

* {lit}`srnStep` updates the suffix and the vector of simultaneous results.
* {lit}`runSRN` folds these updates over the reversed recursion word.

## Main statements

* {lit}`runSRN_eq` identifies the iterative result with {name}`Geb.SizeBounded.evalSRN`.
* {lit}`runSRN_lengths_le` bounds each word in an iterative state.
* {lit}`runSRN_storage_le` bounds the sum of the retained word lengths.

## Implementation notes

The vector materializes the results of a stage. This is an implementation of the recursion
operator on word values, not a compilation of its base and step functions to a Turing machine.

## References

* \[Mazzanti2016\], Section 2 and Theorem 5.3, retaining simultaneous results together.

## Tags

simultaneous recursion, bitstring, iteration, vector
-/

set_option doc.verso true

@[expose] public section

namespace Geb.SizeBounded

open Cobham (Sem)

/-- Extend the reconstructed suffix and evaluate each component against the previous vector. -/
def srnStep {a b : ℕ} (h : Bool → Fin b → Sem (b + a + 1)) (y : Fin a → List Bool)
    (s : List Bool × Vector (List Bool) b) (i : Bool) : List Bool × Vector (List Bool) b :=
  (i :: s.1, Vector.ofFnC fun j ↦ h i j (stepEnv s.1 (fun l ↦ s.2.get l) y))

/-- Evaluate simultaneous recursion by folding over the word from right to left. -/
def runSRN {a b : ℕ} (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (w : List Bool) (y : Fin a → List Bool) : List Bool × Vector (List Bool) b :=
  w.reverse.foldl (srnStep h y) ([], Vector.ofFnC fun j ↦ g j y)

/-- The empty word initializes the vector with all base values. -/
@[simp] theorem runSRN_nil {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (b + a + 1)) (y : Fin a → List Bool) :
    runSRN g h [] y = ([], Vector.ofFnC fun j ↦ g j y) := rfl

/-- Extending a word performs one vector update after evaluating its tail. -/
theorem runSRN_cons {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (b + a + 1)) (i : Bool) (w : List Bool)
    (y : Fin a → List Bool) :
    runSRN g h (i :: w) y = srnStep h y (runSRN g h w y) i := by
  simp only [runSRN, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The iterative state is the original word together with all its recursive values. -/
theorem runSRN_eq {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (b + a + 1)) (w : List Bool) (y : Fin a → List Bool) :
    runSRN g h w y = (w, Vector.ofFnC fun j ↦ evalSRN g h w j y) := by
  refine List.rec rfl (fun i v ih ↦ ?_) w
  rw [runSRN_cons, ih]
  simp only [srnStep, Vector.get_ofFnC, evalSRN, stepEnv]

/-- Every word retained at a stage satisfies the same non-size-increase bound. -/
theorem runSRN_lengths_le {a b kg kh : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (b + a + 1)} (hg : ∀ j, NSI kg (g j))
    (hh : ∀ i j, NSI kh (h i j)) (w : List Bool) (y : Fin a → List Bool) (m : ℕ)
    (hw : w.length ≤ m) (hy : ∀ i, (y i).length ≤ m) :
    (runSRN g h w y).1.length ≤ m ∧
      ∀ j, ((runSRN g h w y).2.get j).length ≤ max m (max kg kh) := by
  rw [runSRN_eq]
  refine ⟨hw, fun j ↦ ?_⟩
  simp only [Vector.get_ofFnC]
  exact nsi_srn hg hh j (Fin.cons w y) m (Fin.cases hw hy)

/-- The number of bits in a reconstructed suffix and its vector of results. -/
def srnStorage {b : ℕ} (s : List Bool × Vector (List Bool) b) : ℕ :=
  s.1.length + (List.ofFn fun j ↦ (s.2.get j).length).sum

/-- Bounding each retained word bounds their total size by the fixed number of words. -/
theorem srnStorage_le {b : ℕ} (s : List Bool × Vector (List Bool) b) (L : ℕ)
    (hw : s.1.length ≤ L) (hv : ∀ j, (s.2.get j).length ≤ L) :
    srnStorage s ≤ (b + 1) * L := by
  have hs := List.sum_le_card_nsmul (List.ofFn fun j ↦ (s.2.get j).length) L
    (fun x hx ↦ by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact hv j)
  simp only [List.length_ofFn, Nat.nsmul_eq_mul] at hs
  exact (Nat.add_le_add hw hs).trans_eq (by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm])

/-- The total retained state has linear size when the base and step functions are NSI.
This counts word bits, not the work cells visited by a Turing machine. -/
theorem runSRN_storage_le {a b kg kh : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (b + a + 1)} (hg : ∀ j, NSI kg (g j))
    (hh : ∀ i j, NSI kh (h i j)) (w : List Bool) (y : Fin a → List Bool) (m : ℕ)
    (hw : w.length ≤ m) (hy : ∀ i, (y i).length ≤ m) :
    srnStorage (runSRN g h w y) ≤ (b + 1) * max m (max kg kh) := by
  obtain ⟨hs, hv⟩ := runSRN_lengths_le hg hh w y m hw hy
  exact srnStorage_le _ _ (hs.trans (Nat.le_max_left _ _)) hv

end Geb.SizeBounded
