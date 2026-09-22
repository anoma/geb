/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.List.Infix
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Finiteness.Attr

set_option doc.verso true in
/-!
# Composable summaries for packed tree topology

An opening parenthesis contributes one and a closing parenthesis minus one.
The total excess and minimum prefix excess, including the empty prefix, suffice
to recognize a balanced forest. Combining summaries permits independent block
scans followed by a balanced reduction, or cached summaries in a persistent tree.
The range min-max construction of \[NavarroSadakane2014\] supplies the context;
only its total and minimum components are needed for this recognition experiment.

## Main definitions

* {lit}`Summary` stores an excess and a minimum.
* {lit}`Summary.append` combines adjacent blocks, in order.
* {lit}`summarize` specifies the summary of signed steps.
* {lit}`scan` computes that summary with a left fold and a two-integer accumulator.
* {lit}`wordSummary` interprets a word at an explicit width.

## Main statements

* {lit}`Summary.append_assoc` permits reassociation without changing the result.
* {lit}`summarize_flatten` proves that block grouping preserves the result.
* {lit}`scan_eq_summarize` proves the accumulator implementation correct.
* {lit}`balanced_eq_true_iff` proves the exact prefix-sum acceptance condition.

## References

* \[NavarroSadakane2014\]

## Tags

balanced parentheses, succinct tree, persistent sequence, parallel reduction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.SuccinctTree

/-- Total excess and minimum prefix excess of a parenthesis block. -/
@[ext] structure Summary where
  /-- Number of openings minus number of closings. -/
  total : ℤ
  /-- Minimum excess over prefixes, including the empty prefix. -/
  minimum : ℤ
  deriving DecidableEq, Repr, Inhabited

attribute [nolint unusedArguments] instReprSummary.repr

/-- Combine adjacent blocks; the second block's prefixes start at the first block's total. -/
def Summary.append (a b : Summary) : Summary :=
  ⟨a.total + b.total, min a.minimum (a.total + b.minimum)⟩

/-- The block reduction may be reassociated, while preserving block order. -/
theorem Summary.append_assoc (a b c : Summary) :
    (a.append b).append c = a.append (b.append c) := by
  apply Summary.ext
  · simp only [Summary.append]
    omega
  · simp only [Summary.append]
    omega

/-- Reference summary of signed steps, including the empty prefix. -/
def summarize (steps : List ℤ) : Summary :=
  steps.foldr (fun d s ↦ ⟨d + s.total, min 0 (d + s.minimum)⟩) ⟨0, 0⟩

/-- The empty prefix ensures that the minimum is nonpositive. -/
theorem summarize_minimum_nonpos (steps : List ℤ) : (summarize steps).minimum ≤ 0 := by
  cases steps <;> simp only [summarize, List.foldr] <;> omega

/-- Scanning adjacent blocks separately preserves their complete summary. -/
theorem summarize_append (xs ys : List ℤ) :
    summarize (xs ++ ys) = (summarize xs).append (summarize ys) := by
  refine List.rec ?_ ?_ xs
  · have hy := summarize_minimum_nonpos ys
    apply Summary.ext <;> simp only [List.nil_append, summarize, List.foldr, Summary.append]
    · omega
    · change (summarize ys).minimum = min 0 (0 + (summarize ys).minimum)
      omega
  · intro d xs ih
    change Summary.mk (d + (summarize (xs ++ ys)).total)
      (min 0 (d + (summarize (xs ++ ys)).minimum)) =
      (Summary.mk (d + (summarize xs).total)
        (min 0 (d + (summarize xs).minimum))).append (summarize ys)
    rw [ih]
    apply Summary.ext <;> simp only [Summary.append] <;> omega

/-- The total component is the ordinary sum of signed steps. -/
theorem summarize_total (steps : List ℤ) : (summarize steps).total = steps.sum := by
  refine List.rec rfl ?_ steps
  intro d ds ih
  change d + (summarize ds).total = d + ds.sum
  rw [ih]

/-- A lower bound on the summary minimum is exactly a lower bound on every prefix sum. -/
theorem le_summarize_minimum_iff (steps : List ℤ) : ∀ bound : ℤ,
    bound ≤ (summarize steps).minimum ↔ ∀ p ∈ steps.inits, bound ≤ p.sum := by
  refine List.rec ?_ ?_ steps
  · intro bound
    simp [summarize]
  · intro d ds ih bound
    simp only [summarize, List.foldr]
    change bound ≤ min 0 (d + (summarize ds).minimum) ↔ _
    rw [List.inits_cons]
    simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, List.sum_nil]
    rw [le_min_iff]
    have h := ih (bound - d)
    constructor
    · rintro ⟨hzero, hrest⟩
      refine ⟨hzero, ?_⟩
      rintro p ⟨q, hq, rfl⟩
      have hp := h.mp (by omega) q hq
      simp only [List.sum_cons]
      omega
    · rintro ⟨hzero, hrest⟩
      refine ⟨hzero, ?_⟩
      have hp := h.mpr (fun q hq ↦ by
        have hq' := hrest (d :: q) ⟨q, hq, rfl⟩
        simp only [List.sum_cons] at hq'
        omega)
      omega

/-- Accept a balanced sequence of signed steps by its summary. -/
def balanced (steps : List ℤ) : Bool :=
  decide ((summarize steps).total = 0 ∧ 0 ≤ (summarize steps).minimum)

/-- The summary test is exact: total zero and every prefix nonnegative. -/
theorem balanced_eq_true_iff (steps : List ℤ) :
    balanced steps = true ↔ steps.sum = 0 ∧ ∀ p ∈ steps.inits, 0 ≤ p.sum := by
  simp only [balanced, decide_eq_true_eq, summarize_total, le_summarize_minimum_iff]

/-- Interpret packed topology bits, with openings represented by true. -/
def bitSteps (bits : List Bool) : List ℤ := bits.map fun b ↦ if b then 1 else -1

/-- A portable unsigned word's logical bits, least significant first, with explicit width. -/
def wordBits (width word : ℕ) : List Bool :=
  (List.range width).map fun i ↦ word.testBit i

/-- Reference summary of one unsigned word at its declared logical width. -/
def wordSummary (width word : ℕ) : Summary := summarize (bitSteps (wordBits width word))

/-- Reducing any list of blocks agrees with scanning their concatenation. -/
theorem summarize_flatten (blocks : List (List ℤ)) :
    summarize blocks.flatten =
      (blocks.map summarize).foldr Summary.append ⟨0, 0⟩ := by
  refine List.rec rfl ?_ blocks
  intro b bs ih
  simp only [List.flatten_cons, summarize_append, List.map_cons, List.foldr, ih]

/-- Scan left to right using only the current summary as accumulator. -/
def scan (steps : List ℤ) : Summary :=
  steps.foldl (fun s d ↦ s.append (summarize [d])) ⟨0, 0⟩

/-- The accumulator implementation computes the same summary as the specification. -/
theorem scan_eq_summarize (steps : List ℤ) : scan steps = summarize steps := by
  have aux : ∀ ds pre : List ℤ,
      ds.foldl (fun s d ↦ s.append (summarize [d])) (summarize pre) =
        summarize (pre ++ ds) := by
    intro ds
    refine List.rec ?_ ?_ ds
    · intro pre
      simp
    · intro d ds ih pre
      simp only [List.foldl_cons, ← summarize_append]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
  exact aux steps []

end Geb.SuccinctTree
