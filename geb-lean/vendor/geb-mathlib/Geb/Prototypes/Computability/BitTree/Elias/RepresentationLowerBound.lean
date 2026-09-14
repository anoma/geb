/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.List.Nodup
public import Batteries.Data.List.Perm
public import Geb.Prototypes.Computability.BitTree.Encoding

set_option doc.verso true

/-!
# Counting lower bound for lossless tree representations

For fixed fork count {lit}`I` and total payload length {lit}`B`, every injective
binary representation has worst-case length at least {lit}`B`. A fixed comb shape
already contains all {lit}`2^B` choices for its last leaf's payload. There are only
{lit}`2^B - 1` binary words shorter than {lit}`B`, even when codewords need not be prefix-free.

## Main definitions

* {lit}`words` enumerates fixed-length bitstrings using list sections.
* {lit}`payloadComb` embeds arbitrary bitstrings into trees with a prescribed fork count.

## Main statements

* {lit}`bitstring_representation_lower_bound` proves the finite counting bound.
* {lit}`tree_representation_lower_bound` transfers it to trees of fixed size.

## Tags

binary tree, representation size, counting, information lower bound
-/

@[expose] public section

namespace Geb.BitTree.Elias

/-- All binary words of the given length. -/
def words (n : ℕ) : List (List Bool) := (List.replicate n [false, true]).sections

/-- Enumeration extends every shorter word by each possible next bit. -/
theorem words_succ (n : ℕ) :
    words (n + 1) = (words n).flatMap fun w ↦ [false :: w, true :: w] := by
  simp only [words, List.replicate_succ, List.sections, List.map_cons, List.map_nil]

/-- Fixed-length enumeration contains exactly the words of that length. -/
theorem mem_words (n : ℕ) : ∀ w, w ∈ words n ↔ w.length = n := by
  refine Nat.rec ?_ ?_ n
  · intro w
    simp [words]
  · intro n ih w
    rw [words_succ, List.mem_flatMap]
    constructor
    · rintro ⟨v, hv, hw⟩
      have hl := (ih v).mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only [List.length_cons, hl]
    · intro hw
      cases w with
      | nil => simp only [List.length_nil] at hw; omega
      | cons b w =>
        refine ⟨w, (ih w).mpr (by simp only [List.length_cons] at hw; omega), ?_⟩
        cases b <;> simp

/-- There are exactly two to the power of the length binary words. -/
theorem length_words : ∀ n, (words n).length = 2 ^ n := by
  refine Nat.rec rfl ?_
  intro n ih
  rw [words_succ, List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
    ih, Nat.pow_succ, Nat.nsmul_eq_mul]

/-- Fixed-length enumeration has no duplicate words. -/
theorem nodup_words : ∀ n, (words n).Nodup := by
  refine Nat.rec (by simp [words]) ?_
  intro n ih
  rw [words_succ, List.nodup_flatMap]
  refine ⟨fun w _ ↦ by simp, ih.imp ?_⟩
  intro a b hab
  simp [List.disjoint_left, hab]

/-- All binary words strictly shorter than the given bound. -/
def shortWords (n : ℕ) : List (List Bool) := (List.range n).flatMap words

/-- Membership in the bounded enumeration is exactly the strict length bound. -/
theorem mem_shortWords (n : ℕ) (w : List Bool) : w ∈ shortWords n ↔ w.length < n := by
  simp only [shortWords, List.mem_flatMap, List.mem_range, mem_words]
  exact ⟨fun ⟨k, hk, he⟩ ↦ he ▸ hk, fun h ↦ ⟨w.length, h, rfl⟩⟩

/-- The number of words shorter than a bound is one less than its power of two. -/
theorem length_shortWords : ∀ n, (shortWords n).length + 1 = 2 ^ n := by
  refine Nat.rec rfl ?_
  intro n ih
  have he : shortWords (n + 1) = shortWords n ++ words n := by
    simp only [shortWords, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  rw [he, List.length_append, length_words, Nat.pow_succ]
  omega

/-- An injective encoding of all fixed-length words cannot shorten every word. -/
theorem bitstring_representation_lower_bound (code : List Bool → List Bool)
    (hinj : Function.Injective code) (bits bound : ℕ)
    (hbound : ∀ w, w.length = bits → (code w).length ≤ bound) : bits ≤ bound := by
  have hsub : (words bits).map code ⊆ shortWords (bound + 1) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact (mem_shortWords _ _).mpr (by have := hbound v ((mem_words _ _).mp hv); omega)
  have hlen := (List.subperm_of_subset ((nodup_words bits).map hinj) hsub).length_le
  rw [List.length_map, length_words] at hlen
  have hs := length_shortWords (bound + 1)
  by_cases h : bits ≤ bound
  · exact h
  · have hp : 2 ^ (bound + 1) ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- A fixed right comb with empty left leaves and one variable last payload. -/
def payloadComb (forks : ℕ) (w : List Bool) : Tree :=
  Nat.rec (leaf w) (fun _ t ↦ fork (leaf []) t) forks

/-- The payload stored at the rightmost leaf. -/
def lastPayload : Tree → List Bool := WType.elim (List Bool) fun x ↦
  match x with
  | ⟨some s, _⟩ => s
  | ⟨none, f⟩ => f true

/-- Reading the last leaf recovers the word used to build a comb. -/
theorem lastPayload_payloadComb (w : List Bool) : ∀ forks,
    lastPayload (payloadComb forks w) = w :=
  Nat.rec rfl (fun _ ih ↦ ih)

/-- Varying the last payload gives distinct trees. -/
theorem payloadComb_injective (forks : ℕ) : Function.Injective (payloadComb forks) := by
  intro v w h
  have he := congrArg lastPayload h
  simpa only [lastPayload_payloadComb] using he

/-- The comb fixes the fork count while retaining the full payload length. -/
theorem counts_payloadComb (w : List Bool) : ∀ forks,
    counts (payloadComb forks w) = (forks, forks + 1, w.length) := by
  refine Nat.rec rfl ?_
  intro forks ih
  change counts (fork (leaf []) (payloadComb forks w)) = _
  rw [counts_fork, counts_leaf, ih]
  simp only [List.length_nil, Nat.zero_add, Nat.add_comm 1]

/-- Any lossless binary code for trees needs at least the total payload length in the worst case. -/
theorem tree_representation_lower_bound (code : Tree → List Bool)
    (hinj : Function.Injective code) (forks bits bound : ℕ)
    (hbound : ∀ t, (counts t).1 = forks → (counts t).2.2 = bits → (code t).length ≤ bound) :
    bits ≤ bound := by
  apply bitstring_representation_lower_bound (fun w ↦ code (payloadComb forks w))
    (hinj.comp (payloadComb_injective forks)) bits bound
  intro w hw
  apply hbound (payloadComb forks w)
  · rw [counts_payloadComb]
  · rw [counts_payloadComb, hw]

end Geb.BitTree.Elias
