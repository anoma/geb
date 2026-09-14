/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.RepresentationLowerBound
public import Geb.Prototypes.Computability.BitTree.Counter

public import Geb.Prototypes.Computability.BitTree.Elias.Tree

set_option doc.verso true

/-!
# Asymptotic size of the Elias tree representation

Let {lit}`B` be the total payload length and {lit}`L` the number of leaves.
For every positive integer {lit}`k`, a threshold on the average payload length
ensures that the entire representation occupies at most {lit}`(1 + 1/k) * B` bits.
The bound is uniform in tree shape, leaf count, and the distribution of payload lengths.
Thus the representation has {lit}`B + o(B)` bits whenever {lit}`B / L` tends to infinity.

## Main statements

* {lit}`length_encode_affine` bounds representation length with an arbitrary leading slack.
* {lit}`length_encode_le_of_average` gives an explicit average-length threshold.
* {lit}`representation_redundancy_vanishes` states the resulting quantified limit.
* {lit}`length_encode_le_competitor` compares against every lossless code's worst-case bound.

## Implementation notes

The integer precision parameter expresses the epsilon definition of vanishing relative
redundancy without real-number division. Succinctness concerns stored representation bits;
the recognizer's visited work cells are a separate quantity. The limit here requires
diverging average payload length, not merely diverging node count or total payload length.
No navigation index or random-access query bound is asserted.

## References

\[Navarro2016\], Chapter 1, supplies the context of compact representations and the
multivariable little-o convention. The explicit estimates below are derived from the
verified delta-code length formula.

## Tags

Elias delta code, representation size, asymptotic succinctness, redundancy
-/

@[expose] public section

namespace Geb.BitTree.Elias

/-- A linear multiple of an exponent is bounded by its power of two plus a fixed allowance. -/
theorem mul_le_pow_add (a : ℕ) : ∀ s, a * s ≤ 2 ^ s + a * a := by
  refine Nat.rec (by simp) ?_
  intro s ih
  by_cases h : s + 1 ≤ a
  · exact (Nat.mul_le_mul_left a h).trans (Nat.le_add_left _ _)
  · have hs : a ≤ 2 ^ s := by
      have hp : s < 2 ^ s := Nat.lt_two_pow_self
      omega
    rw [Nat.mul_succ, Nat.pow_succ]
    omega

/-- Binary size admits an affine bound with any prescribed inverse slope. -/
theorem mul_size_succ_le (a n : ℕ) :
    a * (n + 1).size ≤ n + (a * a + a + 1) := by
  have hs := size_pos (n + 1) (by omega)
  have hp : 2 ^ ((n + 1).size - 1) ≤ n + 1 := by
    by_cases hp : n + 1 < 2 ^ ((n + 1).size - 1)
    · have hh := Geb.BitTree.Counter.size_le_of_lt_pow (n + 1) ((n + 1).size - 1) hp
      omega
    · omega
  have hh := mul_le_pow_add a ((n + 1).size - 1)
  have he : (n + 1).size = ((n + 1).size - 1) + 1 := by omega
  rw [he, Nat.mul_add, Nat.mul_one]
  omega

/-- Per-leaf allowance in the uniform affine representation bound. -/
def representationAllowance (k : ℕ) : ℕ := (3 * k) * (3 * k) + 5 * k + 1

/-- Node tags and a length header have an arbitrarily small linear payload coefficient. -/
theorem mul_header_le (k n : ℕ) :
    k * (2 + (encodeNat n).length) ≤ n + representationAllowance k := by
  have hl := Nat.mul_le_mul_left k (length_encodeNat_le n)
  have hs := mul_size_succ_le (3 * k) n
  rw [← Nat.mul_assoc, Nat.mul_comm k 3] at hl
  unfold representationAllowance
  rw [Nat.mul_add]
  omega

/-- A uniform affine bound for the representation, including all node tags and leaf headers. -/
theorem length_encode_affine (k : ℕ) (t : Tree) :
    k * (encode t).length + k ≤ (k + 1) * (counts t).2.2 +
      representationAllowance k * (counts t).2.1 :=
  tree_ind (P := fun t ↦ k * (encode t).length + k ≤ (k + 1) * (counts t).2.2 +
      representationAllowance k * (counts t).2.1)
    (fun s ↦ by
      have h := mul_header_le k s.length
      simp only [encode_leaf, List.length_cons, List.length_append, counts_leaf,
        Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h ⊢
      omega)
    (fun l r hl hr ↦ by
      simp only [encode_fork, List.length_cons, List.length_append, counts_fork,
        Nat.mul_add, Nat.mul_one]
      omega) t

/-- Raw payload bits are included verbatim in the representation. -/
theorem payload_le_length_encode (t : Tree) : (counts t).2.2 ≤ (encode t).length := by
  rw [length_encode]
  omega

/-- A sufficiently large average leaf payload makes total relative overhead at most {lit}`1/k`. -/
theorem length_encode_le_of_average (k : ℕ) (t : Tree)
    (h : representationAllowance (2 * k) * (counts t).2.1 ≤ (counts t).2.2) :
    k * (encode t).length ≤ (k + 1) * (counts t).2.2 := by
  have hb := length_encode_affine (2 * k) t
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul] at hb ⊢
  omega

/-- Along every family with diverging average payload length, relative redundancy vanishes. -/
theorem representation_redundancy_vanishes (ts : ℕ → Tree)
    (havg : ∀ m, ∃ n₀, ∀ n ≥ n₀, m * (counts (ts n)).2.1 ≤ (counts (ts n)).2.2) :
    ∀ k, ∃ n₀, ∀ n ≥ n₀,
      k * ((encode (ts n)).length - (counts (ts n)).2.2) ≤ (counts (ts n)).2.2 := by
  intro k
  obtain ⟨n₀, hn⟩ := havg (representationAllowance (2 * k))
  refine ⟨n₀, fun n h ↦ ?_⟩
  have hb := length_encode_le_of_average k (ts n) (hn n h)
  rw [Nat.mul_sub_left_distrib]
  simp only [Nat.add_mul, Nat.one_mul] at hb
  omega

/-- In the long-average-payload regime, the encoding approaches every competing worst-case bound. -/
theorem length_encode_le_competitor (k : ℕ) (t : Tree)
    (havg : representationAllowance (2 * k) * (counts t).2.1 ≤ (counts t).2.2)
    (code : Tree → List Bool) (hinj : Function.Injective code) (bound : ℕ)
    (hbound : ∀ u, (counts u).1 = (counts t).1 → (counts u).2.2 = (counts t).2.2 →
      (code u).length ≤ bound) :
    k * (encode t).length ≤ (k + 1) * bound :=
  (length_encode_le_of_average k t havg).trans (Nat.mul_le_mul_left (k + 1)
    (tree_representation_lower_bound code hinj (counts t).1 (counts t).2.2 bound hbound))

end Geb.BitTree.Elias
