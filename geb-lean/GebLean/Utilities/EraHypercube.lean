import GebLean.Utilities.ArithClosedForms
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Mixed-radix enumeration of the side-`t` hypercube

This module enumerates the 0-indexed cube `{0, …, t − 1}^k`, presented as a
`Finset` of total functions `Fin k → ℕ`, by the base-`t` positional index
`a ↦ a₀ + a₁ t + ⋯ + a_{k−1} t^{k−1}`. The enumeration is the `v` index
function of Prunescu–Sauras-Altuzarra, arXiv:2407.12928, Lemma 3.3; later
tasks of the Era bounded-sum engine reindex a cube sum onto a flat
`Finset.range (t ^ k)` sum through it.

## Main definitions

* `cubePoints k t` — the side-`t` cube `{0, …, t − 1}^k` as a `Finset` of
  total functions `Fin k → ℕ`.
* `mixedRadix k t a` — the base-`t` positional index of a cube point `a`.

## Main statements

* `mixedRadix_lt` — the range bound: a cube point indexes below `t ^ k`.
* `mixedRadix_injOn` — `mixedRadix k t` is injective on `cubePoints k t`.
* `card_cubePoints` — the cube has `t ^ k` points.
* `image_mixedRadix_cubePoints` — the image of the cube under `mixedRadix`
  is exactly `Finset.range (t ^ k)`: the enumeration is a bijection of the
  cube onto the flat index range.
* `pack_lt` — a base-`2 ^ (2 * w)` block-packed number with each block below
  `2 ^ (2 * w)` is below `2 ^ (2 * w * N)`.
* `hw_pack_additive` — the binary digit sum of a base-`2 ^ (2 * w)`
  block-packed number is the sum of the per-block digit sums (the no-carry
  step of arXiv:2407.12928, Lemma 3.3).

## References

* J. Prunescu and L. Sauras-Altuzarra, *An arithmetization of the Goodstein
  process and a closed form for the `T(n)` length function*,
  arXiv:2407.12928, Lemma 3.3.

## Tags

mixed radix, hypercube, base-`t` digits, enumeration
-/

namespace GebLean.EraHypercube

open Finset

/-- The side-`t` cube `{0, …, t − 1}^k` as a `Finset` of total functions
`Fin k → ℕ`. A function lies in `cubePoints k t` iff each coordinate is
below `t`. -/
def cubePoints (k t : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range t)

/-- The base-`t` positional index of a cube point, 0-indexed:
`mixedRadix k t a = a₀ + a₁ t + ⋯ + a_{k−1} t^{k−1}`. -/
def mixedRadix (k t : ℕ) (a : Fin k → ℕ) : ℕ :=
  ∑ i, a i * t ^ (i : ℕ)

/-- A cube point `a ∈ cubePoints k t` is characterised by its coordinates
each lying below `t`. -/
theorem mem_cubePoints {k t : ℕ} {a : Fin k → ℕ} :
    a ∈ cubePoints k t ↔ ∀ i, a i < t := by
  simp only [cubePoints, Fintype.mem_piFinset, Finset.mem_range]

/-- The range bound: a function whose coordinates are all below `t` has
mixed-radix index below `t ^ k`. -/
theorem mixedRadix_lt {k t : ℕ} {a : Fin k → ℕ} (ha : ∀ i, a i < t) :
    mixedRadix k t a < t ^ k := by
  induction k with
  | zero => simp [mixedRadix]
  | succ k ih =>
    rw [mixedRadix, Fin.sum_univ_castSucc]
    have hlt : ∑ i : Fin k, a i.castSucc * t ^ (i : ℕ) < t ^ k :=
      ih (fun i => ha i.castSucc)
    have htop : a (Fin.last k) * t ^ k ≤ (t - 1) * t ^ k :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (ha (Fin.last k)))
    calc
      (∑ i : Fin k, a i.castSucc * t ^ (i : ℕ)) + a (Fin.last k) * t ^ k
          < t ^ k + (t - 1) * t ^ k := by
            exact Nat.add_lt_add_of_lt_of_le hlt htop
      _ = t ^ (k + 1) := by
            have ht : 1 ≤ t := Nat.lt_of_le_of_lt (Nat.zero_le _) (ha (Fin.last k))
            have hle : t ^ k ≤ t * t ^ k := Nat.le_mul_of_pos_left _ ht
            rw [pow_succ, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (t ^ k) t]
            omega

/-- The first-coordinate recurrence: the mixed-radix index of a cube point on
`Fin (k + 1)` splits as its zeroth coordinate plus `t` times the index of its
tail. -/
theorem mixedRadix_succ (k t : ℕ) (a : Fin (k + 1) → ℕ) :
    mixedRadix (k + 1) t a = a 0 + t * mixedRadix k t (Fin.tail a) := by
  rw [mixedRadix, Fin.sum_univ_succ, mixedRadix, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, Fin.tail, pow_succ]
  refine congrArg (a 0 + ·) (Finset.sum_congr rfl fun x _ => ?_)
  ring

/-- `mixedRadix k t` is injective on the side-`t` cube: a cube point is
determined by its base-`t` positional index. -/
theorem mixedRadix_injOn (k t : ℕ) :
    Set.InjOn (mixedRadix k t) (cubePoints k t) := by
  induction k with
  | zero =>
    intro a _ b _ _
    exact funext (fun i => i.elim0)
  | succ k ih =>
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_cubePoints] at ha hb
    rw [mixedRadix_succ, mixedRadix_succ] at hab
    have ht : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) (ha 0)
    have h0 : a 0 = b 0 := by
      have := congrArg (· % t) hab
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0),
        Nat.mod_eq_of_lt (hb 0)] using this
    have htail : mixedRadix k t (Fin.tail a) = mixedRadix k t (Fin.tail b) := by
      have hsum : t * mixedRadix k t (Fin.tail a)
          = t * mixedRadix k t (Fin.tail b) := by omega
      exact Nat.eq_of_mul_eq_mul_left ht hsum
    have htaileq : Fin.tail a = Fin.tail b :=
      ih (mem_cubePoints.mpr fun i => ha i.succ)
        (mem_cubePoints.mpr fun i => hb i.succ) htail
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, h0, htaileq]

/-- The side-`t` cube on `Fin k` has `t ^ k` points. -/
theorem card_cubePoints (k t : ℕ) : (cubePoints k t).card = t ^ k := by
  rw [cubePoints, Fintype.card_piFinset]
  simp [Finset.card_range]

/-- The mixed-radix index is a bijection of the side-`t` cube onto the flat
index range: the image of `cubePoints k t` under `mixedRadix k t` is exactly
`Finset.range (t ^ k)`. This is the reindexing identity consumed when a sum
over the cube is rewritten as a sum over `Finset.range (t ^ k)`. -/
theorem image_mixedRadix_cubePoints (k t : ℕ) :
    (cubePoints k t).image (mixedRadix k t) = Finset.range (t ^ k) := by
  have hsub : (cubePoints k t).image (mixedRadix k t) ⊆ Finset.range (t ^ k) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨a, ha, rfl⟩ := hn
    exact Finset.mem_range.mpr (mixedRadix_lt (mem_cubePoints.mp ha))
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_range, Finset.card_image_of_injOn (mixedRadix_injOn k t),
    card_cubePoints]

/-- Geometric bound on a base-`2 ^ (2 * w)` block sum: if each block value
`g i` is below `2 ^ (2 * w)`, the packed number occupies fewer than `N` blocks,
hence `∑_{i < N} 2 ^ (2 * w * i) * g i < 2 ^ (2 * w * N)`. -/
theorem pack_lt (w N : ℕ) (g : ℕ → ℕ) (hg : ∀ i, i < N → g i < 2 ^ (2 * w)) :
    (∑ i ∈ Finset.range N, 2 ^ (2 * w * i) * g i) < 2 ^ (2 * w * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hlow : (∑ i ∈ Finset.range N, 2 ^ (2 * w * i) * g i) < 2 ^ (2 * w * N) :=
      ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    have htop : 2 ^ (2 * w * N) * g N + 2 ^ (2 * w * N)
        ≤ 2 ^ (2 * w * N) * 2 ^ (2 * w) := by
      have := Nat.mul_le_mul_left (2 ^ (2 * w * N))
        (Nat.succ_le_of_lt (hg N (Nat.lt_succ_self N)))
      rw [Nat.mul_succ] at this
      omega
    have hpow : 2 ^ (2 * w * (N + 1)) = 2 ^ (2 * w * N) * 2 ^ (2 * w) := by
      rw [← pow_add]; ring_nf
    rw [hpow]
    omega

/-- Hamming-weight additivity over non-overlapping base-`2 ^ (2 * w)` blocks:
if `g i < 2 ^ (2 * w)` for every `i < N`, the binary digit sum of the packed
number is the sum of the per-block digit sums. -/
theorem hw_pack_additive (w N : ℕ) (g : ℕ → ℕ)
    (hg : ∀ i, i < N → g i < 2 ^ (2 * w)) :
    (Nat.digits 2 (∑ i ∈ Finset.range N, 2 ^ (2 * w * i) * g i)).sum
      = ∑ i ∈ Finset.range N, (Nat.digits 2 (g i)).sum := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set L := ∑ i ∈ Finset.range N, 2 ^ (2 * w * i) * g i
    have hLlt : L < 2 ^ (2 * w * N) :=
      pack_lt w N g (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    rw [GebLean.sum_digits_two_add (2 * w * N) L (g N) hLlt]
    rw [ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))]

/-- Cube-sum factorisation (arXiv:2407.12928, Lemma 3.2): a sum over the
cube of a product of per-coordinate weighted geometric terms factors into a
product of single-variable sums. -/
theorem cubeSum_factor (k : ℕ) (u : Fin k → ℕ) (vbase : Fin k → ℕ) (t : ℕ) :
    (∑ a ∈ cubePoints k t, ∏ i, (a i) ^ (u i) * (vbase i) ^ (a i))
      = ∏ i, (∑ j ∈ Finset.range t, j ^ (u i) * (vbase i) ^ j) := by
  rw [cubePoints, Finset.prod_univ_sum]

end GebLean.EraHypercube
