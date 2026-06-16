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
* `mixedRadixInv k t n` — the base-`t` digit-extraction inverse of
  `mixedRadix`, recovering a cube point from its positional index.
* `packM k w t P` — the packed witness number that places the digit-block
  indicator `δ(P a, w)` at base-`2 ^ (2 * w)` position `mixedRadix k t a`.
* `recSeq init step` — the first-order recurrence sequence `s 0 = init`,
  `s (m + 1) = step m (s m)`.
* `histCode init step A n` — the base-`A` positional code of the value
  history `s 0, …, s n` of `recSeq init step`.

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
* `mixedRadixInv_mixedRadix` — `mixedRadixInv` left-inverts `mixedRadix` on
  the cube.
* `deltaBlock_pos_lt` — the digit-block indicator is a positive value below
  `2 ^ (2 * w)`, so it occupies one base-`2 ^ (2 * w)` block.
* `packM_digitsum_eq` — the binary digit sum of the packed witness equals
  `2w` per vanishing cube point and `w` per non-vanishing point.
* `count_zeros_eq` — the count read-off (arXiv:2407.12928, Lemma 3.3 /
  Theorem 3.4): `HW(M) / w − tᵏ` equals the number of cube points where the
  value function vanishes.
* `positional_readoff` — the positional read-off (arXiv:2606.09336,
  Theorem 2): the top base-`A` digit of a bounded positional code is
  recovered by floor division.
* `recurrence_readoff` — the first-order recurrence read-off
  (arXiv:2606.09336, Theorem 2, `k = 1`): an `A`-bounded recurrence's `n`-th
  value is the top base-`A` digit of its history code.

## References

* M. Prunescu and L. Sauras-Altuzarra, *On the representation of
  number-theoretic functions by arithmetic terms*, arXiv:2407.12928
  (the `δ` indicator, cube-sum factorisation, and the count read-off).
* G. Istrate, M. Prunescu and J. M. Shunia, *Undecidability, Chaos and
  Universality in Arithmetic Terms*, arXiv:2606.09336 (Theorem 2, the
  positional read-off of a bounded base-`A` recurrence code).

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

/-- The packed witness number of arXiv:2407.12928, Lemma 3.3: place the
digit-block indicator `δ(P a, w)` at base-`2 ^ (2 * w)` position `v(a)` for
every cube point `a`, where `v = mixedRadix k t` enumerates the cube. -/
def packM (k w t : ℕ) (P : (Fin k → ℕ) → ℕ) : ℕ :=
  ∑ a ∈ cubePoints k t, 2 ^ (2 * w * mixedRadix k t a) * deltaBlock (P a) w

/-- Block range of the digit-block indicator: for `0 < w` and `a < 2 ^ w`,
`δ(a, w)` is a positive value below `2 ^ (2 * w)`, so it fits in one
base-`2 ^ (2 * w)` block. -/
theorem deltaBlock_pos_lt {a w : ℕ} (hw : 0 < w) (ha : a < 2 ^ w) :
    0 < GebLean.deltaBlock a w ∧ GebLean.deltaBlock a w < 2 ^ (2 * w) := by
  have hbig : (2 : ℕ) ≤ 2 ^ w := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hfac2hi : 2 ^ w - a + 1 ≤ 2 ^ w + 1 := by omega
  have hpow : (2 : ℕ) ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  refine ⟨?_, ?_⟩
  · unfold GebLean.deltaBlock
    exact Nat.mul_pos (by omega) (by omega)
  · unfold GebLean.deltaBlock
    rw [hpow]
    calc (2 ^ w - 1) * (2 ^ w - a + 1) ≤ (2 ^ w - 1) * (2 ^ w + 1) :=
          Nat.mul_le_mul_left _ hfac2hi
      _ = 2 ^ w * 2 ^ w - 1 := by
          rw [Nat.sub_one_mul, Nat.mul_add, Nat.mul_one]; omega
      _ < 2 ^ w * 2 ^ w := by
          have : 1 ≤ 2 ^ w * 2 ^ w := Nat.one_le_iff_ne_zero.mpr (by positivity)
          omega

/-- The base-`t` digit-extraction inverse of `mixedRadix`:
`mixedRadixInv k t n i = n / t ^ i % t` recovers the `i`-th coordinate. -/
def mixedRadixInv (k t n : ℕ) : Fin k → ℕ := fun i => n / t ^ (i : ℕ) % t

/-- `mixedRadixInv` left-inverts `mixedRadix` on the cube: the base-`t`
digit extraction recovers a cube point from its positional index. -/
theorem mixedRadixInv_mixedRadix {k t : ℕ} {a : Fin k → ℕ} (ha : ∀ i, a i < t) :
    mixedRadixInv k t (mixedRadix k t a) = a := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    have ht : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) (ha 0)
    have hrec : mixedRadix (k + 1) t a = a 0 + t * mixedRadix k t (Fin.tail a) :=
      mixedRadix_succ k t a
    have htail : mixedRadixInv k t (mixedRadix k t (Fin.tail a)) = Fin.tail a :=
      ih (fun i => ha i.succ)
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [mixedRadixInv, hrec]
      rw [Fin.val_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (ha 0)]
    · intro j
      have hdiv : mixedRadix (k + 1) t a / t ^ ((j.succ : Fin (k + 1)) : ℕ)
          = mixedRadix k t (Fin.tail a) / t ^ (j : ℕ) := by
        rw [hrec]
        have hjval : ((j.succ : Fin (k + 1)) : ℕ) = (j : ℕ) + 1 := by simp
        have hinner : (a 0 + t * mixedRadix k t (Fin.tail a)) / t
            = mixedRadix k t (Fin.tail a) := by
          rw [Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt (ha 0), Nat.zero_add]
        rw [hjval, pow_succ, Nat.mul_comm (t ^ (j : ℕ)) t, ← Nat.div_div_eq_div_mul,
          hinner]
      simp only [mixedRadixInv, hdiv]
      have := congrFun htail j
      simpa only [mixedRadixInv, Fin.tail] using this

/-- The carry-free digit-sum read-off (arXiv:2407.12928, Lemma 3.3): the
binary digit sum of the packed witness equals the per-block contribution
`2w` at vanishing cube points and `w` elsewhere. -/
theorem packM_digitsum_eq (k w t : ℕ) (hw : 0 < w)
    (P : (Fin k → ℕ) → ℕ) (hP : ∀ a ∈ cubePoints k t, P a < 2 ^ w) :
    (Nat.digits 2 (packM k w t P)).sum
      = ∑ a ∈ cubePoints k t, (if P a = 0 then 2 * w else w) := by
  -- the block value, reindexed by the base-`t` digit-extraction inverse
  set g : ℕ → ℕ := fun n => deltaBlock (P (mixedRadixInv k t n)) w with hg_def
  -- every flat index below `t ^ k` is the image of a cube point
  have hgbnd : ∀ n, n < t ^ k → g n < 2 ^ (2 * w) := by
    intro n hn
    have hmem : n ∈ Finset.range (t ^ k) := Finset.mem_range.mpr hn
    rw [← image_mixedRadix_cubePoints k t, Finset.mem_image] at hmem
    obtain ⟨a, ha, hav⟩ := hmem
    have hacube : ∀ i, a i < t := mem_cubePoints.mp ha
    have hinv : mixedRadixInv k t n = a := by
      rw [← hav]; exact mixedRadixInv_mixedRadix hacube
    have hPlt : P (mixedRadixInv k t n) < 2 ^ w := by rw [hinv]; exact hP a ha
    exact (deltaBlock_pos_lt hw hPlt).2
  -- the packed witness in `hw_pack_additive`'s flat block-sum shape
  have hpack : packM k w t P = ∑ i ∈ Finset.range (t ^ k), 2 ^ (2 * w * i) * g i := by
    rw [← image_mixedRadix_cubePoints k t,
      Finset.sum_image (mixedRadix_injOn k t), packM]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hacube : ∀ i, a i < t := mem_cubePoints.mp ha
    rw [hg_def]
    simp only [mixedRadixInv_mixedRadix hacube]
  rw [hpack, hw_pack_additive w (t ^ k) g hgbnd]
  -- reindex the per-block digit sums back onto the cube
  rw [← image_mixedRadix_cubePoints k t, Finset.sum_image (mixedRadix_injOn k t)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hacube : ∀ i, a i < t := mem_cubePoints.mp ha
  have hPa : P a < 2 ^ w := hP a ha
  rw [hg_def]
  simp only [mixedRadixInv_mixedRadix hacube]
  rw [← GebLean.hwClosed_eq _ (deltaBlock_pos_lt hw hPa).1,
    GebLean.hwClosed_deltaBlock hPa]

/-- The count read-off (arXiv:2407.12928, Lemma 3.3 / Theorem 3.4):
`HW(M)/w − tᵏ` equals the number of cube points where `P` vanishes. -/
theorem count_zeros_eq (k w t : ℕ) (hw : 0 < w)
    (P : (Fin k → ℕ) → ℕ) (hP : ∀ a ∈ cubePoints k t, P a < 2 ^ w) :
    (Nat.digits 2 (packM k w t P)).sum / w - t ^ k
      = ((cubePoints k t).filter (fun a => P a = 0)).card := by
  set d := ((cubePoints k t).filter (fun a => P a = 0)).card with hd_def
  have hdle : d ≤ t ^ k := by
    rw [hd_def, ← card_cubePoints k t]
    exact Finset.card_filter_le _ _
  -- the digit sum splits over the vanishing-point filter and its complement
  have hsplit : (Nat.digits 2 (packM k w t P)).sum = (d + t ^ k) * w := by
    rw [packM_digitsum_eq k w t hw P hP]
    rw [← Finset.sum_filter_add_sum_filter_not (cubePoints k t) (fun a => P a = 0)]
    have hpos : ∑ a ∈ (cubePoints k t).filter (fun a => P a = 0),
        (if P a = 0 then 2 * w else w) = d * (2 * w) := by
      rw [Finset.sum_congr rfl (fun a ha => by
        rw [if_pos (Finset.mem_filter.mp ha).2])]
      rw [Finset.sum_const, hd_def, smul_eq_mul]
    have hneg : ∑ a ∈ (cubePoints k t).filter (fun a => ¬ P a = 0),
        (if P a = 0 then 2 * w else w) = (t ^ k - d) * w := by
      rw [Finset.sum_congr rfl (fun a ha => by
        rw [if_neg (Finset.mem_filter.mp ha).2])]
      have hcard : ((cubePoints k t).filter (fun a => ¬ P a = 0)).card = t ^ k - d := by
        have := Finset.card_filter_add_card_filter_not
          (s := cubePoints k t) (fun a => P a = 0)
        rw [card_cubePoints, ← hd_def] at this
        omega
      rw [Finset.sum_const, smul_eq_mul, hcard]
    rw [hpos, hneg]
    have hsum : d * (2 * w) + (t ^ k - d) * w = (d + t ^ k) * w := by
      have hdw : d * w ≤ t ^ k * w := Nat.mul_le_mul_right w hdle
      rw [Nat.sub_mul, Nat.add_mul, Nat.mul_comm d (2 * w), Nat.two_mul, Nat.add_mul,
        Nat.mul_comm w d]
      omega
    exact hsum
  rw [hsplit, Nat.mul_div_cancel _ hw, Nat.add_sub_cancel]

/-- Positional read-off (arXiv:2606.09336, Theorem 2): the top base-`A`
digit of a bounded positional code is recovered by floor division. -/
theorem positional_readoff (A n : ℕ) (a : ℕ → ℕ) (hA : 0 < A)
    (ha : ∀ k, k ≤ n → a k < A) :
    (∑ k ∈ Finset.range (n + 1), a k * A ^ k) / A ^ n = a n := by
  rw [Finset.sum_range_succ]
  have hlow : (∑ k ∈ Finset.range n, a k * A ^ k) < A ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hlt : (∑ k ∈ Finset.range n, a k * A ^ k) < A ^ n :=
        ih (fun k hk => ha k (Nat.le_succ_of_le hk))
      have htop : a n * A ^ n ≤ (A - 1) * A ^ n :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (ha n (Nat.le_succ n)))
      calc
        (∑ k ∈ Finset.range n, a k * A ^ k) + a n * A ^ n
            < A ^ n + (A - 1) * A ^ n := Nat.add_lt_add_of_lt_of_le hlt htop
        _ = A ^ (n + 1) := by
              rw [pow_succ, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (A ^ n) A]
              have hle : A ^ n ≤ A * A ^ n := Nat.le_mul_of_pos_left _ hA
              omega
  rw [Nat.add_mul_div_right _ _ (Nat.pow_pos hA : 0 < A ^ n), Nat.div_eq_of_lt hlow,
    Nat.zero_add]

/-- A first-order recurrence sequence `s 0 = init`, `s (m + 1) = step m (s m)`. -/
def recSeq (init : ℕ) (step : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => init
  | m + 1 => step m (recSeq init step m)

/-- The base-`A` positional code of the value history `s 0, …, s n`, where
`s = recSeq init step`. The `Era`-term realisation, packing the step's
Diophantine encoding via the count engine, is `Phase 6`; this is the
`ℕ`-level code. -/
def histCode (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), recSeq init step k * A ^ k

/-- First-order recurrence read-off (arXiv:2606.09336, Theorem 2, `k = 1`):
an `A`-bounded recurrence's `n`-th value is the top base-`A` digit of its
history code. -/
theorem recurrence_readoff (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ)
    (n : ℕ) (hbound : ∀ j, j ≤ n → recSeq init step j < A) :
    recSeq init step n = histCode init step A n / A ^ n := by
  have hA : 0 < A := Nat.lt_of_le_of_lt (Nat.zero_le _) (hbound 0 (Nat.zero_le n))
  exact (positional_readoff A n (recSeq init step) hA hbound).symm

end GebLean.EraHypercube
