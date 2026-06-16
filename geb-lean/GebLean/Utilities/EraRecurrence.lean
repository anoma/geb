import GebLean.Utilities.EraHypercube
import GebLean.Utilities.EraDiophantine

/-!
# The positional-coding digit predicate `piDigit`

This module transcribes the base-`A` digit-extraction predicate of
arXiv:2606.09336, Lemma 3 (p. 8): the relation that holds iff `a` is the
`j`-th base-`A` digit of `x`, additionally constrained by `j ≤ n`. The
predicate is stated through an existential positional decomposition
`x = λ₁ + a·Aʲ + λ₂·A^{j+1}` with `λ₁ < Aʲ` and `a < A`, and is shown to
coincide with the closed form `a = x / Aʲ % A` whenever `1 ≤ A` and
`j ≤ n`. Later tasks of the Era recurrence read-off use `piDigit` to name
the per-step digit of a recurrence's history code.

## Main definitions

* `piDigit` — the base-`A` digit-extraction predicate of
  arXiv:2606.09336, Lemma 3.

## Main statements

* `piDigit_iff` — under `1 ≤ A` and `j ≤ n`, `piDigit x A j n a` holds iff
  `a = x / A ^ j % A`.

## References

* G. Istrate, M. Prunescu and J. M. Shunia, *Undecidability, Chaos and
  Universality in Arithmetic Terms*, arXiv:2606.09336, Lemma 3 (p. 8),
  the base-`A` positional digit predicate. Local copy:
  `/home/terence/wingeb/undecidability-chaos-universality-arithmetic-terms.pdf`.

## Tags

positional coding, base-`A` digits, digit extraction, recurrence read-off
-/

namespace GebLean.EraRecurrence

/-- The base-`A` digit-extraction predicate of arXiv:2606.09336, Lemma 3:
`piDigit x A j n a` holds iff `a` is the `j`-th base-`A` digit of `x` and
`j ≤ n`. Equivalent to `a = x / A ^ j % A`. -/
def piDigit (x A j n a : ℕ) : Prop :=
  (∃ l₁ l₂, x = l₁ + a * A ^ j + l₂ * A ^ (j + 1) ∧ l₁ < A ^ j) ∧ a < A ∧ j ≤ n

theorem piDigit_iff (x A j n a : ℕ) (hA : 1 ≤ A) (hj : j ≤ n) :
    piDigit x A j n a ↔ a = x / A ^ j % A := by
  have hApos : 0 < A ^ j := Nat.pow_pos hA
  constructor
  · rintro ⟨⟨l₁, l₂, hx, hl₁⟩, haA, _⟩
    subst hx
    rw [Nat.pow_succ]
    -- `x / Aʲ = a + l₂ * A` after dividing out the low part `l₁ < Aʲ`.
    have hdiv : (l₁ + a * A ^ j + l₂ * (A ^ j * A)) / A ^ j = a + l₂ * A := by
      rw [show l₁ + a * A ^ j + l₂ * (A ^ j * A)
            = l₁ + (a + l₂ * A) * A ^ j by ring]
      rw [Nat.add_mul_div_right _ _ hApos, Nat.div_eq_of_lt hl₁, Nat.zero_add]
    rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt haA]
  · intro ha
    refine ⟨⟨x % A ^ j, x / A ^ (j + 1), ?_, Nat.mod_lt _ hApos⟩, ?_, hj⟩
    · subst ha
      -- Reassemble `x` from its low remainder, the extracted digit, and the
      -- high quotient: `x = x % Aʲ + (x / Aʲ % A) * Aʲ + (x / A^{j+1}) * A^{j+1}`.
      have hdm₁ := Nat.div_add_mod x (A ^ j)
      have hdm₂ := Nat.div_add_mod (x / A ^ j) A
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, eq_comm]
      -- After `← Nat.div_div_eq_div_mul`, the high quotient is `x / Aʲ / A`.
      calc x % A ^ j + x / A ^ j % A * A ^ j + x / A ^ j / A * (A ^ j * A)
          = x % A ^ j + (A * (x / A ^ j / A) + x / A ^ j % A) * A ^ j := by ring
        _ = x % A ^ j + x / A ^ j * A ^ j := by rw [hdm₂]
        _ = A ^ j * (x / A ^ j) + x % A ^ j := by ring
        _ = x := hdm₁
    · rw [ha]
      exact Nat.mod_lt _ hA

open GebLean.EraHypercube

/-- Geometric bound on a positional partial sum: if each coefficient `a k`
for `k < m` is below `A`, then `∑_{k < m} a_k A^k < A^m`. -/
theorem positional_partial_lt (A m : ℕ) (a : ℕ → ℕ) (hA : 0 < A)
    (ha : ∀ k, k < m → a k < A) :
    (∑ k ∈ Finset.range m, a k * A ^ k) < A ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hlt : (∑ k ∈ Finset.range m, a k * A ^ k) < A ^ m :=
      ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
    have htop : a m * A ^ m ≤ (A - 1) * A ^ m :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (ha m (Nat.lt_succ_self m)))
    calc
      (∑ k ∈ Finset.range m, a k * A ^ k) + a m * A ^ m
          < A ^ m + (A - 1) * A ^ m := Nat.add_lt_add_of_lt_of_le hlt htop
      _ = A ^ (m + 1) := by
            rw [pow_succ, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (A ^ m) A]
            have hle : A ^ m ≤ A * A ^ m := Nat.le_mul_of_pos_left _ hA
            omega

/-- Interior digit extraction from a positional code (arXiv:2606.09336,
Lemma 3, generalised to any digit `j ≤ n`): the `j`-th base-`A` digit of
`∑_{k ≤ n} a_k A^k` is `a_j`, provided every coefficient is below `A`. -/
theorem digit_of_code (A n j : ℕ) (a : ℕ → ℕ) (hA : 0 < A)
    (ha : ∀ k, k ≤ n → a k < A) (hj : j ≤ n) :
    (∑ k ∈ Finset.range (n + 1), a k * A ^ k) / A ^ j % A = a j := by
  -- Express the code as `piDigit`'s positional decomposition and read off the
  -- digit through `piDigit_iff`.
  set x := ∑ k ∈ Finset.range (n + 1), a k * A ^ k with hx
  refine ((piDigit_iff x A j n (a j) hA hj).mp ?_).symm
  refine ⟨⟨∑ k ∈ Finset.range j, a k * A ^ k,
    ∑ k ∈ Finset.range (n - j), a (j + 1 + k) * A ^ k, ?_, ?_⟩, ha j hj, hj⟩
  · -- Split the code at index `j` into low part, `a j · A^j`, and high part.
    rw [hx]
    have hsplit : ∑ k ∈ Finset.range (n + 1), a k * A ^ k
        = (∑ k ∈ Finset.range j, a k * A ^ k)
          + (∑ k ∈ Finset.Ico j (n + 1), a k * A ^ k) := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_succ_of_le hj)]
    rw [hsplit]
    have hIco : ∑ k ∈ Finset.Ico j (n + 1), a k * A ^ k
        = a j * A ^ j
          + (∑ k ∈ Finset.range (n - j), a (j + 1 + k) * A ^ k) * A ^ (j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hlen : n + 1 - j = (n - j) + 1 := by omega
      rw [hlen, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Finset.sum_mul]
      have hcong : ∀ k ∈ Finset.range (n - j),
          a (j + (k + 1)) * A ^ (j + (k + 1))
            = a (j + 1 + k) * A ^ k * A ^ (j + 1) := by
        intro k _
        rw [show j + (k + 1) = j + 1 + k by ring,
          show j + 1 + k = k + (j + 1) by ring, pow_add]
        ring
      rw [Finset.sum_congr rfl hcong]
      ring
    rw [hIco]
    ring
  · -- The low part is below `A^j` by the geometric bound.
    exact positional_partial_lt A j a hA
      (fun k hk => ha k (Nat.le_trans (Nat.le_of_lt hk) hj))

/-- The recurrence-instance predicate (arXiv:2606.09336, master relation,
`k = 1`): index `j` "hits" for code `x` when consecutive base-`A`
digits `a_j, a_{j+1}` of `x` satisfy `a_{j+1} = step j a_j`. -/
def hitsAt (step : ℕ → ℕ → ℕ) (A x j : ℕ) : Prop :=
  step j (x / A ^ j % A) = x / A ^ (j + 1) % A

/-- `hitsAt` is decidable: it unfolds to an equality of naturals. -/
instance (step : ℕ → ℕ → ℕ) (A x j : ℕ) : Decidable (hitsAt step A x j) :=
  Nat.decEq _ _

/-- The number of recurrence instances `0 ≤ j < n` satisfied by code `x`
(arXiv:2606.09336, Claim 3, `G(n, y)(x)`). -/
def hitCount (step : ℕ → ℕ → ℕ) (A x n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => hitsAt step A x j)).card

/-- Positional uniqueness: two naturals below `A ^ (n + 1)` with equal
base-`A` digit `· / A^j % A` at every position `j ≤ n` are equal. -/
theorem eq_of_digits_eq (A n x y : ℕ) (hA : 0 < A)
    (hx : x < A ^ (n + 1)) (hy : y < A ^ (n + 1))
    (hdig : ∀ j, j ≤ n → x / A ^ j % A = y / A ^ j % A) :
    x = y := by
  induction n generalizing x y with
  | zero =>
    have h0 := hdig 0 (Nat.le_refl 0)
    simp only [pow_zero, Nat.div_one] at h0
    rw [pow_one] at hx hy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h0
  | succ n ih =>
    -- The bottom digit agrees, and the higher quotients agree by induction.
    have hbot : x % A = y % A := by
      have := hdig 0 (Nat.zero_le _)
      simpa using this
    have hquot : x / A = y / A := by
      refine ih (x / A) (y / A) ?_ ?_ ?_
      · rw [Nat.div_lt_iff_lt_mul hA, ← pow_succ]; exact hx
      · rw [Nat.div_lt_iff_lt_mul hA, ← pow_succ]; exact hy
      · intro j hj
        have hjs : j + 1 ≤ n + 1 := Nat.succ_le_succ hj
        have := hdig (j + 1) hjs
        rwa [pow_succ, Nat.mul_comm (A ^ j) A, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul] at this
    calc x = A * (x / A) + x % A := (Nat.div_add_mod x A).symm
      _ = A * (y / A) + y % A := by rw [hquot, hbot]
      _ = y := Nat.div_add_mod y A

/-- arXiv:2606.09336, Claim 4 (`k = 1`): for `A` a strict bound on the
trajectory `recSeq init step` up to `n`, the hit count is maximal (`= n`)
with correct initial digit iff the code `x` is `histCode init step A n`. -/
theorem hitCount_eq_max_iff (init : ℕ) (step : ℕ → ℕ → ℕ) (A n : ℕ)
    (hbound : ∀ j, j ≤ n → recSeq init step j < A)
    (x : ℕ) (hx : x < A ^ (n + 1)) :
    (hitCount step A x n = n ∧ x / A ^ 0 % A = init)
      ↔ x = histCode init step A n := by
  have hA : 0 < A := Nat.lt_of_le_of_lt (Nat.zero_le _) (hbound 0 (Nat.zero_le n))
  -- Every base-`A` digit of `histCode` up to `n` is the recurrence value.
  have hcode_dig : ∀ j, j ≤ n →
      histCode init step A n / A ^ j % A = recSeq init step j := by
    intro j hj
    exact digit_of_code A n j (recSeq init step) hA hbound hj
  constructor
  · -- (⟹) all hits plus correct initial digit determine `x` as `histCode`.
    rintro ⟨hcount, hinit⟩
    -- Each `j < n` hits, since the filter exhausts `range n`.
    have hall : ∀ j ∈ Finset.range n, hitsAt step A x j := by
      have hfilt : (Finset.range n).filter (fun j => hitsAt step A x j)
          = Finset.range n := by
        refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
        rw [Finset.card_range]
        exact Nat.le_of_eq hcount.symm
      intro j hj
      have : j ∈ (Finset.range n).filter (fun j => hitsAt step A x j) := by
        rw [hfilt]; exact hj
      exact (Finset.mem_filter.mp this).2
    -- The `j`-th digit of `x` equals `recSeq init step j` for all `j ≤ n`.
    have hxdig : ∀ j, j ≤ n → x / A ^ j % A = recSeq init step j := by
      intro j hj
      induction j with
      | zero => rwa [pow_zero, Nat.div_one] at hinit ⊢
      | succ j ih =>
        have hjn : j < n := Nat.lt_of_succ_le hj
        have hjle : j ≤ n := Nat.le_of_lt hjn
        have hhit := hall j (Finset.mem_range.mpr hjn)
        rw [hitsAt, ih hjle] at hhit
        rw [recSeq]
        exact hhit.symm
    -- Positional uniqueness closes the goal.
    refine eq_of_digits_eq A n x (histCode init step A n) hA hx ?_ ?_
    · rw [histCode]
      exact positional_partial_lt A (n + 1) (recSeq init step) hA
        (fun k hk => hbound k (Nat.le_of_lt_succ hk))
    · intro j hj
      rw [hxdig j hj, hcode_dig j hj]
  · -- (⟸) for `x = histCode`, every instance hits and the initial digit is `init`.
    rintro rfl
    refine ⟨?_, ?_⟩
    · have hfilt : (Finset.range n).filter
          (fun j => hitsAt step A (histCode init step A n) j) = Finset.range n := by
        refine Finset.filter_true_of_mem ?_
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        rw [hitsAt, hcode_dig j (Nat.le_of_lt hjn),
          hcode_dig (j + 1) (Nat.succ_le_of_lt hjn), recSeq]
      rw [hitCount, hfilt, Finset.card_range]
    · have h0 := hcode_dig 0 (Nat.zero_le n)
      rw [recSeq] at h0
      exact h0

/-- The number of ordered pairs `(ω₁, ω₂)` with `ω₁ < B`, `ω₂ < B` and
`ω₁ + ω₂ + 1 = C` is `C`, provided `C ≤ B` (so the range contains every
solution). arXiv:2606.09336, Claim 5: the `ω₁+ω₂+1` counting trick. -/
theorem card_pairs_succ_sum (B C : ℕ) (hCB : C ≤ B) :
    ((Finset.range B ×ˢ Finset.range B).filter (fun p => p.1 + p.2 + 1 = C)).card
      = C := by
  have hcard : ((Finset.range B ×ˢ Finset.range B).filter
      (fun p => p.1 + p.2 + 1 = C)).card = (Finset.range C).card := by
    refine Finset.card_nbij' (fun p => p.1) (fun i => (i, C - 1 - i)) ?_ ?_ ?_ ?_
    · rintro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · rintro i hi
      simp only [Finset.coe_range, Set.mem_Iio] at hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Finset.mem_range]
      refine ⟨⟨Nat.lt_of_lt_of_le hi hCB, ?_⟩, ?_⟩
      · omega
      · omega
    · rintro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Finset.mem_range] at hp
      obtain ⟨⟨-, -⟩, hsum⟩ := hp
      rw [Prod.ext_iff]
      refine ⟨rfl, ?_⟩
      change C - 1 - p.1 = p.2
      omega
    · rintro i hi
      rfl
  rw [hcard, Finset.card_range]

/-- The `E₂` solution count (arXiv:2606.09336, Claim 5, `k = 1`): the
number of pairs `(ω₁, ω₂)` in the square `[0, A^(n+1))²` whose induced code
`x = ω₁ + ω₂ + 1` is a valid, bounded, maximal-hit trajectory code. -/
def solCount (init : ℕ) (step : ℕ → ℕ → ℕ) (A n : ℕ) : ℕ :=
  ((Finset.range (A ^ (n + 1)) ×ˢ Finset.range (A ^ (n + 1))).filter
    (fun p => hitCount step A (p.1 + p.2 + 1) n = n
      ∧ (p.1 + p.2 + 1) / A ^ 0 % A = init
      ∧ p.1 + p.2 + 1 < A ^ (n + 1))).card

/-- arXiv:2606.09336, Claim 5 (`k = 1`): the `E₂` solution count equals the
history code. -/
theorem solCount_eq_histCode (init : ℕ) (step : ℕ → ℕ → ℕ) (A n : ℕ)
    (hbound : ∀ j, j ≤ n → recSeq init step j < A) :
    solCount init step A n = histCode init step A n := by
  have hA : 0 < A := Nat.lt_of_le_of_lt (Nat.zero_le _) (hbound 0 (Nat.zero_le n))
  set H := histCode init step A n with hH
  set t := A ^ (n + 1) with ht
  have hHt : H < t := by
    rw [hH, ht, histCode]
    exact positional_partial_lt A (n + 1) (recSeq init step) hA
      (fun k hk => hbound k (Nat.le_of_lt_succ hk))
  have hpred : ∀ p : ℕ × ℕ,
      (hitCount step A (p.1 + p.2 + 1) n = n
        ∧ (p.1 + p.2 + 1) / A ^ 0 % A = init
        ∧ p.1 + p.2 + 1 < t)
        ↔ p.1 + p.2 + 1 = H := by
    intro p
    constructor
    · rintro ⟨hcount, hinit, hlt⟩
      exact (hitCount_eq_max_iff init step A n hbound (p.1 + p.2 + 1) hlt).mp
        ⟨hcount, hinit⟩
    · intro heq
      have hlt : p.1 + p.2 + 1 < t := heq ▸ hHt
      obtain ⟨hcount, hinit⟩ :=
        (hitCount_eq_max_iff init step A n hbound (p.1 + p.2 + 1) hlt).mpr heq
      exact ⟨hcount, hinit, hlt⟩
  rw [solCount, ← ht]
  rw [show (Finset.range t ×ˢ Finset.range t).filter
        (fun p => hitCount step A (p.1 + p.2 + 1) n = n
          ∧ (p.1 + p.2 + 1) / A ^ 0 % A = init
          ∧ p.1 + p.2 + 1 < t)
      = (Finset.range t ×ˢ Finset.range t).filter (fun p => p.1 + p.2 + 1 = H) from
    Finset.filter_congr (fun p _ => by rw [hpred p])]
  exact card_pairs_succ_sum t H (Nat.le_of_lt hHt)

end GebLean.EraRecurrence
