import GebLean.LawvereER
import GebLean.Utilities.EraBoundedSum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Search-free closed forms for number-theoretic functions

`ℕ`-level closed-form identities supporting the Era bounded-sum engine
(`GebLean/EraCompleteness.lean`): the slow `2`-adic valuation, the
central binomial coefficient, the binary Hamming weight, and the
digit-block indicator, each equated to a Mathlib reference function.

## Main definitions

* `nu2Closed` — the slow, log-free `2`-adic valuation closed form.
* `centralBinomClosed` — the central binomial coefficient as a
  base-`2^(2n)` digit read-off of `(1 + 2^(2n))^(2n)`.
* `hwClosed` — the binary Hamming weight as `ν₂(C(2n,n))` (Kummer).
* `deltaBlock` — the digit-block indicator `δ a w = (2^w - 1)(2^w - a + 1)`.
* `solCount` — the number of `(x, y) ∈ ℕ²` with `a·x + b·y = n`.

## Main statements

* `nu2Closed_eq` — `nu2Closed n = padicValNat 2 n` for `n ≥ 1`.
* `centralBinomClosed_eq` — `centralBinomClosed n = Nat.centralBinom n`
  for `n ≥ 1`.
* `hwClosed_eq` — `hwClosed n = (Nat.digits 2 n).sum` for `n ≥ 1`.
* `hwClosed_deltaBlock` — `HW(δ a w) = 2w` if `a = 0`, else `w`, for
  `a < 2^w`.
* `solCount_le_succ` — `solCount a b n ≤ n + 1` for `1 ≤ a, 1 ≤ b`.
* `solCount_mul_eq_gcd_succ` — `solCount a b (a * b) = gcd a b + 1` for
  `1 ≤ a, 1 ≤ b` (the Prunescu–Shunia gcd linear-Diophantine count).

## References

* Prunescu, Sauras-Altuzarra, arXiv:2407.12928 (the method; `ν_p`
  Theorem 2.1).

## Tags

elementary recursive, closed form, p-adic valuation
-/

namespace GebLean

/-- The slow (log-free) `2`-adic valuation closed form
(arXiv:2407.12928, Theorem 2.1). `Nat.gcd n (2^n) = 2^(v₂ n)`, so the
binomial-mod read-off recovers `v₂ n`. Realised as an `Era` term later;
not numerically evaluable on large inputs, but its `eval` lemma is
proved, not computed. -/
def nu2Closed (n : ℕ) : ℕ :=
  let base := 2 ^ (n + 1) - 1
  (Nat.gcd n (2 ^ n) ^ (n + 1) % base ^ 2) / base

private theorem gcd_pow_eq (n : ℕ) (hn : 1 ≤ n) :
    Nat.gcd n (2 ^ n) = 2 ^ padicValNat 2 n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  set x := padicValNat 2 n with hx
  have hxn : x ≤ n := by
    have := padicValNat_le_nat_log (p := 2) n
    exact this.trans (Nat.log_le_self 2 n)
  apply Nat.dvd_antisymm
  · -- gcd ∣ 2^x : gcd ∣ n and gcd ∣ 2^n, so gcd = 2^k, and k ≤ x
    obtain ⟨k, hk, hgcd⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right n (2 ^ n))
    rw [hgcd]
    have hdn : (2 : ℕ) ^ k ∣ n := hgcd ▸ Nat.gcd_dvd_left n (2 ^ n)
    have hkx : k ≤ x := (padicValNat_dvd_iff_le hn0).mp hdn
    exact pow_dvd_pow 2 hkx
  · -- 2^x ∣ gcd : 2^x ∣ n and 2^x ∣ 2^n
    apply Nat.dvd_gcd
    · exact pow_padicValNat_dvd
    · exact pow_dvd_pow 2 hxn

private theorem pow_succ_mod_sq (a x : ℕ) :
    (a + 1) ^ x % a ^ 2 = (1 + x * a) % a ^ 2 := by
  induction x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih, ← Nat.mul_mod]
    have hexp : (1 + k * a) * (a + 1) = 1 + (k + 1) * a + k * a ^ 2 := by ring
    rw [hexp, Nat.add_mul_mod_self_right]

/-- The slow `ν₂` closed form computes the `2`-adic valuation: for
`n ≥ 1`, `nu2Closed n = padicValNat 2 n`. -/
theorem nu2Closed_eq (n : ℕ) (hn : 1 ≤ n) :
    nu2Closed n = padicValNat 2 n := by
  set x := padicValNat 2 n with hx
  set base := 2 ^ (n + 1) - 1 with hbase
  have hxn : x ≤ n := by
    have := padicValNat_le_nat_log (p := 2) n
    exact this.trans (Nat.log_le_self 2 n)
  -- `2 ^ (n + 1) = base + 1`
  have hpow1 : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hbb : base + 1 = 2 ^ (n + 1) := by omega
  -- rewrite the gcd power as `(base + 1) ^ x`
  have hgcd : Nat.gcd n (2 ^ n) ^ (n + 1) = (base + 1) ^ x := by
    rw [gcd_pow_eq n hn, ← pow_mul, Nat.mul_comm, pow_mul, hbb]
  -- numeric bounds on `base`
  have hbase2 : 2 ≤ n + 1 := by omega
  have hbge : 2 ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) hbase2
  have hbase3 : 3 ≤ base := by omega
  -- `x < base` (since `x ≤ n < 2 ^ (n + 1) - 1 = base`)
  have hnlt : n < 2 ^ (n + 1) - 1 := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
    have h3 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hxb : x < base := lt_of_le_of_lt hxn hnlt
  -- `1 + x * base < base ^ 2`
  have hlt : 1 + x * base < base ^ 2 := by
    have : x * base + base ≤ base * base := by
      have := Nat.mul_le_mul_right base (Nat.succ_le_of_lt hxb)
      simpa [Nat.succ_mul, Nat.mul_comm] using this
    have hsq : base ^ 2 = base * base := by ring
    omega
  -- assemble
  unfold nu2Closed
  simp only [← hbase]
  rw [hgcd, pow_succ_mod_sq, Nat.mod_eq_of_lt hlt]
  rw [Nat.add_mul_div_right _ _ (by omega : 0 < base)]
  have h1div : (1 : ℕ) / base = 0 := Nat.div_eq_of_lt (by omega)
  omega

private theorem ofDigits_ofFn (b : ℕ) (m : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits b (List.ofFn (fun i : Fin m => f i)) =
      ∑ i ∈ Finset.range m, f i * b ^ i := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, Nat.ofDigits_append]
    simp only [Fin.val_castSucc, List.length_ofFn]
    rw [ih, Finset.sum_range_succ]
    simp [Nat.ofDigits_singleton, Fin.last, Nat.mul_comm]

private theorem choose_two_mul_lt (n j : ℕ) (hn : 1 ≤ n) :
    (2 * n).choose j < 2 ^ (2 * n) := by
  have hk : 2 * n = (2 * n - 1) + 1 := by omega
  have hle : (2 * n).choose j ≤ 2 ^ (2 * n - 1) := by
    rw [hk]; exact Nat.choose_succ_le_two_pow (2 * n - 1) j
  have hlt : 2 ^ (2 * n - 1) < 2 ^ (2 * n) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact lt_of_le_of_lt hle hlt

/-- `C(2n,n)` as the arithmetic-term closed form
`⌊(1+2^(2n))^(2n) / 2^(2n²)⌋ mod 2^(2n)` (arXiv:2407.12928). Agrees with
`Nat.centralBinom` for `n ≥ 1`; degenerates to `0` at `n = 0`
(`Nat.centralBinom 0 = 1`), handled separately. -/
def centralBinomClosed (n : ℕ) : ℕ :=
  ((1 + 2 ^ (2 * n)) ^ (2 * n) / 2 ^ (2 * n ^ 2)) % 2 ^ (2 * n)

/-- The central-binomial closed form computes `Nat.centralBinom`: for
`n ≥ 1`, `centralBinomClosed n = Nat.centralBinom n`. -/
theorem centralBinomClosed_eq (n : ℕ) (hn : 1 ≤ n) :
    centralBinomClosed n = Nat.centralBinom n := by
  set b := 2 ^ (2 * n) with hb
  set L := List.ofFn (fun j : Fin (2 * n + 1) => (2 * n).choose j) with hL
  have hbpos : 0 < b := by rw [hb]; positivity
  -- digits are all `< b`
  have hdig : ∀ l ∈ L, l < b := by
    intro l hmem
    rw [hL, List.mem_ofFn] at hmem
    obtain ⟨j, rfl⟩ := hmem
    exact choose_two_mul_lt n j hn
  -- expansion: `(1 + b) ^ (2n) = ofDigits b L`
  have hexp : (1 + b) ^ (2 * n) = Nat.ofDigits b L := by
    rw [hL, ofDigits_ofFn, add_comm 1 b, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, mul_one, Nat.cast_id, Nat.mul_comm]
  -- `2 ^ (2 n²) = b ^ n`
  have hpow : (2 : ℕ) ^ (2 * n ^ 2) = b ^ n := by
    rw [hb, ← pow_mul]; ring_nf
  rw [Nat.centralBinom_eq_two_mul_choose, centralBinomClosed, ← hb, hexp, hpow,
    Nat.ofDigits_div_pow_eq_ofDigits_drop n hbpos L hdig,
    Nat.ofDigits_mod_eq_head!]
  -- the leading digit of `drop n L` is `C(2n, n)`
  have hgE : L[n]? = some ((2 * n).choose n) := by
    rw [hL, List.getElem?_ofFn, dif_pos (by omega)]
  have hhead : (List.drop n L).head! = (2 * n).choose n := by
    have h2 := List.head?_drop (l := L) (i := n)
    rw [hgE] at h2
    exact List.head!_of_head? h2
  rw [hhead, Nat.mod_eq_of_lt (choose_two_mul_lt n n hn)]

private theorem sum_digits_two_mul (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · rw [Nat.digits_base_mul (by norm_num) hn]; simp

/-- Kummer's theorem at `p = 2`: the `2`-adic valuation of the central
binomial coefficient equals the binary digit sum,
`ν₂(C(2n,n)) = S₂(n)`. -/
theorem padicValNat_centralBinom_two (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkummer := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := 2) (k := n) (n := 2 * n) (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hkummer
  rw [sum_digits_two_mul] at hkummer
  omega

/-- Binary Hamming weight (digit sum) `σ`, as `ν₂(C(2n,n))` (Kummer),
using the slow log-free `ν₂`. -/
def hwClosed (n : ℕ) : ℕ := nu2Closed (centralBinomClosed n)

/-- The Hamming-weight closed form computes the binary digit sum: for
`n ≥ 1`, `hwClosed n = (Nat.digits 2 n).sum`. -/
theorem hwClosed_eq (n : ℕ) (hn : 1 ≤ n) :
    hwClosed n = (Nat.digits 2 n).sum := by
  rw [hwClosed, centralBinomClosed_eq n hn, nu2Closed_eq _ (Nat.centralBinom_pos n),
    padicValNat_centralBinom_two]

private theorem sum_digits_two_succ (n : ℕ) :
    (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n / 2)).sum := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [Nat.digits_def' (by norm_num) h]; simp

private theorem sum_digits_two_add (w x y : ℕ) (hx : x < 2 ^ w) :
    (Nat.digits 2 (x + 2 ^ w * y)).sum
      = (Nat.digits 2 x).sum + (Nat.digits 2 y).sum := by
  induction w generalizing x with
  | zero => simp_all
  | succ k ih =>
    have hpow : (2 : ℕ) ^ (k + 1) * y = 2 * (2 ^ k * y) := by rw [pow_succ]; ring
    rw [sum_digits_two_succ (x + 2 ^ (k + 1) * y), sum_digits_two_succ x, hpow]
    set t := 2 ^ k * y with ht
    have hmod : (x + 2 * t) % 2 = x % 2 := by omega
    have hdiv : (x + 2 * t) / 2 = x / 2 + t := by omega
    rw [hmod, hdiv]
    have hxd : x / 2 < 2 ^ k := by omega
    rw [ht, ih (x / 2) hxd]
    omega

private theorem sum_digits_two_compl (w m : ℕ) (hm : m < 2 ^ w) :
    (Nat.digits 2 m).sum + (Nat.digits 2 (2 ^ w - 1 - m)).sum = w := by
  induction w generalizing m with
  | zero => interval_cases m; simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hmdiv : m / 2 < 2 ^ k := by omega
    have hc : 2 ^ (k + 1) - 1 - m = 2 * (2 ^ k - 1 - m / 2) + (1 - m % 2) := by
      have := Nat.div_add_mod m 2
      have hk1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    rw [sum_digits_two_succ m, sum_digits_two_succ (2 ^ (k + 1) - 1 - m), hc]
    rw [Nat.mul_add_mod, Nat.mul_add_div (by norm_num)]
    have hmod : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hsub : (1 - m % 2) / 2 = 0 := by omega
    rw [hsub, Nat.add_zero]
    have := ih (m / 2) hmdiv
    omega

/-- The digit-block indicator (arXiv:2407.12928, Lemma 3.1):
`δ a w = (2^w - 1)(2^w - a + 1)`. -/
def deltaBlock (a w : ℕ) : ℕ := (2 ^ w - 1) * (2 ^ w - a + 1)

/-- `HW(δ a w) = 2w` when `a = 0`, else `w`, for `0 ≤ a < 2^w`. -/
theorem hwClosed_deltaBlock {a w : ℕ} (ha : a < 2 ^ w) :
    hwClosed (deltaBlock a w) = if a = 0 then 2 * w else w := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · -- `w = 0` forces `a = 0` and `deltaBlock = 0`
    subst hw
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    rfl
  · have hbig : (2 : ℕ) ^ w ≥ 2 := by
      calc (2 : ℕ) ^ w ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hw
        _ = 2 := by norm_num
    by_cases ha0 : a = 0
    · -- high-bit-only block: `δ 0 w = 2^(2w) - 1`, digit sum `2w`
      subst ha0
      have hd : deltaBlock 0 w = 2 ^ (2 * w) - 1 := by
        have hpow : (2 : ℕ) ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
        unfold deltaBlock
        rw [Nat.sub_zero, hpow, Nat.sub_one_mul, Nat.mul_add, Nat.mul_one]
        omega
      have h1d : 1 ≤ deltaBlock 0 w := by
        rw [hd]
        have : (2 : ℕ) ^ (2 * w) ≥ 2 := by
          calc (2 : ℕ) ^ (2 * w) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 2 := by norm_num
        omega
      rw [hwClosed_eq _ h1d, hd]
      have hcompl := sum_digits_two_compl (2 * w) 0 (by positivity)
      simp only [Nat.digits_zero, List.sum_nil, Nat.sub_zero, Nat.zero_add] at hcompl
      rw [hcompl, if_pos rfl]
    · -- two-block: `δ a w = (a-1) + 2^w * (2^w - a)`, digit sum `w`
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have hd : deltaBlock a w = (a - 1) + 2 ^ w * (2 ^ w - a) := by
        have hmul : (2 : ℕ) ^ w * (2 ^ w - a + 1) = 2 ^ w * (2 ^ w - a) + 2 ^ w := by
          rw [Nat.mul_add, Nat.mul_one]
        unfold deltaBlock
        rw [Nat.sub_one_mul, hmul]
        omega
      have hlow : a - 1 < 2 ^ w := by omega
      have h1d : 1 ≤ deltaBlock a w := by
        rw [hd]
        have hpos : 1 ≤ 2 ^ w - a := by omega
        have : 2 ^ w ≤ 2 ^ w * (2 ^ w - a) := Nat.le_mul_of_pos_right _ hpos
        omega
      rw [hwClosed_eq _ h1d, hd, sum_digits_two_add w (a - 1) (2 ^ w - a) hlow]
      have hcompl := sum_digits_two_compl w (a - 1) hlow
      have hcomp_eq : 2 ^ w - a = 2 ^ w - 1 - (a - 1) := by omega
      rw [hcomp_eq, hcompl, if_neg ha0]

/-- The number of `(x, y) ∈ ℕ²` with `a·x + b·y = n`. Finite for
`1 ≤ a, 1 ≤ b` (every solution lies in the `(n+1)×(n+1)` box). -/
def solCount (a b n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => a * p.1 + b * p.2 = n)).card

private theorem mem_solCount_box (a b n x y : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * x + b * y = n) : x < n + 1 ∧ y < n + 1 := by
  have hx : x ≤ a * x := Nat.le_mul_of_pos_left x ha
  have hy : y ≤ b * y := Nat.le_mul_of_pos_left y hb
  omega

/-- For `1 ≤ a, 1 ≤ b`, the solution count of `a·x + b·y = n` is at most
`n + 1`: the map `(x, y) ↦ (a·x, b·y)` injects the solutions into
`Finset.antidiagonal n`. Equality holds at `a = b = 1`. -/
theorem solCount_le_succ (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b n ≤ n + 1 := by
  rw [solCount, ← Finset.Nat.card_antidiagonal n]
  apply Finset.card_le_card_of_injOn (fun p => (a * p.1, b * p.2))
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
    simp only [Finset.mem_coe, Finset.mem_antidiagonal]
    exact hp.2
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_product, Finset.mem_range] at hp hq
    simp only [Prod.mk.injEq] at hpq
    have h1 : p.1 = q.1 := Nat.eq_of_mul_eq_mul_left ha hpq.1
    have h2 : p.2 = q.2 := Nat.eq_of_mul_eq_mul_left hb hpq.2
    exact Prod.ext h1 h2

/-- The Prunescu–Shunia gcd linear-Diophantine count: for `1 ≤ a, 1 ≤ b`,
the number of `(x, y) ∈ ℕ²` with `a·x + b·y = a·b` equals
`gcd a b + 1`. With `d = gcd a b`, the solutions are exactly
`(b - (b/d)·t, (a/d)·t)` for `t = 0, …, d`. -/
theorem solCount_mul_eq_gcd_succ (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b (a * b) = Nat.gcd a b + 1 := by
  set d := Nat.gcd a b with hd
  have hdpos : 1 ≤ d := Nat.gcd_pos_of_pos_left b ha
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  set a' := a / d with ha'
  set b' := b / d with hb'
  have hada : d * a' = a := Nat.mul_div_cancel' hda
  have hbdb : d * b' = b := Nat.mul_div_cancel' hdb
  have ha'pos : 1 ≤ a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h, Nat.mul_zero] at hada; omega
    · exact h
  have hb'pos : 1 ≤ b' := by
    rcases Nat.eq_zero_or_pos b' with h | h
    · rw [h, Nat.mul_zero] at hbdb; omega
    · exact h
  -- a * b' = a' * b = a*b / d
  have hcross : a * b' = b * a' := by
    rw [← hada, ← hbdb]; ring
  -- key equation: for t ≤ d, the forward map lands in the solution set
  have hbt : ∀ t : ℕ, t ≤ d → b' * t ≤ b := by
    intro t ht
    have : b' * t ≤ b' * d := Nat.mul_le_mul_left b' ht
    rw [Nat.mul_comm b' d, hbdb] at this; exact this
  have hsol : ∀ t : ℕ, t ≤ d →
      a * (b - b' * t) + b * (a' * t) = a * b := by
    intro t ht
    have hle := hbt t ht
    have h1 : a * (b - b' * t) = a * b - a * (b' * t) := Nat.mul_sub a b (b' * t)
    have h2 : a * (b' * t) = b * (a' * t) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, hcross]
    have h3 : a * (b' * t) ≤ a * b := Nat.mul_le_mul_left a hle
    omega
  have hcop : a'.Coprime b' := Nat.coprime_div_gcd_div_gcd (by omega)
  -- characterization: every solution is `(b - b'*t, a'*t)` for some `t ≤ d`
  have hchar : ∀ x y : ℕ, a * x + b * y = a * b →
      a' ∣ y ∧ y / a' ≤ d ∧ x = b - b' * (y / a') ∧ y = a' * (y / a') := by
    intro x y hxy
    -- reduce by d : a'*x + b'*y = a'*b
    have hred : a' * x + b' * y = a' * b := by
      have hmul : d * (a' * x + b' * y) = d * (a' * b) := by
        have e : d * (a' * x + b' * y) = a * x + b * y := by
          rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, hada, hbdb]
        have e2 : d * (a' * b) = a * b := by
          rw [← Nat.mul_assoc, hada]
        rw [e, e2, hxy]
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    -- a' ∣ b'*y, hence a' ∣ y by coprimality
    have hdvd : a' ∣ b' * y := by
      have hsum : a' ∣ a' * x + b' * y := by rw [hred]; exact Dvd.intro b rfl
      exact (Nat.dvd_add_right (Dvd.intro x rfl)).mp hsum
    have hay : a' ∣ y := hcop.dvd_of_dvd_mul_left hdvd
    set t := y / a' with htdef
    have hyt : y = a' * t := (Nat.mul_div_cancel' hay).symm
    -- substitute: a'*x + b'*a'*t = a'*b ⇒ x + b'*t = b
    have hxbt : x + b' * t = b := by
      have hstep : a' * (x + b' * t) = a' * b := by
        rw [Nat.mul_add]
        have hre : b' * y = a' * (b' * t) := by
          rw [hyt]; ring
        rw [hre] at hred; exact hred
      exact Nat.eq_of_mul_eq_mul_left (by omega) hstep
    have htd : t ≤ d := by
      have : b' * t ≤ b := by omega
      have h2 : b' * t ≤ b' * d := by rw [Nat.mul_comm b' d, hbdb]; omega
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    exact ⟨hay, htd, by omega, hyt⟩
  rw [solCount, ← Finset.card_range (d + 1)]
  symm
  apply Finset.card_nbij' (fun t => (b - b' * t, a' * t)) (fun p => p.2 / a')
  · -- MapsTo i : range (d+1) → solutions
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio] at ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_range]
    have heq := hsol t (by omega)
    obtain ⟨hx, hy⟩ := mem_solCount_box a b (a * b) (b - b' * t) (a' * t) ha hb heq
    exact ⟨⟨hx, hy⟩, heq⟩
  · -- MapsTo j : solutions → range (d+1)
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_range] at hp
    simp only [Finset.coe_range, Set.mem_Iio]
    obtain ⟨-, htd, -, -⟩ := hchar p.1 p.2 hp.2
    omega
  · -- left_inv : j (i t) = t for t ∈ range (d+1)
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio] at ht
    simp only [Nat.mul_div_cancel_left t (by omega : 0 < a')]
  · -- right_inv : i (j p) = p for solutions p
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_range] at hp
    obtain ⟨-, -, hx, hy⟩ := hchar p.1 p.2 hp.2
    apply Prod.ext
    · simp only; rw [← hx]
    · simp only; rw [← hy]

/-- Inclusion–exclusion recurrence for the linear-Diophantine count:
for `1 ≤ a, 1 ≤ b` and `a + b ≤ m`,
`solCount a b m + solCount a b (m − a − b)
  = solCount a b (m − a) + solCount a b (m − b)`. The coefficientwise
content of `(1 − tᵃ)(1 − tᵇ)·Σ solCount a b m · tᵐ = 1`. -/
private theorem solCount_recurrence (a b m : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : a + b ≤ m) :
    solCount a b m + solCount a b (m - a - b)
      = solCount a b (m - a) + solCount a b (m - b) := by
  set S := (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun p => a * p.1 + b * p.2 = m) with hS
  set Sx := S.filter (fun p => 1 ≤ p.1) with hSx
  set Sy := S.filter (fun p => 1 ≤ p.2) with hSy
  have hmemS : ∀ p : ℕ × ℕ, p ∈ S ↔
      (p.1 < m + 1 ∧ p.2 < m + 1) ∧ a * p.1 + b * p.2 = m := by
    intro p
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
  have hmemSx : ∀ p : ℕ × ℕ, p ∈ Sx ↔ p ∈ S ∧ 1 ≤ p.1 := by
    intro p; rw [hSx, Finset.mem_filter]
  have hmemSy : ∀ p : ℕ × ℕ, p ∈ Sy ↔ p ∈ S ∧ 1 ≤ p.2 := by
    intro p; rw [hSy, Finset.mem_filter]
  -- `Sx ∪ Sy = S`: no solution has `x = 0 ∧ y = 0` for `m ≥ a + b > 0`.
  have hunion : Sx ∪ Sy = S := by
    apply Finset.Subset.antisymm
    · intro p hp
      rw [Finset.mem_union, hmemSx, hmemSy] at hp
      rcases hp with h | h
      · exact h.1
      · exact h.1
    · intro p hp
      rw [Finset.mem_union, hmemSx, hmemSy]
      have heq := ((hmemS p).mp hp).2
      rcases Nat.eq_zero_or_pos p.1 with hx0 | hx0
      · rcases Nat.eq_zero_or_pos p.2 with hy0 | hy0
        · exfalso; rw [hx0, hy0] at heq; omega
        · exact Or.inr ⟨hp, hy0⟩
      · exact Or.inl ⟨hp, hx0⟩
  -- card identity from `card_union_add_card_inter`.
  have hincl : S.card + (Sx ∩ Sy).card = Sx.card + Sy.card := by
    rw [← hunion]; exact Finset.card_union_add_card_inter Sx Sy
  -- `card Sx = solCount a b (m - a)`.
  have hSxcard : Sx.card = solCount a b (m - a) := by
    rw [solCount]
    apply Finset.card_nbij' (fun p => (p.1 - 1, p.2)) (fun p => (p.1 + 1, p.2))
    · intro p hp
      simp only [Finset.mem_coe, hmemSx, hmemS] at hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      obtain ⟨⟨-, heq⟩, hx1⟩ := hp
      have hax : a ≤ a * p.1 := Nat.le_mul_of_pos_right a hx1
      have heq' : a * (p.1 - 1) + b * p.2 = m - a := by
        have : a * (p.1 - 1) = a * p.1 - a := by rw [Nat.mul_sub, Nat.mul_one]
        omega
      exact ⟨mem_solCount_box a b (m - a) (p.1 - 1) p.2 ha hb heq', heq'⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Finset.mem_coe, hmemSx, hmemS]
      obtain ⟨-, heq⟩ := hp
      have heq' : a * (p.1 + 1) + b * p.2 = m := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact ⟨⟨mem_solCount_box a b m (p.1 + 1) p.2 ha hb heq', heq'⟩, by omega⟩
    · intro p hp
      simp only [Finset.mem_coe, hmemSx, hmemS] at hp
      obtain ⟨-, hx1⟩ := hp
      apply Prod.ext
      · simp only; omega
      · simp only
    · intro p _
      apply Prod.ext
      · simp only; omega
      · simp only
  -- `card Sy = solCount a b (m - b)`.
  have hSycard : Sy.card = solCount a b (m - b) := by
    rw [solCount]
    apply Finset.card_nbij' (fun p => (p.1, p.2 - 1)) (fun p => (p.1, p.2 + 1))
    · intro p hp
      simp only [Finset.mem_coe, hmemSy, hmemS] at hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      obtain ⟨⟨-, heq⟩, hy1⟩ := hp
      have hby : b ≤ b * p.2 := Nat.le_mul_of_pos_right b hy1
      have heq' : a * p.1 + b * (p.2 - 1) = m - b := by
        have : b * (p.2 - 1) = b * p.2 - b := by rw [Nat.mul_sub, Nat.mul_one]
        omega
      exact ⟨mem_solCount_box a b (m - b) p.1 (p.2 - 1) ha hb heq', heq'⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Finset.mem_coe, hmemSy, hmemS]
      obtain ⟨-, heq⟩ := hp
      have heq' : a * p.1 + b * (p.2 + 1) = m := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact ⟨⟨mem_solCount_box a b m p.1 (p.2 + 1) ha hb heq', heq'⟩, by omega⟩
    · intro p hp
      simp only [Finset.mem_coe, hmemSy, hmemS] at hp
      obtain ⟨-, hy1⟩ := hp
      apply Prod.ext
      · simp only
      · simp only; omega
    · intro p _
      apply Prod.ext
      · simp only
      · simp only; omega
  -- `card (Sx ∩ Sy) = solCount a b (m - a - b)`.
  have hmemInter : ∀ p : ℕ × ℕ, p ∈ Sx ∩ Sy ↔
      ((p.1 < m + 1 ∧ p.2 < m + 1) ∧ a * p.1 + b * p.2 = m)
        ∧ 1 ≤ p.1 ∧ 1 ≤ p.2 := by
    intro p
    rw [Finset.mem_inter, hmemSx, hmemSy, hmemS]
    tauto
  have hintercard : (Sx ∩ Sy).card = solCount a b (m - a - b) := by
    rw [solCount]
    apply Finset.card_nbij' (fun p => (p.1 - 1, p.2 - 1))
      (fun p => (p.1 + 1, p.2 + 1))
    · intro p hp
      simp only [Finset.mem_coe, hmemInter] at hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      obtain ⟨⟨-, heq⟩, hx1, hy1⟩ := hp
      have hax0 : a ≤ a * p.1 := Nat.le_mul_of_pos_right a hx1
      have hby0 : b ≤ b * p.2 := Nat.le_mul_of_pos_right b hy1
      have heq' : a * (p.1 - 1) + b * (p.2 - 1) = m - a - b := by
        have hax : a * (p.1 - 1) = a * p.1 - a := by rw [Nat.mul_sub, Nat.mul_one]
        have hby : b * (p.2 - 1) = b * p.2 - b := by rw [Nat.mul_sub, Nat.mul_one]
        omega
      exact ⟨mem_solCount_box a b (m - a - b) (p.1 - 1) (p.2 - 1) ha hb heq', heq'⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp
      simp only [Finset.mem_coe, hmemInter]
      obtain ⟨-, heq⟩ := hp
      have heq' : a * (p.1 + 1) + b * (p.2 + 1) = m := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]; omega
      exact ⟨⟨mem_solCount_box a b m (p.1 + 1) (p.2 + 1) ha hb heq', heq'⟩,
        by omega, by omega⟩
    · intro p hp
      simp only [Finset.mem_coe, hmemInter] at hp
      obtain ⟨-, hx1, hy1⟩ := hp
      apply Prod.ext
      · simp only; omega
      · simp only; omega
    · intro p _
      apply Prod.ext
      · simp only; omega
      · simp only; omega
  have hScard : S.card = solCount a b m := by rw [hS, solCount]
  rw [hSxcard, hSycard, hintercard, hScard] at hincl
  exact hincl

/-- Base-`5^(a·b)` digit sum encoding the linear-Diophantine counts:
`S = Σ_{k=0}^{a·b} solCount a b (a·b − k) · (5^(a·b))^k`. Equals
`⌊5^(a·b·(a·b+a+b)) / ((5^(a²·b)−1)(5^(a·b²)−1))⌋` (proved later). -/
private def gcdDigitSum (a b : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (a * b + 1),
    solCount a b (a * b - k) * (5 ^ (a * b)) ^ k

/-- Each digit `solCount a b (a*b)` is strictly less than the base `5^(a*b)`,
so digits do not overflow into adjacent positions in `gcdDigitSum`. -/
private theorem solCount_mul_lt_base (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    solCount a b (a * b) < 5 ^ (a * b) := by
  have h1 : solCount a b (a * b) ≤ a * b + 1 := solCount_le_succ a b (a * b) ha hb
  have h2 : a * b < 2 ^ (a * b) := Nat.lt_two_pow_self
  have h3 : a * b ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h4 : (2 : ℕ) ^ (a * b) < 5 ^ (a * b) :=
    Nat.pow_lt_pow_left (by norm_num) h3
  omega

/-- The least-significant digit of `gcdDigitSum a b` in base `5^(a*b)` equals
`solCount a b (a*b)`: every higher-indexed term is divisible by `5^(a*b)`. -/
private theorem gcdDigitSum_mod (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdDigitSum a b % 5 ^ (a * b) = solCount a b (a * b) := by
  simp only [gcdDigitSum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  have hfactor : ∑ k ∈ Finset.range (a * b),
      solCount a b (a * b - (k + 1)) * (5 ^ (a * b)) ^ (k + 1) =
      5 ^ (a * b) * ∑ k ∈ Finset.range (a * b),
      solCount a b (a * b - (k + 1)) * (5 ^ (a * b)) ^ k := by
    rw [Finset.mul_sum]
    congr 1; ext k; rw [pow_succ']; ring
  rw [hfactor, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (solCount_mul_lt_base a b ha hb)

/-- Closed-form numerator exponent in base `5^(a·b)`:
`5^(a·b·(a·b+a+b)) = (5^(a·b))^(a·b+a+b)`. -/
private theorem gcd_num_pow (a b : ℕ) :
    5 ^ (a * b * (a * b + a + b)) = (5 ^ (a * b)) ^ (a * b + a + b) := by
  rw [← pow_mul]

/-- First denominator factor exponent in base `5^(a·b)`:
`5^(a²·b) = (5^(a·b))^a`. -/
private theorem gcd_dena_pow (a b : ℕ) :
    5 ^ (a ^ 2 * b) = (5 ^ (a * b)) ^ a := by
  rw [← pow_mul]; congr 1; ring

/-- Second denominator factor exponent in base `5^(a·b)`:
`5^(a·b²) = (5^(a·b))^b`. -/
private theorem gcd_denb_pow (a b : ℕ) :
    5 ^ (a * b ^ 2) = (5 ^ (a * b)) ^ b := by
  rw [← pow_mul]; congr 1; ring

/-- The base-`5^(a·b)` comb `P = 5^((a·b+a+b) mod a) · Σ_{i<(a·b+a+b)/a} (5^(a·b))^(a·i)`,
the exact quotient `⌊5^(a·b·(a·b+a+b)) / (5^(a²·b)−1)⌋` written in base `5^(a·b)`. -/
private def gcdPComb (a b : ℕ) : ℕ :=
  (5 ^ (a * b)) ^ ((a * b + a + b) % a) *
    ∑ i ∈ Finset.range ((a * b + a + b) / a), (5 ^ (a * b)) ^ (a * i)

/-- Two-step division identity: `(5^(a·b))^(a·b+a+b) = ((5^(a·b))^a − 1) · P + (5^(a·b))^r`,
where `P = gcdPComb a b` and `r = (a·b+a+b) % a`. -/
private theorem gcd_num_split (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 ^ (a * b)) ^ (a * b + a + b)
      = ((5 ^ (a * b)) ^ a - 1) * gcdPComb a b
          + (5 ^ (a * b)) ^ ((a * b + a + b) % a) := by
  simp only [gcdPComb]
  -- Set B := 5^(a*b), E := a*b+a+b, q := E/a, r := E%a
  set B := 5 ^ (a * b) with hBdef
  set E := a * b + a + b with hEdef
  set q := E / a with hqdef
  set r := E % a with hrdef
  -- r + a * q = E
  have hEqr : r + a * q = E := by
    have hdm : a * q + r = E := by
      rw [hqdef, hrdef, hEdef]; exact Nat.div_add_mod (a * b + a + b) a
    linarith
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hBa : 1 ≤ B ^ a := Nat.one_le_pow _ _ hB1
  have hBaq_ge : 1 ≤ (B ^ a) ^ q := Nat.one_le_pow _ _ hBa
  -- Rewrite summands: B^(a*i) = (B^a)^i
  have hstep : ∀ i : ℕ, B ^ (a * i) = (B ^ a) ^ i := fun i => pow_mul B a i
  simp_rw [hstep]
  -- (B^a - 1) * ∑ i<q, (B^a)^i = (B^a)^q - 1
  have hprod : (B ^ a - 1) * ∑ i ∈ Finset.range q, (B ^ a) ^ i = (B ^ a) ^ q - 1 := by
    have hg := natGeomSum_mul (B ^ a) q hBa
    linarith [Nat.mul_comm (∑ i ∈ Finset.range q, (B ^ a) ^ i) (B ^ a - 1)]
  -- Rewrite lhs: B^E = B^(r + a*q) = B^r * (B^a)^q
  conv_lhs => rw [← hEqr, pow_add, pow_mul]
  -- Goal: B^r * (B^a)^q = (B^a-1)*(B^r * ∑ i<q, (B^a)^i) + B^r
  -- Simplify rhs: (B^a-1)*(B^r*S) = B^r*((B^a-1)*S) = B^r*((B^a)^q - 1)
  rw [show (B ^ a - 1) * (B ^ r * ∑ i ∈ Finset.range q, (B ^ a) ^ i) =
      B ^ r * ((B ^ a) ^ q - 1) from by
    rw [← Nat.mul_assoc, Nat.mul_comm (B ^ a - 1) (B ^ r), Nat.mul_assoc, hprod]]
  -- Goal: B^r * (B^a)^q = B^r * ((B^a)^q - 1) + B^r
  nth_rw 1 [← Nat.sub_add_cancel (Nat.le_mul_of_pos_right (B ^ r)
    (by linarith [hBaq_ge] : 0 < (B ^ a) ^ q)), Nat.mul_sub_one]

/-- The remainder is strictly less than the denominator factor:
`(5^(a·b))^((a·b+a+b) % a) < (5^(a·b))^a − 1`. -/
private theorem gcd_rem_lt_dena (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (5 ^ (a * b)) ^ ((a * b + a + b) % a) < (5 ^ (a * b)) ^ a - 1 := by
  set B := 5 ^ (a * b) with hBdef
  set r := (a * b + a + b) % a with hrdef
  have hr : r < a := Nat.mod_lt _ (by omega)
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  -- B ≥ 5 since a*b ≥ 1 (a,b ≥ 1)
  have hB5 : 5 ≤ B := by
    rw [hBdef]
    calc (5 : ℕ) = 5 ^ 1 := (pow_one 5).symm
      _ ≤ 5 ^ (a * b) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  -- B^r ≤ B^(a-1) since r ≤ a-1
  have hBr_le : B ^ r ≤ B ^ (a - 1) := Nat.pow_le_pow_right hB1 (by omega)
  -- B^(a-1) ≥ 1
  have hBa1 : 1 ≤ B ^ (a - 1) := Nat.one_le_pow _ _ hB1
  -- B^a = B^(a-1) * B (since a = (a-1)+1)
  have hBa_eq : B ^ a = B ^ (a - 1) * B := by
    conv_lhs => rw [show a = a - 1 + 1 by omega]
    rw [pow_succ]
  -- B^(a-1) < B^a - 1
  have hBa1_lt : B ^ (a - 1) < B ^ a - 1 := by
    rw [hBa_eq]
    have h5 : B ^ (a - 1) * 5 ≤ B ^ (a - 1) * B := Nat.mul_le_mul_left _ hB5
    have hge : 1 ≤ B ^ (a - 1) * B := Nat.le_trans hBa1 (Nat.le_mul_of_pos_right _ (by linarith))
    omega
  linarith

end GebLean
