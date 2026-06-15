import GebLean.LawvereER
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

## Main statements

* `nu2Closed_eq` — `nu2Closed n = padicValNat 2 n` for `n ≥ 1`.
* `centralBinomClosed_eq` — `centralBinomClosed n = Nat.centralBinom n`
  for `n ≥ 1`.

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

end GebLean
