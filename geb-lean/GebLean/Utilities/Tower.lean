import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Tower of Twos

Iterated exponential `tower k x` applies `fun n => 2 ^ n` to `x` a
total of `k` times.  Used as a bounding function for the elementary
recursive functions: every ER term's interpretation is dominated by a
fixed-height tower applied to the context's maximum (plus a padding
constant).
-/

namespace GebLean

/-- `tower k x` is a tower of `k` twos applied to `x`:
`tower 0 x = x` and `tower (k+1) x = 2 ^ tower k x`. -/
def tower : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => 2 ^ tower k x

@[simp] theorem tower_zero (x : ℕ) : tower 0 x = x := rfl

@[simp] theorem tower_succ (k x : ℕ) :
    tower (k + 1) x = 2 ^ tower k x := rfl

/-- `x ≤ tower k x` for all `k`, `x`. -/
theorem self_le_tower (k x : ℕ) : x ≤ tower k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    calc x ≤ tower k x := ih
      _ ≤ 2 ^ tower k x := by
        have h : tower k x < 2 ^ tower k x :=
          Nat.lt_two_pow_self
        exact le_of_lt h

/-- `1 ≤ tower k x` whenever `1 ≤ x`. -/
theorem one_le_tower_of_one_le (k x : ℕ) (hx : 1 ≤ x) :
    1 ≤ tower k x := le_trans hx (self_le_tower k x)

/-- `tower k` is monotone in its second argument. -/
theorem tower_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) :
    tower k x ≤ tower k y := by
  induction k with
  | zero => exact h
  | succ k ih =>
    exact Nat.pow_le_pow_right (by omega) ih

/-- `tower k` is strictly monotone in its second argument: `x < y` gives
`tower k x < tower k y`. The name avoids a misparse against `tower_succ`, whose
successor is the height argument; consumers read this lemma at `y = x + 1`. -/
theorem tower_lt_tower_right (k : ℕ) {x y : ℕ} (h : x < y) :
    tower k x < tower k y := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.pow_lt_pow_right Nat.one_lt_two ih

/-- Composition of towers: applying a height-`j` tower to a
height-`k` tower of `x` equals applying a height-`j+k` tower to `x`. -/
theorem tower_comp (j k x : ℕ) :
    tower j (tower k x) = tower (j + k) x := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    rw [Nat.succ_add]
    change 2 ^ tower j (tower k x) = 2 ^ tower (j + k) x
    rw [ih]

/-- `n ≤ 2 ^ n` for all `n`. -/
theorem le_two_pow_self (n : ℕ) : n ≤ 2 ^ n :=
  Nat.le_of_lt Nat.lt_two_pow_self

/-- `tower` is monotone in its first argument. -/
theorem tower_mono_left {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (x : ℕ) :
    tower k₁ x ≤ tower k₂ x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    exact le_trans ih (le_two_pow_self _)

/-- `2 ^ n ≤ tower n 1`: a height-`n` tower of twos dominates a
single exponential of `n`. -/
theorem two_pow_le_tower_one (n : ℕ) : 2 ^ n ≤ tower n 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 ^ (n + 1) ≤ 2 ^ tower n 1
    have hle : n + 1 ≤ tower n 1 := by
      calc n + 1 ≤ 2 ^ n := by
            have h := Nat.lt_two_pow_self (n := n)
            omega
        _ ≤ tower n 1 := ih
    exact Nat.pow_le_pow_right (by omega) hle

/-- `2 * n ≤ 2 ^ n` for `n ≥ 2`. -/
theorem two_mul_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have hstep : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
      rw [Nat.pow_succ]; omega
    calc 2 * (n + 1)
        = 2 * n + 2 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := hstep

/-- Multiplicative bound: `m * tower k m ≤ tower (k + 2) m` for `m ≥ 2`. -/
theorem mul_tower_le_tower_add_two {k m : ℕ} (hm : 2 ≤ m) :
    m * tower k m ≤ tower (k + 2) m := by
  have h_self : m ≤ tower k m := self_le_tower k m
  have h_tower_ge : 2 ≤ tower k m := le_trans hm h_self
  change m * tower k m ≤ 2 ^ (2 ^ tower k m)
  calc m * tower k m
      ≤ 2 ^ m * tower k m :=
        Nat.mul_le_mul_right _ (le_two_pow_self m)
    _ ≤ 2 ^ m * 2 ^ tower k m :=
        Nat.mul_le_mul_left _ (le_two_pow_self (tower k m))
    _ = 2 ^ (m + tower k m) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ (2 * tower k m) := by
        apply Nat.pow_le_pow_right (by omega)
        omega
    _ ≤ 2 ^ (2 ^ tower k m) :=
        Nat.pow_le_pow_right (by omega) (two_mul_le_two_pow h_tower_ge)

/-- Power bound: `tower k m ^ m ≤ tower (k + 3) m` for `m ≥ 2`. -/
theorem tower_pow_le_tower_add_three {k m : ℕ} (hm : 2 ≤ m) :
    tower k m ^ m ≤ tower (k + 3) m := by
  have h_pow : tower k m ≤ 2 ^ tower k m := le_two_pow_self _
  have h_mul_bound : m * tower k m ≤ tower (k + 2) m :=
    mul_tower_le_tower_add_two hm
  change tower k m ^ m ≤ 2 ^ (tower (k + 2) m)
  calc tower k m ^ m
      ≤ (2 ^ tower k m) ^ m :=
        Nat.pow_le_pow_left h_pow _
    _ = 2 ^ (tower k m * m) := by rw [← Nat.pow_mul]
    _ = 2 ^ (m * tower k m) := by rw [Nat.mul_comm]
    _ ≤ 2 ^ (tower (k + 2) m) :=
        Nat.pow_le_pow_right (by omega) h_mul_bound

end GebLean
