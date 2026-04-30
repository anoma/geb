import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Log
import GebLean.Utilities.Tower
import GebLean.Utilities.SzudzikSeq

/-!
# Computational complexity primitives

Generic natural-number arithmetic supporting polynomial
and tower bounds used in the ER polynomial-bound
infrastructure.  This module references neither
`ERMor1` nor `KMor1`; it depends only on `Nat`,
`Nat.pair`, `Nat.seqPack`, and `tower` from
`Utilities/Tower.lean`.

The principal results are:

- `Nat.pair_le_sq` — quadratic upper bound on Cantor
  pairing.
- `Nat.seqPackBound` and its dominance lemma — closed-
  form polynomial upper bound on `Nat.seqPack`.
- `Nat.tower_succ_pow_bound` and
  `Nat.tower_succ_pow_bound_strong` — polynomial-of-tower
  bounds for the inductive step of polynomial iteration.
- `Nat.polynomial_iter_tower_bound` — iterating a
  polynomially-bounded step `j` times keeps the value
  within a height-2 tower of a linear function in
  `(j, x, Nat.log 2 D, m)`.

See `docs/plans/2026-04-30-er-polynomial-bound-design.md`
(Module A).

A related but distinct concept is course-of-values
recursion (PlanetMath:
`https://planetmath.org/courseofvaluesrecursion`); our
infrastructure does simultaneous primitive recursion
via Hilbert–Bernays reduction with Szudzik pairing,
which is different from course-of-values.
-/

namespace Nat

/-- Quadratic upper bound on mathlib's `Nat.pair`. -/
theorem pair_le_sq (x y : ℕ) :
    Nat.pair x y ≤ (x + y + 1)^2 := by
  unfold Nat.pair
  by_cases h : x < y
  · simp only [h, if_true]
    have hsq : (x + y + 1)^2 = (x + y + 1) * (x + y + 1) := by
      ring
    rw [hsq]
    have h1 : y * y ≤ (x + y) * (x + y) := by
      have hle : y ≤ x + y := Nat.le_add_left _ _
      exact Nat.mul_le_mul hle hle
    have h2 : (x + y) * (x + y) + x ≤ (x + y + 1) * (x + y + 1) := by
      have hexp : (x + y + 1) * (x + y + 1)
          = (x + y) * (x + y) + (x + y) + (x + y) + 1 := by ring
      rw [hexp]
      omega
    omega
  · simp only [h, if_false]
    have hsq : (x + y + 1)^2 = (x + y + 1) * (x + y + 1) := by
      ring
    rw [hsq]
    have h1 : x * x ≤ (x + y) * (x + y) := by
      have hle : x ≤ x + y := Nat.le_add_right _ _
      exact Nat.mul_le_mul hle hle
    have h2 : (x + y) * (x + y) + x + y ≤ (x + y + 1) * (x + y + 1) := by
      have hexp : (x + y + 1) * (x + y + 1)
          = (x + y) * (x + y) + (x + y) + (x + y) + 1 := by ring
      rw [hexp]
      omega
    omega

/-- Closed-form polynomial upper bound on `seqPack` for
a list of length at most `k + 1` with components bounded
by `(m + 1)^d`.  The exponent `(d + 5) * 4^(k + 1)`
absorbs the quadratic blow-up per pairing together with
additive constants picked up by each step.  The base
`(m + 2)` ensures `≥ 2`, which lets the proof handle
`m = 0`. -/
def seqPackBound (k d m : ℕ) : ℕ :=
  (m + 2)^((d + 5) * 4^(k + 1))

private theorem two_le_m_add_two (m : ℕ) : 2 ≤ m + 2 := by
  omega

private theorem m_add_two_pos (m : ℕ) : 0 < m + 2 := by
  omega

private theorem one_le_m_add_two_pow (m e : ℕ) :
    1 ≤ (m + 2)^e :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e (by omega))

private theorem pow_le_pow_right_m_add_two
    {m a b : ℕ} (h : a ≤ b) :
    (m + 2)^a ≤ (m + 2)^b :=
  Nat.pow_le_pow_right (m_add_two_pos m) h

/-- Auxiliary structural-induction bound: `seqPack vs`
fits under `(m + 2)^((d + 5) * 4^vs.length)` when each
component is bounded by `(m + 1)^d`. -/
private theorem seqPack_le_pow_aux
    (vs : List ℕ) (d m : ℕ)
    (h_bounds : ∀ v ∈ vs, v ≤ (m + 1) ^ d) :
    Nat.seqPack vs ≤ (m + 2)^((d + 5) * 4^vs.length) := by
  induction vs with
  | nil =>
      simp only [Nat.seqPack_nil]
      exact Nat.zero_le _
  | cons v vs' ih =>
      have hv : v ≤ (m + 1)^d :=
        h_bounds v List.mem_cons_self
      have h_tail : ∀ w ∈ vs', w ≤ (m + 1)^d := by
        intro w hw
        exact h_bounds w (List.mem_cons_of_mem _ hw)
      have ih' := ih h_tail
      set B := m + 2 with hB
      set En := (d + 5) * 4^vs'.length with hEn
      have hB2 : 2 ≤ B := two_le_m_add_two m
      have hBd : (m + 1)^d ≤ B^d := by
        apply Nat.pow_le_pow_left
        omega
      have hv_le : v ≤ B^d := le_trans hv hBd
      have hB_pow_pos : 1 ≤ B^En := one_le_m_add_two_pow m En
      have hd_le_En : d ≤ En := by
        have h4n : 1 ≤ 4^vs'.length :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        have : d ≤ d + 5 := by omega
        calc d ≤ d + 5 := this
          _ = (d + 5) * 1 := by ring
          _ ≤ (d + 5) * 4^vs'.length :=
              Nat.mul_le_mul_left _ h4n
      have hBd_le : B^d ≤ B^En :=
        pow_le_pow_right_m_add_two hd_le_En
      have hsum_le_3 :
          v + Nat.seqPack vs' + 1 ≤ 3 * B^En := by
        have h1 : v + Nat.seqPack vs' + 1
            ≤ B^d + B^En + 1 := by
          have := Nat.add_le_add hv_le ih'
          omega
        have h2 : B^d + B^En + 1 ≤ 3 * B^En := by
          have ha : B^d ≤ B^En := hBd_le
          have hb : 1 ≤ B^En := hB_pow_pos
          omega
        exact le_trans h1 h2
      have hsq_le :
          (v + Nat.seqPack vs' + 1)^2
            ≤ 9 * B^(2 * En) := by
        have hpow2 : (3 * B^En)^2 = 9 * B^(2 * En) := by
          have hexp : (B^En)^2 = B^(2 * En) := by
            rw [← pow_mul, Nat.mul_comm]
          calc (3 * B^En)^2
              = 9 * (B^En)^2 := by ring
            _ = 9 * B^(2 * En) := by rw [hexp]
        calc (v + Nat.seqPack vs' + 1)^2
            ≤ (3 * B^En)^2 := Nat.pow_le_pow_left hsum_le_3 2
          _ = 9 * B^(2 * En) := hpow2
      have h9_le_B4 : 9 ≤ B^4 := by
        have : (2 : ℕ)^4 = 16 := by decide
        calc 9 ≤ 16 := by decide
          _ = (2 : ℕ)^4 := by decide
          _ ≤ B^4 := Nat.pow_le_pow_left hB2 4
      have h9pow_le : 9 * B^(2 * En) ≤ B^(2 * En + 4) := by
        calc 9 * B^(2 * En)
            ≤ B^4 * B^(2 * En) :=
              Nat.mul_le_mul_right _ h9_le_B4
          _ = B^(4 + 2 * En) := (pow_add B 4 (2 * En)).symm
          _ = B^(2 * En + 4) := by
              rw [Nat.add_comm 4 (2 * En)]
      have hpair_le :
          Nat.pair v (Nat.seqPack vs')
            ≤ B^(2 * En + 4) := by
        have h1 := Nat.pair_le_sq v (Nat.seqPack vs')
        exact le_trans h1 (le_trans hsq_le h9pow_le)
      have hone_le_B : 1 ≤ B^(2 * En + 4) :=
        one_le_m_add_two_pow m (2 * En + 4)
      have h_pair_plus_1 :
          Nat.pair v (Nat.seqPack vs') + 1
            ≤ 2 * B^(2 * En + 4) := by
        have := hpair_le
        omega
      have h2_le_B : 2 ≤ B := hB2
      have h2_pow_le :
          2 * B^(2 * En + 4)
            ≤ B^(2 * En + 5) := by
        calc 2 * B^(2 * En + 4)
            ≤ B * B^(2 * En + 4) :=
              Nat.mul_le_mul_right _ h2_le_B
          _ = B^(2 * En + 5) := by
              rw [show B * B^(2 * En + 4)
                = B^1 * B^(2 * En + 4) by rw [pow_one],
                ← pow_add]
              congr 1; omega
      have h_target_exp :
          2 * En + 5 ≤ (d + 5) * 4^(vs'.length + 1) := by
        have hEn_def : En = (d + 5) * 4^vs'.length := hEn
        rw [hEn_def]
        have h4 : 4^(vs'.length + 1)
            = 4 * 4^vs'.length := by
          rw [pow_succ]; ring
        rw [h4]
        have h4n_pos : 1 ≤ 4^vs'.length :=
          Nat.one_le_iff_ne_zero.mpr
            (pow_ne_zero _ (by omega))
        have hd5 : 5 ≤ (d + 5) := by omega
        have : 2 * (d + 5) * 4^vs'.length + 5
            ≤ (d + 5) * (4 * 4^vs'.length) := by
          have hexp :
              (d + 5) * (4 * 4^vs'.length)
                = 2 * (d + 5) * 4^vs'.length
                  + 2 * (d + 5) * 4^vs'.length := by
            ring
          rw [hexp]
          have : 5 ≤ 2 * (d + 5) * 4^vs'.length := by
            have h2d5 : 10 ≤ 2 * (d + 5) := by omega
            calc 5 ≤ 10 := by decide
              _ = 10 * 1 := by ring
              _ ≤ 2 * (d + 5) * 4^vs'.length :=
                  Nat.mul_le_mul h2d5 h4n_pos
          omega
        calc 2 * ((d + 5) * 4^vs'.length) + 5
            = 2 * (d + 5) * 4^vs'.length + 5 := by ring
          _ ≤ (d + 5) * (4 * 4^vs'.length) := this
      have h_final_pow :
          B^(2 * En + 5)
            ≤ B^((d + 5) * 4^(vs'.length + 1)) :=
        pow_le_pow_right_m_add_two h_target_exp
      simp only [Nat.seqPack_cons]
      have hlen :
          (v :: vs').length = vs'.length + 1 := rfl
      rw [hlen]
      calc Nat.pair v (Nat.seqPack vs') + 1
          ≤ 2 * B^(2 * En + 4) := h_pair_plus_1
        _ ≤ B^(2 * En + 5) := h2_pow_le
        _ ≤ B^((d + 5) * 4^(vs'.length + 1)) :=
            h_final_pow

/-- `Nat.seqPack` is bounded by `seqPackBound` when the
components are themselves polynomially bounded. -/
theorem seqPack_le_seqPackBound
    (vs : List ℕ) (k d m : ℕ)
    (hlen : vs.length ≤ k + 1)
    (h_bounds : ∀ v ∈ vs, v ≤ (m + 1) ^ d) :
    Nat.seqPack vs ≤ seqPackBound k d m := by
  have h_struct := seqPack_le_pow_aux vs d m h_bounds
  have hexp_le :
      (d + 5) * 4^vs.length ≤ (d + 5) * 4^(k + 1) := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by decide) hlen
  exact le_trans h_struct
    (pow_le_pow_right_m_add_two hexp_le)

private theorem succ_le_two_pow_succ (n : ℕ) :
    n + 1 ≤ 2 ^ (n + 1) := by
  have h := Nat.lt_two_pow_self (n := n + 1)
  omega

private theorem self_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n :=
  GebLean.le_two_pow_self n

private theorem tower_add_le_tower_shift
    (h x D : ℕ) :
    GebLean.tower h x + D + 1
      ≤ GebLean.tower h (x + D + 1) := by
  induction h with
  | zero => simp [GebLean.tower_zero]
  | succ h ih =>
      change 2 ^ GebLean.tower h x + D + 1
        ≤ 2 ^ GebLean.tower h (x + D + 1)
      have hIH := ih
      have hpow_le :
          2 ^ (GebLean.tower h x + D + 1)
            ≤ 2 ^ GebLean.tower h (x + D + 1) :=
        Nat.pow_le_pow_right (by decide) hIH
      have hsplit :
          2 ^ (GebLean.tower h x + D + 1)
            = 2 ^ GebLean.tower h x * 2 ^ (D + 1) := by
        have : GebLean.tower h x + D + 1
            = GebLean.tower h x + (D + 1) := by ring
        rw [this, pow_add]
      have hone_le_pow : 1 ≤ 2 ^ GebLean.tower h x :=
        Nat.one_le_iff_ne_zero.mpr
          (pow_ne_zero _ (by decide))
      have h_d_plus_one : D + 1 ≤ 2 ^ (D + 1) - 1 := by
        have h2 : 2 ^ (D + 1) ≥ D + 2 := by
          have := Nat.lt_two_pow_self (n := D + 1)
          omega
        omega
      have hbound :
          2 ^ GebLean.tower h x + D + 1
            ≤ 2 ^ GebLean.tower h x * 2 ^ (D + 1) := by
        have hk : 2 ^ (D + 1) ≥ 2 := by
          have : (2 : ℕ) ^ 1 = 2 := by decide
          calc (2 : ℕ) = 2 ^ 1 := by decide
            _ ≤ 2 ^ (D + 1) :=
                Nat.pow_le_pow_right (by decide) (by omega)
        have hexpand :
            2 ^ GebLean.tower h x * 2 ^ (D + 1)
              = 2 ^ GebLean.tower h x
                + 2 ^ GebLean.tower h x
                  * (2 ^ (D + 1) - 1) := by
          have h_one_le : 1 ≤ 2 ^ (D + 1) := by
            have := Nat.one_le_iff_ne_zero.mpr
              (pow_ne_zero (D + 1) (by decide : (2 : ℕ) ≠ 0))
            exact this
          have :
              2 ^ GebLean.tower h x * 2 ^ (D + 1)
                = 2 ^ GebLean.tower h x * 1
                  + 2 ^ GebLean.tower h x
                    * (2 ^ (D + 1) - 1) := by
            rw [← Nat.mul_add]
            congr 1
            omega
          rw [this, Nat.mul_one]
        rw [hexpand]
        have hmul_ge :
            2 ^ GebLean.tower h x * (2 ^ (D + 1) - 1)
              ≥ D + 1 := by
          calc D + 1
              ≤ 2 ^ (D + 1) - 1 := h_d_plus_one
            _ = 1 * (2 ^ (D + 1) - 1) := by ring
            _ ≤ 2 ^ GebLean.tower h x
                  * (2 ^ (D + 1) - 1) :=
                Nat.mul_le_mul_right _ hone_le_pow
        omega
      calc 2 ^ GebLean.tower h x + D + 1
          ≤ 2 ^ GebLean.tower h x * 2 ^ (D + 1) := hbound
        _ = 2 ^ (GebLean.tower h x + D + 1) := hsplit.symm
        _ ≤ 2 ^ GebLean.tower h (x + D + 1) := hpow_le

/-- Polynomial-of-tower bound: a polynomial of degree `D`
applied to `tower h x + 1` is dominated by a tower of
height `h + 2` applied to `x + D + 1`.  Used in the
inductive step of `polynomial_iter_tower_two_bound`.

The bound shape uses `tower (h + 2)` and shifts the input
by `D + 1` rather than `Nat.log 2 D + 1`, which gives a
uniform inequality covering the `h = 0` boundary case
(where a tighter logarithmic shift fails). -/
theorem tower_succ_pow_bound (h D x : ℕ) :
    (GebLean.tower h x + 1)^D ≤
      GebLean.tower (h + 2) (x + D + 1) := by
  set T := GebLean.tower h x with hT
  have hT1 : T + 1 ≤ 2 ^ (T + 1) := succ_le_two_pow_succ T
  have hpow_le : (T + 1) ^ D ≤ (2 ^ (T + 1)) ^ D :=
    Nat.pow_le_pow_left hT1 D
  have hpow_eq : (2 ^ (T + 1)) ^ D = 2 ^ ((T + 1) * D) := by
    rw [← pow_mul]
  have hmul_le : (T + 1) * D ≤ 2 ^ (T + 1 + D) := by
    have h_t_le : T + 1 ≤ 2 ^ (T + 1) := hT1
    have h_d_le : D ≤ 2 ^ D := self_le_two_pow_self D
    calc (T + 1) * D
        ≤ 2 ^ (T + 1) * 2 ^ D :=
          Nat.mul_le_mul h_t_le h_d_le
      _ = 2 ^ (T + 1 + D) := by rw [← pow_add]
  have hexp_eq : T + 1 + D = T + D + 1 := by ring
  have hmul_le' : (T + 1) * D ≤ 2 ^ (T + D + 1) := by
    rw [← hexp_eq]; exact hmul_le
  have h_shift :
      T + D + 1 ≤ GebLean.tower h (x + D + 1) :=
    tower_add_le_tower_shift h x D
  have hexp_le_tower :
      2 ^ (T + D + 1) ≤ GebLean.tower (h + 1) (x + D + 1) := by
    change 2 ^ (T + D + 1) ≤ 2 ^ GebLean.tower h (x + D + 1)
    exact Nat.pow_le_pow_right (by decide) h_shift
  have h_outer :
      2 ^ ((T + 1) * D)
        ≤ 2 ^ GebLean.tower (h + 1) (x + D + 1) := by
    have h1 : 2 ^ ((T + 1) * D) ≤ 2 ^ (2 ^ (T + D + 1)) :=
      Nat.pow_le_pow_right (by decide) hmul_le'
    have h2 :
        2 ^ (2 ^ (T + D + 1))
          ≤ 2 ^ GebLean.tower (h + 1) (x + D + 1) :=
      Nat.pow_le_pow_right (by decide) hexp_le_tower
    exact le_trans h1 h2
  calc (T + 1) ^ D
      ≤ (2 ^ (T + 1)) ^ D := hpow_le
    _ = 2 ^ ((T + 1) * D) := hpow_eq
    _ ≤ 2 ^ GebLean.tower (h + 1) (x + D + 1) := h_outer
    _ = GebLean.tower (h + 2) (x + D + 1) := rfl

/-- Strong polynomial-of-tower bound for `h ≥ 2`: a tower
of height at least 2 dominates polynomial growth without
needing a height bump.  The shift is logarithmic in `D`.

This is the bound used by `polynomial_iter_tower_bound`,
which iterates a polynomially-bounded step.  Keeping the
height fixed across iterations requires this strong form;
the looser `tower_succ_pow_bound` cannot keep height
fixed because it adds 2 to the height each iteration. -/
theorem tower_succ_pow_bound_strong
    (h D x : ℕ) (h_h : 2 ≤ h) :
    (GebLean.tower h x + 1)^D ≤
      GebLean.tower h (x + Nat.log 2 D + 2) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 :=
    ⟨h - 2, by omega⟩
  set y := x + Nat.log 2 D + 2 with hy_def
  set U := GebLean.tower h' x with hU_def
  set T := GebLean.tower (h' + 2) x with hT_def
  have hT_eq : T = 2 ^ (2 ^ U) := rfl
  have hT_pos : 1 ≤ T := by
    rw [hT_eq]
    exact Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (by decide))
  have hT_plus_one_le : T + 1 ≤ 2 * T := by omega
  have hT_pow_eq : T ^ D = 2 ^ ((2 ^ U) * D) := by
    rw [hT_eq, ← Nat.pow_mul]
  have h_2T_pow_eq :
      (2 * T) ^ D = 2 ^ (D + (2 ^ U) * D) := by
    rw [Nat.mul_pow, hT_pow_eq, ← Nat.pow_add]
  have hD_le : D ≤ 2 ^ (Nat.log 2 D + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) D)
  have h_two_pow_U_pos : 1 ≤ 2 ^ U :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have h_sum_eq :
      D + (2 ^ U) * D = (2 ^ U + 1) * D := by ring
  have h_two_pow_U_plus_one_le :
      2 ^ U + 1 ≤ 2 ^ (U + 1) := by
    have hexp : 2 ^ (U + 1) = 2 * 2 ^ U := by
      rw [Nat.pow_succ]; ring
    omega
  have h_main_exp_le :
      (2 ^ U + 1) * D
        ≤ 2 ^ (U + 1) * 2 ^ (Nat.log 2 D + 1) :=
    Nat.mul_le_mul h_two_pow_U_plus_one_le hD_le
  have h_pow_combine :
      2 ^ (U + 1) * 2 ^ (Nat.log 2 D + 1)
        = 2 ^ (U + Nat.log 2 D + 2) := by
    rw [← Nat.pow_add]
    congr 1
    ring
  have h_exp_bound :
      D + (2 ^ U) * D ≤ 2 ^ (U + Nat.log 2 D + 2) := by
    rw [h_sum_eq, ← h_pow_combine]
    exact h_main_exp_le
  have h_shift_le :
      U + Nat.log 2 D + 2 ≤ GebLean.tower h' y := by
    have h_step :=
      tower_add_le_tower_shift h' x (Nat.log 2 D + 1)
    have hyy : x + (Nat.log 2 D + 1) + 1 = y := by
      change x + (Nat.log 2 D + 1) + 1 = x + Nat.log 2 D + 2
      ring
    rw [hyy] at h_step
    have hUU : GebLean.tower h' x + (Nat.log 2 D + 1) + 1
        = U + Nat.log 2 D + 2 := by ring
    rw [hUU] at h_step
    exact h_step
  have h_inner_pow_le :
      2 ^ (U + Nat.log 2 D + 2) ≤ 2 ^ GebLean.tower h' y :=
    Nat.pow_le_pow_right (by decide) h_shift_le
  have h_exp_le_two_pow_tower :
      D + (2 ^ U) * D ≤ 2 ^ GebLean.tower h' y :=
    le_trans h_exp_bound h_inner_pow_le
  have h_target_eq :
      GebLean.tower (h' + 2) y
        = 2 ^ (2 ^ GebLean.tower h' y) := rfl
  change (T + 1) ^ D ≤ GebLean.tower (h' + 2) y
  rw [h_target_eq]
  calc (T + 1) ^ D
      ≤ (2 * T) ^ D := Nat.pow_le_pow_left hT_plus_one_le D
    _ = 2 ^ (D + (2 ^ U) * D) := h_2T_pow_eq
    _ ≤ 2 ^ (2 ^ GebLean.tower h' y) :=
        Nat.pow_le_pow_right (by decide) h_exp_le_two_pow_tower

/-- Iterating a polynomially-bounded step `j` times keeps
the value bounded by a fixed-height tower (height 2) of a
linear function in `(j, x, Nat.log 2 D, m)`.  The bound
relies on `tower_succ_pow_bound_strong` to keep the tower
height fixed across iterations. -/
theorem polynomial_iter_tower_bound
    (step : ℕ → ℕ → ℕ) (D m : ℕ)
    (h_step : ∀ v x, step v x ≤ (max v x + 1) ^ D)
    (v_0 : ℕ → ℕ) (h_base : ∀ x, v_0 x ≤ m * x + m)
    (j x : ℕ) :
    Nat.iterate (fun v => step v x) j (v_0 x) ≤
      GebLean.tower 2
        ((Nat.log 2 D + 2) * j + m * x + m + x
          + Nat.log 2 D + 2) := by
  induction j with
  | zero =>
      simp only [Nat.iterate]
      have h0 : v_0 x ≤ m * x + m := h_base x
      have h1 :
          m * x + m ≤
            (Nat.log 2 D + 2) * 0 + m * x + m + x
              + Nat.log 2 D + 2 := by
        omega
      have h2 :
          (Nat.log 2 D + 2) * 0 + m * x + m + x
            + Nat.log 2 D + 2
            ≤ GebLean.tower 2
              ((Nat.log 2 D + 2) * 0 + m * x + m + x
                + Nat.log 2 D + 2) :=
        GebLean.self_le_tower _ _
      exact le_trans h0 (le_trans h1 h2)
  | succ j ih =>
      set H_j :=
        (Nat.log 2 D + 2) * j + m * x + m + x
          + Nat.log 2 D + 2 with hHj
      set H_succ :=
        (Nat.log 2 D + 2) * (j + 1) + m * x + m + x
          + Nat.log 2 D + 2 with hHsucc
      have h_step_eq :
          (fun v => step v x)^[j + 1] (v_0 x)
            = step ((fun v => step v x)^[j] (v_0 x)) x := by
        rw [Function.iterate_succ_apply']
      rw [h_step_eq]
      set prev := (fun v => step v x)^[j] (v_0 x) with hprev
      have h_prev_le : prev ≤ GebLean.tower 2 H_j := ih
      have h_x_le : x ≤ H_j := by
        change x ≤
          (Nat.log 2 D + 2) * j + m * x + m + x
            + Nat.log 2 D + 2
        omega
      have h_x_le_tower : x ≤ GebLean.tower 2 H_j :=
        le_trans h_x_le (GebLean.self_le_tower 2 H_j)
      have h_max_le : max prev x ≤ GebLean.tower 2 H_j :=
        max_le h_prev_le h_x_le_tower
      have h_max_plus_one_le :
          max prev x + 1 ≤ GebLean.tower 2 H_j + 1 := by
        omega
      have h_pow_le :
          (max prev x + 1) ^ D
            ≤ (GebLean.tower 2 H_j + 1) ^ D :=
        Nat.pow_le_pow_left h_max_plus_one_le D
      have h_strong :
          (GebLean.tower 2 H_j + 1) ^ D
            ≤ GebLean.tower 2 (H_j + Nat.log 2 D + 2) :=
        tower_succ_pow_bound_strong 2 D H_j (by decide)
      have h_step_bound : step prev x ≤ (max prev x + 1) ^ D :=
        h_step prev x
      have h_H_succ_eq :
          H_j + Nat.log 2 D + 2 = H_succ := by
        change
          (Nat.log 2 D + 2) * j + m * x + m + x
              + Nat.log 2 D + 2 + Nat.log 2 D + 2
            = (Nat.log 2 D + 2) * (j + 1) + m * x + m + x
              + Nat.log 2 D + 2
        ring
      calc step prev x
          ≤ (max prev x + 1) ^ D := h_step_bound
        _ ≤ (GebLean.tower 2 H_j + 1) ^ D := h_pow_le
        _ ≤ GebLean.tower 2 (H_j + Nat.log 2 D + 2) :=
            h_strong
        _ = GebLean.tower 2 H_succ := by rw [h_H_succ_eq]

end Nat
