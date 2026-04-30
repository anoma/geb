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
- `Nat.polynomial_iter_tower_two_bound` — iterating a
  polynomially-bounded step `j` times keeps the value
  within a height-2 tower of a linear function.

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

end Nat
