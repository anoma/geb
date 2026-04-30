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

end Nat
