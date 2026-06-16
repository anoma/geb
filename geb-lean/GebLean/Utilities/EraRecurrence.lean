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

end GebLean.EraRecurrence
