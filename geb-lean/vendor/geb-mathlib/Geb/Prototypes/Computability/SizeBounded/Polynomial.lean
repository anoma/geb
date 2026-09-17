/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Cost
public import Mathlib.Algebra.Polynomial.Eval.Defs

set_option doc.verso true in
/-!
# Polynomial representation of the evaluator's time bound

The natural-number bound in {name}`Geb.SizeBounded.time_le_poly` is represented by a
mathlib polynomial. This is the polynomial representation used by CSLib's single-tape
polynomial-time computability predicate; it does not supply a machine witness.

## Main statements

* {lit}`time_le_polynomial` bounds evaluation time by a polynomial with natural coefficients.

## Implementation notes

This module packages the constructive cost bound using mathlib's polynomial operations,
which depend on classical choice. The evaluator and its arithmetic bounds remain in
{lit}`Geb.Prototypes.Computability.SizeBounded.Cost`.

## Tags

polynomial, complexity, cost model, bitstring
-/

set_option doc.verso true

public section

namespace Geb.SizeBounded

/-- The evaluator's time bound as a natural-coefficient polynomial in mathlib's representation. -/
theorem time_le_polynomial {n : ℕ} (e : SOf n) :
    ∃ p : Polynomial ℕ, ∀ (x : Fin n → List Bool) (m : ℕ),
      (∀ i, (x i).length ≤ m) → (e.account x).time ≤ p.eval m := by
  obtain ⟨c, d, h⟩ := time_le_poly e
  refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x m hx ↦ ?_⟩
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using h x m hx

end Geb.SizeBounded
