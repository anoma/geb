/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.Mazzanti.Derived

set_option doc.verso true

/-!
# No internal universal evaluator

Syntactic validation of an expression is distinct from evaluating arbitrary
expression code. An evaluator for every unary expression cannot itself be an
expression of the same algebra. Substitution and the zero test give the diagonal
contradiction, independently of a machine characterization.

## Main statements

* {lit}`Expr.not_universal` excludes a universal evaluator for any assignment of
  natural-number codes to unary expressions. The assignment need not be injective.

## Implementation notes

This does not prohibit an external interpreter, a resource-bounded evaluator
with an explicit budget, or a checker for explicit computation histories. It
excludes an internal total evaluator satisfying the unrestricted specification.

## Tags

function algebra, diagonalization, universal evaluator
-/

public section

namespace Geb.Mazzanti.Expr

/-- No binary expression evaluates every unary expression from a numerical code.
In particular, syntactic membership checking does not supply an internal evaluator. -/
theorem not_universal (code : Expr 1 → ℕ) (universal : Expr 2) :
    ¬ ∀ (e : Expr 1) (n : ℕ), universal.eval ![code e, n] = e.eval ![n] := by
  intro hu
  let diagonal := ifZero (universal.comp ![proj 1 0, proj 1 0]) (constant 1 1) (constant 1 0)
  have hd (n : ℕ) : diagonal.eval ![n] = if universal.eval ![n, n] = 0 then 1 else 0 := by
    simp only [diagonal, eval_ifZero, eval_comp, eval_constant]
    have he : (fun i ↦ (![proj 1 0, proj 1 0] i).eval ![n]) = ![n, n] := by
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl
    simp only [he]
  have h := hu diagonal (code diagonal)
  rw [hd] at h
  by_cases hz : universal.eval ![code diagonal, code diagonal] = 0
  · rw [if_pos hz] at h
    omega
  · rw [if_neg hz] at h
    exact hz h

end Geb.Mazzanti.Expr
