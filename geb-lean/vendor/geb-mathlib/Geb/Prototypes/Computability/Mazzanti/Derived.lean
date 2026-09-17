/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.Mazzanti.Syntax
public import Mathlib.Data.Fin.VecNotation

set_option doc.verso true in
/-!
# Derived expressions for numerical branching

Binary predecessor and branching at zero are derived from recursion and
projections. They are expressions of the algebra, not additional primitives.

## Main definitions

* {lit}`Expr.half` removes the low binary digit.
* {lit}`Expr.cond` selects its second argument at zero and its third otherwise.
* {lit}`Expr.ifZero` substitutes three expressions into that conditional.

## Main statements

* {lit}`Expr.eval_half` and {lit}`Expr.eval_ifZero` give the numerical meanings.

## Tags

function algebra, binary predecessor, conditional
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Mazzanti.Expr

/-- Binary predecessor, obtained by returning the prefix in both recursion branches. -/
def half : Expr 1 := recursion (fun _ : Fin 1 ↦ constant 0 0)
  (fun _ ↦ proj 2 0) (fun _ ↦ proj 2 0) 0

/-- Binary predecessor computes division by two. -/
@[simp] theorem eval_half (n : ℕ) : half.eval ![n] = n / 2 := by
  refine Nat.binaryRec' (motive := fun n ↦ half.eval ![n] = n / 2) rfl ?_ n
  intro bit m hm _
  simpa [half, Nat.bit_div_two] using eval_recursion_bit
    (fun _ : Fin 1 ↦ constant 0 0) (fun _ ↦ proj 2 0) (fun _ ↦ proj 2 0) 0 bit m hm ![]

/-- The conditional's recursion ignores all previous results. -/
def cond : Expr 3 := recursion (fun _ : Fin 1 ↦ proj 2 0)
  (fun _ ↦ proj 4 2) (fun _ ↦ proj 4 2) 0

/-- The conditional tests only whether its first argument is zero. -/
@[simp] theorem eval_cond (n y z : ℕ) : cond.eval ![n, y, z] = if n = 0 then y else z := by
  refine Nat.binaryRec' (motive := fun n ↦
    cond.eval ![n, y, z] = if n = 0 then y else z) rfl ?_ n
  intro bit m hm _
  have hn := Nat.bit_ne_zero_iff.mpr hm
  rw [if_neg hn]
  have he := eval_recursion_bit (fun _ : Fin 1 ↦ proj 2 0)
    (fun _ ↦ proj 4 2) (fun _ ↦ proj 4 2) 0 bit m hm ![y, z]
  cases bit <;> exact he

/-- Branch on an expression's value, with both alternatives themselves expressions. -/
def ifZero {n : ℕ} (test yes no : Expr n) : Expr n := cond.comp ![test, yes, no]

/-- Substitution into the conditional has the expected branching semantics. -/
@[simp] theorem eval_ifZero {n : ℕ} (test yes no : Expr n) (x : Fin n → ℕ) :
    (ifZero test yes no).eval x = if test.eval x = 0 then yes.eval x else no.eval x := by
  rw [ifZero, eval_comp]
  have he : (fun i ↦ (![test, yes, no] i).eval x) = ![test.eval x, yes.eval x, no.eval x] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j ↦ j.elim0))) i
  rw [he]
  exact eval_cond _ _ _

/-- Remove the low digit from an expression's value. -/
def halfOf {n : ℕ} (e : Expr n) : Expr n := half.comp ![e]

/-- Substitution into binary predecessor. -/
@[simp] theorem eval_halfOf {n : ℕ} (e : Expr n) (x : Fin n → ℕ) :
    (halfOf e).eval x = e.eval x / 2 := by
  change half.eval ![e.eval x] = _
  exact eval_half _

end Geb.Mazzanti.Expr
