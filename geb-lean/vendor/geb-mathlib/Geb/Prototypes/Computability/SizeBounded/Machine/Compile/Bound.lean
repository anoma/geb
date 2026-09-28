/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Basic

set_option doc.verso true in
/-!
# The step bound of a compiled program

{lit}`stepBound` reads a bound on a compiled program's step count off an
expression's syntax, as a function of a bound on its arguments' lengths, by
the same fold {name}`Geb.SizeBounded.nsiConst` uses on {name}`Geb.SizeBounded.sig`.
{lit}`stepValue` assembles one node's bound from its children's: the three
base forms are affine in the length bound; a substitution node's bound is a
multiple of the maximum of its argument bounds plus its head's; a recursion
node's bound is built from the loop body's, itself the maximum of the two
bits' step bounds, iterated over the length bound.

{lit}`le_nsiValue` bounds each child's contribution to
{name}`Geb.SizeBounded.nsiValue` by the value the parent node assigns it.

# Main definitions

* {lit}`stepValue` — the step bound of one node from its children's.
* {lit}`stepBound` — the step bound of an expression, by the fold.

# Main statements

* {lit}`stepBound_mk` — the fold's computation rule.
* {lit}`le_nsiValue` — each child's constant is at most its node's.

# Tags

Turing machine, step bound, recursion on notation, size-bounded
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Geb.SizeBounded (Shape Direction sig finMax le_finMax)

public section

/-- The step bound of one node from its children's, as functions of the length bound. -/
@[expose] def stepValue : (a : Shape) → (Direction a → ℕ → ℕ) → ℕ → ℕ
  | .const _ _, _ => fun B ↦ 4 * B + 9
  | .proj _ _, _ => fun B ↦ 5 * B + 12
  | .sbs _, _ => fun B ↦ 7 * B + 16
  | .comp _ m, t => fun B ↦ m * finMax m (fun i ↦ t (.inr i) B) + 1 + t (.inl ()) B
  | .srn _ b _, t => fun B ↦
      let body := b * max (finMax b fun l ↦ t (.inr (.inl l)) B)
        (finMax b fun l ↦ t (.inr (.inr l)) B) + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16)
        + (5 * B + 12)
      (5 * B + 12) + (4 * B + 9) + (b * finMax b (fun l ↦ t (.inl l) B) + 1)
        + (B * (body + 2 * B + 6) + 3) + (5 * B + 12)

/-- The step bound of an expression as a function of the length bound, read off
its syntax by folding {name}`stepValue` over the tree. -/
@[expose] def stepBound : sig.toPFunctor.W → ℕ → ℕ :=
  WType.elim (ℕ → ℕ) fun x ↦ stepValue x.1 x.2

/-- The fold's computation rule. -/
theorem stepBound_mk (a : Shape) (f : Direction a → sig.toPFunctor.W) :
    stepBound (WType.mk a f) = stepValue a fun d ↦ stepBound (f d) := rfl

/-- Each child's constant is at most its node's. -/
theorem le_nsiValue : ∀ (a : Shape) (k : Direction a → ℕ) (d : Direction a),
    k d ≤ Geb.SizeBounded.nsiValue a k := by
  intro a k d
  cases a with
  | const n w => exact d.elim0
  | proj n i => exact d.elim0
  | sbs b => exact d.elim0
  | comp n m =>
    cases d with
    | inl u => exact Nat.le_max_left _ _
    | inr i => exact Nat.le_trans (le_finMax m (fun i ↦ k (.inr i)) i) (Nat.le_max_right _ _)
  | srn a b j =>
    cases d with
    | inl l =>
      exact Nat.le_trans (le_finMax b (fun l ↦ k (.inl l)) l) (Nat.le_max_left _ _)
    | inr d' =>
      cases d' with
      | inl l =>
        exact Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inl l))) l)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      | inr l =>
        exact Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inr l))) l)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end

end Geb.SizeBounded.Machine
