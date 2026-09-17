/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Syntax

set_option doc.verso true in
/-!
# One branch-first step of triage calculus

A step first reduces an application's argument, then its function, and finally
contracts their application when both are values. Values are opaque to this
traversal. Absorbing an argument into a leaf or stem counts as one step, as in
the visual presentation. A triage rule constructs pending applications without
evaluating them.

## Main definitions

* {lit}`contract` applies one absorption or triage rule to two values.
* {lit}`step` returns one successor, or {lit}`none` for a value.
* {lit}`Step` is contextual closure of one root contraction.

## Main statements

* The {lit}`contract_*` equations give the individual rules.
* {lit}`step_eq_none_iff` proves progress and identifies terminal expressions.
* {lit}`step_sound` proves that a successful step performs one contextual contraction.

## References

* \[TreeCalculusSpecification\], triage rules (1), (2), and (3a-c).
* \[TreeCalculusImplementation\], branch-first evaluator.

## Tags

tree calculus, operational semantics, small step, evaluation context
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage

open Expr

/-- Apply one rule to values. Recursive calls of the reference evaluator become syntax. -/
def contract (f x : Value) : Expr :=
  match f with
  | ⟨.leaf, _⟩ => value (Value.stem x)
  | ⟨.stem, c⟩ => value (Value.fork (c ()) x)
  | ⟨.fork, c⟩ =>
    match c false with
    | ⟨.leaf, _⟩ => value (c true)
    | ⟨.stem, d⟩ => app (app (value (d ())) (value x)) (app (value (c true)) (value x))
    | ⟨.fork, d⟩ =>
      match x with
      | ⟨.leaf, _⟩ => value (d false)
      | ⟨.stem, e⟩ => app (value (d true)) (value (e ()))
      | ⟨.fork, e⟩ => app (app (value (c true)) (value (e false))) (value (e true))

/-- A leaf absorbs its argument into a stem. -/
@[simp] theorem contract_leaf (x : Value) :
    contract Value.leaf x = value (Value.stem x) := rfl

/-- A stem absorbs its argument into a fork. -/
@[simp] theorem contract_stem (a x : Value) :
    contract (Value.stem a) x = value (Value.fork a x) := rfl

/-- Rule (1) selects the second child. -/
@[simp] theorem contract_select (a x : Value) :
    contract (Value.fork Value.leaf a) x = value a := rfl

/-- Rule (2) duplicates the argument, leaving the resulting applications pending. -/
@[simp] theorem contract_duplicate (a b x : Value) :
    contract (Value.fork (Value.stem a) b) x =
      app (app (value a) (value x)) (app (value b) (value x)) := rfl

/-- Rule (3a) handles a leaf argument. -/
@[simp] theorem contract_triage_leaf (a b c : Value) :
    contract (Value.fork (Value.fork a b) c) Value.leaf = value a := rfl

/-- Rule (3b) handles a stem argument. -/
@[simp] theorem contract_triage_stem (a b c x : Value) :
    contract (Value.fork (Value.fork a b) c) (Value.stem x) = app (value b) (value x) := rfl

/-- Rule (3c) handles a fork argument. -/
@[simp] theorem contract_triage_fork (a b c x y : Value) :
    contract (Value.fork (Value.fork a b) c) (Value.fork x y) =
      app (app (value c) (value x)) (value y) := rfl

/-- The step algebra retains the original children beside their possible successors. -/
def stepFold : Expr → Expr × Option Expr := WType.elim (Expr × Option Expr) fun z ↦
  match z with
  | ⟨some v, _⟩ => (value v, none)
  | ⟨none, c⟩ =>
    let f := c false
    let x := c true
    (app f.1 x.1, match x.2 with
    | some x' => some (app f.1 x')
    | none =>
      match f.2 with
      | some f' => some (app f' x.1)
      | none =>
        match f.1.getValue, x.1.getValue with
        | some fv, some xv => some (contract fv xv)
        | _, _ => none)

/-- The fold's first component reconstructs its input exactly. -/
@[simp] theorem stepFold_fst (e : Expr) : (stepFold e).1 = e :=
  expr_ind (P := fun e ↦ (stepFold e).1 = e) (fun _ ↦ rfl) (fun f x hf hx ↦ by
    change app (stepFold f).1 (stepFold x).1 = app f x
    rw [hf, hx]) e

/-- One branch-first step: right child, left child, then one root rule. -/
def step (e : Expr) : Option Expr := (stepFold e).2

@[simp] theorem step_value (v : Value) : step (value v) = none := rfl

/-- The recursive equation makes the evaluation order explicit. -/
theorem step_app (f x : Expr) : step (app f x) =
    match step x with
    | some x' => some (app f x')
    | none =>
      match step f with
      | some f' => some (app f' x)
      | none =>
        match f.getValue, x.getValue with
        | some fv, some xv => some (contract fv xv)
        | _, _ => none := by
  unfold step
  change (match (stepFold x).2 with
    | some x' => some (app (stepFold f).1 x')
    | none => match (stepFold f).2 with
      | some f' => some (app f' (stepFold x).1)
      | none => match (stepFold f).1.getValue, (stepFold x).1.getValue with
        | some fv, some xv => some (contract fv xv)
        | _, _ => none) = _
  simp only [stepFold_fst]
  rfl

/-- Exactly values have no successor. In particular, there are no stuck applications. -/
theorem step_eq_none_iff (e : Expr) : step e = none ↔ ∃ v, e = value v := by
  refine expr_ind (P := fun e ↦ step e = none ↔ ∃ v, e = value v) ?_ ?_ e
  · intro v
    exact ⟨fun _ ↦ ⟨v, rfl⟩, fun _ ↦ rfl⟩
  · intro f x hf hx
    constructor
    · intro h
      rw [step_app] at h
      cases hxs : step x with
      | some x' => simp [hxs] at h
      | none =>
        obtain ⟨xv, rfl⟩ := hx.mp hxs
        cases hfs : step f with
        | some f' => simp [hfs] at h
        | none =>
          obtain ⟨fv, rfl⟩ := hf.mp hfs
          simp at h
    · rintro ⟨v, h⟩
      have hh := congrArg getValue h
      simp at hh

/-- A context frame stores the untouched sibling and which side contains the hole. -/
abbrev Frame := Sum Expr Expr

/-- Fill an application context; its head is the outermost frame. -/
def plug (ctx : List Frame) (e : Expr) : Expr := ctx.foldr (fun frame hole ↦
  match frame with
  | .inl x => app hole x
  | .inr f => app f hole) e

/-- One absorption or triage rule inside an application-only context. -/
def Step (e e' : Expr) : Prop := ∃ ctx f x,
  e = plug ctx (app (value f) (value x)) ∧ e' = plug ctx (contract f x)

/-- A contraction remains one contraction under a function-position context. -/
theorem Step.app_left {f f' : Expr} (h : Step f f') (x : Expr) :
    Step (app f x) (app f' x) := by
  obtain ⟨ctx, a, b, rfl, rfl⟩ := h
  exact ⟨.inl x :: ctx, a, b, rfl, rfl⟩

/-- A contraction remains one contraction under an argument-position context. -/
theorem Step.app_right (f : Expr) {x x' : Expr} (h : Step x x') :
    Step (app f x) (app f x') := by
  obtain ⟨ctx, a, b, rfl, rfl⟩ := h
  exact ⟨.inr f :: ctx, a, b, rfl, rfl⟩

/-- A successful computation performs exactly one contextual contraction. -/
theorem step_sound (e : Expr) : ∀ e', step e = some e' → Step e e' := by
  refine expr_ind (P := fun e ↦ ∀ e', step e = some e' → Step e e') ?_ ?_ e
  · intro v e' h
    simp at h
  · intro f x hf hx e' h
    rw [step_app] at h
    cases hxs : step x with
    | some x' =>
      simp only [hxs, Option.some.injEq] at h
      subst e'
      exact (hx x' hxs).app_right f
    | none =>
      obtain ⟨xv, rfl⟩ := (step_eq_none_iff x).mp hxs
      cases hfs : step f with
      | some f' =>
        simp only [step_value, hfs, Option.some.injEq] at h
        subst e'
        exact (hf f' hfs).app_left (value xv)
      | none =>
        obtain ⟨fv, rfl⟩ := (step_eq_none_iff f).mp hfs
        simp only [step_value, getValue_value, Option.some.injEq] at h
        subst e'
        exact ⟨[], fv, xv, rfl, rfl⟩

end Geb.Triage
