/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphRuntime

set_option doc.verso true in
/-!
# Bounded graph execution and normal-form read-back

A bounded runtime execution performs the default schedule until its fuel is exhausted,
retaining a normal state once reached. The runner returns a result only when that state
has no further redex. Every returned result reads back a reached graph normal form.
If any abstract graph schedule normalizes the input, the executable runner succeeds at
some finite bound, and its read-back agrees with that abstract normal form.

The premise is graph normalization. Applying these results to compiled kernel programs
requires the separate simulation from the sequential compiler calculus to port graphs.

## Main definitions

* {lit}`GraphRuntime.execute` — execute a bounded number of runtime steps.
* {lit}`GraphRuntime.run` — return the bounded execution's result when it is normal.

## Main statements

* {lit}`GraphRuntime.run_refines` — a successful run reads back a reached graph normal form.
* {lit}`GraphRuntime.run_eq_normal` — its read-back agrees with any reached normal form.
* {lit}`GraphRuntime.halts_of_normalizes` — a normalizing graph has a successful finite run.

## Tags

interaction net, graph runtime, execution, refinement, adequacy, normal form
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.GraphRuntime

universe u

variable {α : Type u} {arity : α → ℕ} {boundary : ℕ}

/-- Execute a bounded number of steps, retaining a state once its redexes are exhausted. -/
def execute (s : PortSystem arity) (fuel : ℕ) (n : State arity boundary) : State arity boundary :=
  Nat.rec (motive := fun _ ↦ State arity boundary → State arity boundary) id
    (fun _ next m ↦ match step s m with
      | none => m
      | some result => next result) fuel n

/-- Zero fuel leaves the runtime state unchanged. -/
@[simp] theorem execute_zero (s : PortSystem arity) (n : State arity boundary) :
    execute s 0 n = n := rfl

/-- A normal runtime state returns immediately at every fuel bound. -/
theorem execute_of_step_none {s : PortSystem arity} {n : State arity boundary}
    (h : step s n = none) (fuel : ℕ) : execute s fuel n = n := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [execute, h]

/-- One initial step followed by the remaining fuel is the same bounded execution. -/
theorem execute_succ (s : PortSystem arity) (fuel : ℕ) (n : State arity boundary) :
    execute s (fuel + 1) n = execute s fuel ((step s n).getD n) := by
  cases h : step s n with
  | none => simp only [Option.getD_none, execute_of_step_none h]
  | some m =>
    change (match step s n with | none => n | some m => execute s fuel m) = _
    rw [h]
    rfl

/-- Every finite runtime execution reads back a finite schedule of graph contractions. -/
theorem execute_refines (s : PortSystem arity) (fuel : ℕ) (n : State arity boundary) :
    Relation.ReflTransGen (Graph.Step s) (graph n) (graph (execute s fuel n)) := by
  refine Nat.rec (motive := fun fuel ↦ ∀ n : State arity boundary,
    Relation.ReflTransGen (Graph.Step s) (graph n) (graph (execute s fuel n)))
      (fun _ ↦ .refl) (fun fuel ih n ↦ ?_) fuel n
  rw [execute_succ]
  cases h : step s n with
  | none => simpa only [h, Option.getD_none, execute_of_step_none h] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen (Graph.Step s) (graph n) (graph n))
  | some m =>
    simpa only [h, Option.getD_some] using
      (Relation.ReflTransGen.single (step_refines h)).trans (ih m)

/-- Return the bounded execution result only when exhaustive redex search declares it normal. -/
def run (s : PortSystem arity) (fuel : ℕ) (n : State arity boundary) :
    Option (State arity boundary) :=
  let result := execute s fuel n
  match step s result with
  | none => some result
  | some _ => none

/-- A successful run returns its bounded execution result and that result has no runtime step. -/
theorem run_spec {s : PortSystem arity} {fuel : ℕ} {n m : State arity boundary}
    (h : run s fuel n = some m) : execute s fuel n = m ∧ step s m = none := by
  unfold run at h
  dsimp only at h
  split at h
  · rename_i hs
    have hm := Option.some.inj h
    exact ⟨hm, hm ▸ hs⟩
  · cases h

/-- A successful runtime run reads back a reached abstract graph normal form. -/
theorem run_refines {s : PortSystem arity} {fuel : ℕ} {n m : State arity boundary}
    (h : run s fuel n = some m) :
    Relation.ReflTransGen (Graph.Step s) (graph n) (graph m) ∧
      Schedule.Normal (Graph.Step s) (graph m) := by
  obtain ⟨hm, hs⟩ := run_spec h
  exact ⟨hm ▸ execute_refines s fuel n, normal_of_step_none hs⟩

/-- The runtime's returned graph agrees with any normal form reached by another graph schedule. -/
theorem run_eq_normal {s : PortSystem arity} {fuel : ℕ} {n m : State arity boundary}
    {q : Graph arity boundary} (h : run s fuel n = some m)
    (hq : Relation.ReflTransGen (Graph.Step s) (graph n) q)
    (hn : Schedule.Normal (Graph.Step s) q) : graph m = q :=
  Graph.normal_unique (run_refines h).1 hq (run_refines h).2 hn

/-- Accessibility of graph reduction makes the exhaustive executable schedule terminate. -/
theorem halts_of_acc {s : PortSystem arity} {q : Graph arity boundary}
    (h : Acc (Function.swap (Graph.Step s)) q) :
    ∀ n : State arity boundary, graph n = q → ∃ fuel m, run s fuel n = some m := by
  refine Acc.rec (motive := fun q _ ↦
    ∀ n : State arity boundary, graph n = q → ∃ fuel m, run s fuel n = some m) ?_ h
  intro q _ ih n hn
  cases hs : step s n with
  | none =>
    exact ⟨0, n, by simp only [run, execute_zero, hs]⟩
  | some m =>
    have hm : Graph.Step s q (graph m) := hn ▸ step_refines hs
    obtain ⟨fuel, result, hr⟩ := ih (graph m) hm m rfl
    refine ⟨fuel + 1, result, ?_⟩
    have he : execute s (fuel + 1) n = execute s fuel m := by
      rw [execute_succ, hs]
      rfl
    simpa only [run, he] using hr

/-- One normalizing abstract graph schedule guarantees a successful finite executable run. -/
theorem halts_of_normalizes {s : PortSystem arity} {n : State arity boundary}
    {q : Graph arity boundary} (h : Relation.ReflTransGen (Graph.Step s) (graph n) q)
    (hn : Schedule.Normal (Graph.Step s) q) : ∃ fuel m, run s fuel n = some m :=
  halts_of_acc (Graph.terminates_of_normalizes h hn) n rfl

end Geb.InteractionNet.GraphRuntime

end
