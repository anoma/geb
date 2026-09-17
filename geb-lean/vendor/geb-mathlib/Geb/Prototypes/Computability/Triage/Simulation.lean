/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Machine

set_option doc.verso true in
/-!
# Correctness of the triage traversal machine

Function-position frames retain already evaluated arguments. This invariant
connects the explicit descent and rebuilding machine with the branch-first
small-step semantics.

## Main definitions

* {lit}`Ready` is the invariant on the evaluation context.
* {lit}`execute` runs the machine with its proved sufficient fuel.

## Main statements

* {lit}`answer_next` and {lit}`answer_run` preserve the semantic answer.
* {lit}`execute_eq_step` identifies machine execution with exactly one semantic step.

## Tags

tree calculus, abstract machine, simulation, correctness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage.Machine

open Expr

/-- Function-position frames retain a value argument. Argument-position frames are unrestricted. -/
def FrameReady : Frame → Prop
  | .inl x => ∃ v, x = value v
  | .inr _ => True

/-- Every function-position frame of the context has its argument ready. -/
def Ready (ctx : List Frame) : Prop := ∀ frame ∈ ctx, FrameReady frame

/-- The invariant ignores whether frames are listed inside-out or outside-in. -/
theorem ready_reverse {ctx : List Frame} (h : Ready ctx) : Ready ctx.reverse :=
  fun frame hf ↦ h frame (List.mem_reverse.mp hf)

/-- Dropping a context frame preserves readiness. -/
theorem ready_tail {frame : Frame} {ctx : List Frame} (h : Ready (frame :: ctx)) : Ready ctx :=
  fun f hf ↦ h f (List.mem_cons_of_mem _ hf)

/-- Context concatenation composes plugging. -/
theorem plug_append (ctx rest : List Frame) (e : Expr) :
    plug (ctx ++ rest) e = plug ctx (plug rest e) := by simp [plug, List.foldr_append]

/-- Popping an inside-out frame reconstructs one application at the focus. -/
theorem plug_reverse_cons (frame : Frame) (ctx : List Frame) (e : Expr) :
    plug (frame :: ctx).reverse e = plug ctx.reverse
      (match frame with | .inl x => app e x | .inr f => app f e) := by
  cases frame <;> simp [List.reverse_cons, plug]

/-- A successful step propagates through a ready evaluation context. -/
theorem step_plug {ctx : List Frame} (hctx : Ready ctx) {e e' : Expr}
    (h : step e = some e') : step (plug ctx e) = some (plug ctx e') := by
  have aux : ∀ ctx : List Frame, Ready ctx → step (plug ctx e) = some (plug ctx e') := by
    refine List.rec ?_ ?_
    · intro _
      exact h
    · intro frame ctx ih hc
      have ht := ih (ready_tail hc)
      cases frame with
      | inr f =>
        change step (app f (plug ctx e)) = some (app f (plug ctx e'))
        rw [step_app, ht]
      | inl x =>
        obtain ⟨v, rfl⟩ := hc (.inl x) (List.mem_cons_self)
        change step (app (plug ctx e) (value v)) = some (app (plug ctx e') (value v))
        rw [step_app, step_value, ht]
  exact aux ctx hctx

/-- Readiness matters only during descent. -/
def Invariant : Cfg → Prop
  | .seek _ ctx => Ready ctx
  | _ => True

/-- Every machine transition preserves the evaluation-context invariant. -/
theorem invariant_next (cfg : Cfg) (h : Invariant cfg) : Invariant (next cfg) := by
  cases cfg with
  | done result => trivial
  | rebuild e ctx => cases ctx with
    | nil => trivial
    | cons frame ctx => cases frame <;> trivial
  | seek e ctx =>
    refine expr_ind (P := fun e ↦ Invariant (next (.seek e ctx))) ?_ ?_ e
    · intro v
      cases ctx with
      | nil => trivial
      | cons frame ctx =>
        have ht : Ready ctx := ready_tail h
        cases frame with
        | inl x => cases hx : x.getValue <;> simp [next_seek_value, hx, Invariant]
        | inr f =>
          cases hf : f.getValue with
          | some fv => simp [next_seek_value, hf, Invariant]
          | none =>
            simp only [next_seek_value, hf]
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨v, rfl⟩
            · exact ht g hg
    · intro f x _ _
      rw [next_seek_app]
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · trivial
      · exact h g hg

/-- The eventual semantic answer associated with an intermediate configuration. -/
def answer : Cfg → Option Expr
  | .seek e ctx => step (plug ctx.reverse e)
  | .rebuild e ctx => some (plug ctx.reverse e)
  | .done result => result

/-- One abstract transition preserves the eventual one-step result. -/
theorem answer_next (cfg : Cfg) (h : Invariant cfg) : answer (next cfg) = answer cfg := by
  cases cfg with
  | done _ => rfl
  | rebuild e ctx =>
    cases ctx with
    | nil => rfl
    | cons frame ctx => cases frame <;> simp only [next, answer, plug_reverse_cons]
  | seek e ctx =>
    refine expr_ind (P := fun e ↦ answer (next (.seek e ctx)) = answer (.seek e ctx)) ?_ ?_ e
    · intro v
      cases ctx with
      | nil => rfl
      | cons frame ctx =>
        have ht : Ready ctx.reverse := ready_reverse (ready_tail h)
        cases frame with
        | inl x =>
          obtain ⟨xv, rfl⟩ := h (.inl x) (List.mem_cons_self)
          change some (plug ctx.reverse (contract v xv)) =
            step (plug (.inl (value xv) :: ctx).reverse (value v))
          rw [plug_reverse_cons]
          exact (step_plug ht (show step (app (value v) (value xv)) =
            some (contract v xv) by rw [step_app]; rfl)).symm
        | inr f =>
          cases hf : f.getValue with
          | none => simp only [next_seek_value, hf, answer, plug_reverse_cons]
          | some fv =>
            have he := (getValue_eq_some_iff f fv).mp hf
            subst f
            change some (plug ctx.reverse (contract fv v)) =
              step (plug (.inr (value fv) :: ctx).reverse (value v))
            rw [plug_reverse_cons]
            exact (step_plug ht (show step (app (value fv) (value v)) =
              some (contract fv v) by rw [step_app]; rfl)).symm
    · intro f x _ _
      simp only [next_seek_app, answer, plug_reverse_cons]

/-- A finite run preserves the semantic answer. -/
theorem answer_run (n : ℕ) : ∀ cfg, Invariant cfg → answer (run n cfg) = answer cfg :=
  Nat.rec (fun _ _ ↦ rfl) (fun _ ih cfg h ↦
    (ih (next cfg) (invariant_next cfg h)).trans (answer_next cfg h)) n

/-- Execute the traversal machine with a proved linear amount of fuel. -/
def execute (e : Expr) : Option Expr :=
  match run (4 * e.bits + 2) (.seek e []) with
  | .done result => result
  | _ => none

/-- The explicit machine computes precisely one branch-first step. -/
@[simp] theorem execute_eq_step (e : Expr) : execute e = step e := by
  have hh := halted_run_bits e
  have ha := answer_run (4 * e.bits + 2) (.seek e [])
    (show Invariant (.seek e []) from by intro frame h; cases h)
  cases hr : run (4 * e.bits + 2) (.seek e []) with
  | seek _ _ => simp only [hr, halted, Bool.false_eq_true] at hh
  | rebuild _ _ => simp only [hr, halted, Bool.false_eq_true] at hh
  | done result =>
    have he : result = step e := by
      simpa only [hr, answer, List.reverse_nil, plug, List.foldr_nil] using ha
    simpa only [execute, hr] using he

end Geb.Triage.Machine
