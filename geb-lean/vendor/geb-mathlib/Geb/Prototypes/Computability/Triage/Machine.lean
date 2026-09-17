/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Size

set_option doc.verso true in
/-!
# An explicit traversal machine for one triage step

The machine descends through applications, contracts once, then rebuilds the
application context. Its stack stores untouched siblings, never offsets or copies
of ancestor expressions. Values are opaque during descent.

## Main definitions

* {lit}`Cfg` distinguishes descent, context rebuilding, and termination.
* {lit}`next` is one traversal transition.
* {lit}`run` performs a fixed number of transitions through a natural-number recursor.
* {lit}`footprint` counts the serialized data retained in a configuration.

## Implementation notes

This is an abstract traversal machine over explicit trees. A transition may split
or rebuild a serialized expression. Its transition count is not a count of
multitape Turing-machine transitions. The separate scan accounting charges for
traversing the serialized state, and does not supply a verified tape compilation.

## Tags

tree calculus, abstract machine, zipper, space complexity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage.Machine

open Expr

/-- Descent retains inner frames first; rebuilding consumes them in that order. -/
inductive Cfg
  | seek (focus : Expr) (ctx : List Frame)
  | rebuild (focus : Expr) (ctx : List Frame)
  | done (result : Option Expr)

/-- One finite-control transition, never traversing inside an embedded value. -/
def next : Cfg → Cfg
  | .seek e ctx => match e with
    | ⟨none, c⟩ => .seek (c true) (.inr (c false) :: ctx)
    | ⟨some v, _⟩ => match ctx with
      | [] => .done none
      | .inr f :: ctx => match f.getValue with
        | some fv => .rebuild (contract fv v) ctx
        | none => .seek f (.inl (value v) :: ctx)
      | .inl x :: ctx => match x.getValue with
        | some xv => .rebuild (contract v xv) ctx
        | none => .done none
  | .rebuild e [] => .done (some e)
  | .rebuild e (.inl x :: ctx) => .rebuild (app e x) ctx
  | .rebuild e (.inr f :: ctx) => .rebuild (app f e) ctx
  | .done result => .done result

@[simp] theorem next_seek_app (f x : Expr) (ctx : List Frame) :
    next (.seek (app f x) ctx) = .seek x (.inr f :: ctx) := rfl

/-- A reached value either completes the search or enables a root contraction. -/
theorem next_seek_value (v : Value) (ctx : List Frame) : next (.seek (value v) ctx) =
    match ctx with
    | [] => .done none
    | .inr f :: ctx => match f.getValue with
      | some fv => .rebuild (contract fv v) ctx
      | none => .seek f (.inl (value v) :: ctx)
    | .inl x :: ctx => match x.getValue with
      | some xv => .rebuild (contract v xv) ctx
      | none => .done none := rfl

/-- A terminal configuration is absorbing. -/
def halted : Cfg → Bool
  | .done _ => true
  | _ => false

/-- A bounded machine run, carrying all recursion in the natural-number recursor. -/
def run : ℕ → Cfg → Cfg := Nat.rec id (fun _ rec cfg ↦ rec (next cfg))

@[simp] theorem run_zero (cfg : Cfg) : run 0 cfg = cfg := rfl

@[simp] theorem run_succ (n : ℕ) (cfg : Cfg) : run (n + 1) cfg = run n (next cfg) := rfl

@[simp] theorem run_done (n : ℕ) (result : Option Expr) : run n (.done result) = .done result :=
  Nat.rec rfl (fun _ ih ↦ ih) n

/-- Application count; entire values are terminal leaves for this traversal. -/
def applications : Expr → ℕ := WType.elim ℕ fun x ↦
  match x with
  | ⟨some _, _⟩ => 0
  | ⟨none, f⟩ => 1 + f false + f true

@[simp] theorem applications_value (v : Value) : applications (value v) = 0 := rfl

@[simp] theorem applications_app (f x : Expr) :
    applications (app f x) = 1 + applications f + applications x := rfl

/-- The application count is bounded by the serialized input length. -/
theorem applications_le_bits (e : Expr) : applications e ≤ e.bits :=
  expr_ind (P := fun e ↦ applications e ≤ e.bits) (fun _ ↦ Nat.zero_le _)
    (fun f x hf hx ↦ by simp only [applications_app, bits_app]; omega) e

/-- Remaining descent work associated with an untouched sibling. -/
def frameWork : Frame → ℕ
  | .inl _ => 1
  | .inr f => 4 * applications f + 2

/-- A decreasing bound on the remaining traversal transitions. -/
def potential : Cfg → ℕ
  | .seek e ctx => 4 * applications e + (ctx.map frameWork).sum + ctx.length + 2
  | .rebuild _ ctx => ctx.length + 1
  | .done _ => 0

/-- The serialized sibling retained by a context frame. -/
def frameBits : Frame → ℕ
  | .inl x => x.bits
  | .inr f => f.bits

/-- Serialized focus and siblings, allowing eight bits for each context frame. -/
def contextBits (e : Expr) (ctx : List Frame) : ℕ :=
  e.bits + (ctx.map frameBits).sum + 8 * ctx.length

/-- Stored expression data, with context frames charged by their application-header width. -/
def footprint : Cfg → ℕ
  | .seek e ctx | .rebuild e ctx => contextBits e ctx
  | .done none => 0
  | .done (some e) => e.bits

/-- Before contraction reserve room for duplication; afterward only rebuilding remains. -/
def reserve : Cfg → ℕ
  | .seek e ctx => 2 * contextBits e ctx
  | .rebuild e ctx => contextBits e ctx
  | .done none => 0
  | .done (some e) => e.bits

/-- Stored data never exceeds its phase-specific reserve. -/
theorem footprint_le_reserve (cfg : Cfg) : footprint cfg ≤ reserve cfg := by
  cases cfg with
  | seek e ctx => simp [footprint, reserve]; omega
  | rebuild e ctx => rfl
  | done result => cases result <;> rfl

/-- Every live transition strictly decreases the potential. -/
theorem potential_next_lt (cfg : Cfg) (h : halted cfg = false) :
    potential (next cfg) < potential cfg := by
  cases cfg with
  | done _ => cases h
  | rebuild e ctx =>
    cases ctx with
    | nil => simp [next, potential]
    | cons frame ctx => cases frame <;> simp [next, potential]
  | seek e ctx =>
    refine expr_ind (P := fun e ↦ potential (next (.seek e ctx)) < potential (.seek e ctx))
      ?_ ?_ e
    · intro v
      cases ctx with
      | nil => simp [next_seek_value, potential]
      | cons frame ctx =>
        cases frame with
        | inl x =>
          cases hx : x.getValue <;> simp [next_seek_value, hx, potential, frameWork]
          all_goals omega
        | inr f =>
          cases hf : f.getValue with
          | none => simp [next_seek_value, hf, potential, frameWork]; omega
          | some fv =>
            have he := (getValue_eq_some_iff f fv).mp hf
            subst f
            simp [next_seek_value, potential, frameWork]
            omega
    · intro f x _ _
      simp [next_seek_app, potential, frameWork]
      omega

/-- A zero potential means that the machine is already terminal. -/
theorem halted_of_potential_zero (cfg : Cfg) (h : potential cfg = 0) : halted cfg = true := by
  cases cfg <;> simp_all [potential, halted]

/-- Fuel at least the initial potential suffices for termination. -/
theorem halted_run (n : ℕ) : ∀ cfg, potential cfg ≤ n → halted (run n cfg) = true := by
  refine Nat.rec ?_ ?_ n
  · intro cfg h
    change potential cfg ≤ 0 at h
    exact halted_of_potential_zero cfg (by omega)
  · intro n ih cfg h
    cases hh : halted cfg with
    | true => cases cfg <;> simp_all [halted, next]
    | false =>
      have hp := potential_next_lt cfg hh
      exact ih (next cfg) (by omega)

/-- Every transition preserves the space reserve, including the single duplication. -/
theorem reserve_next_le (cfg : Cfg) : reserve (next cfg) ≤ reserve cfg := by
  cases cfg with
  | done result => rfl
  | rebuild e ctx =>
    cases ctx with
    | nil => simp [next, reserve, contextBits]
    | cons frame ctx =>
      cases frame <;> simp [next, reserve, contextBits, frameBits] <;> omega
  | seek e ctx =>
    refine expr_ind (P := fun e ↦ reserve (next (.seek e ctx)) ≤ reserve (.seek e ctx))
      ?_ ?_ e
    · intro v
      cases ctx with
      | nil => simp [next_seek_value, reserve]
      | cons frame ctx =>
        cases frame with
        | inl x =>
          cases hx : x.getValue with
          | none => simp [next_seek_value, hx, reserve]
          | some xv =>
            have he := (getValue_eq_some_iff x xv).mp hx
            subst x
            have hb := contract_bits_le v xv
            simp only [bits_app, bits_value] at hb
            simp [next_seek_value, reserve, contextBits, frameBits]
            omega
        | inr f =>
          cases hf : f.getValue with
          | none => simp [next_seek_value, hf, reserve, contextBits, frameBits]; omega
          | some fv =>
            have he := (getValue_eq_some_iff f fv).mp hf
            subst f
            have hb := contract_bits_le fv v
            simp only [bits_app, bits_value] at hb
            simp [next_seek_value, reserve, contextBits, frameBits]
            omega
    · intro f x _ _
      simp [next_seek_app, reserve, contextBits, frameBits]
      omega

/-- The reserve is nonincreasing along every finite run. -/
theorem reserve_run_le (n : ℕ) : ∀ cfg, reserve (run n cfg) ≤ reserve cfg :=
  Nat.rec (fun _ ↦ Nat.le_refl _) (fun _ ih cfg ↦
    (ih (next cfg)).trans (reserve_next_le cfg)) n

/-- All configurations of a run use at most twice the original serialized input size. -/
theorem footprint_run_le (e : Expr) (n : ℕ) : footprint (run n (.seek e [])) ≤ 2 * e.bits := by
  have h := (footprint_le_reserve (run n (.seek e []))).trans (reserve_run_le n (.seek e []))
  simpa [reserve, contextBits] using h

/-- A linear number of traversal transitions suffices for every expression. -/
theorem halted_run_bits (e : Expr) : halted (run (4 * e.bits + 2) (.seek e [])) = true := by
  apply halted_run
  have h := applications_le_bits e
  simp [potential]
  omega

end Geb.Triage.Machine
