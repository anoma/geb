/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Aesop
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ToDual

set_option doc.verso true

/-!
# One-pass scanner for binary trees with bitstring leaves

The scanner uses a mode and a pending-tree counter. Forks increase the counter;
leaf terminators decrease it. Payload bits are read in their own mode.

## Main definitions

* {lit}`step` consumes one bit.
* {lit}`scan` starts the scan with one pending tree.
* {lit}`validBool` accepts exactly when the scanner ends in its accepting mode.

## Tags

binary tree, recognizer, finite control, counter
-/

@[expose] public section

namespace Geb.BitTree

/-- Scanner modes distinguish tree tags, string tags, payload bits and terminal states. -/
inductive Mode where
  | tree | string | bit | done | dead
  deriving DecidableEq, Repr

/-- A finite-control mode paired with the number of trees awaiting completion. -/
abbrev State := Mode × Nat

/-- Complete one leaf, accepting only when the last pending tree is completed. -/
def finish (n : Nat) : State := if n = 1 then (.done, 0) else (.tree, n - 1)

/-- Consume one input bit, with payload bits interpreted only in payload mode. -/
def step (s : State) (b : Bool) : State :=
  match s.1 with
  | .tree => if b then (.tree, s.2 + 1) else (.string, s.2)
  | .string => if b then (.bit, s.2) else finish s.2
  | .bit => (.string, s.2)
  | .done => (.dead, s.2)
  | .dead => s

/-- Run the scanner from its single pending root. -/
def scan (w : List Bool) : State := w.foldl step (.tree, 1)

/-- Accept exactly when one tree has ended at the end of the input. -/
def validBool (w : List Bool) : Bool := decide ((scan w).1 = .done)

/-- Active modes always retain at least one pending tree. -/
def Active (s : State) : Prop :=
  s.1 = .tree ∨ s.1 = .string ∨ s.1 = .bit → 0 < s.2

/-- Reading a bit preserves positivity of the pending count in active modes. -/
theorem active_step (s : State) (b : Bool) (h : Active s) : Active (step s b) := by
  rcases s with ⟨m, n⟩
  cases m <;> cases b <;> simp_all [Active, step, finish]
  split <;> simp_all
  omega

/-- A fold of scanner steps preserves the active-mode invariant. -/
theorem active_foldl (w : List Bool) : ∀ s, Active s → Active (w.foldl step s) :=
  List.rec (fun _ h ↦ h) (fun b _ ih s h ↦ ih (step s b) (active_step s b h)) w

/-- Every reachable active mode has a positive pending count. -/
theorem scan_active_pos (w : List Bool) :
    (scan w).1 = .tree ∨ (scan w).1 = .string ∨ (scan w).1 = .bit →
      0 < (scan w).2 :=
  active_foldl w (.tree, 1) (by simp [Active])

end Geb.BitTree
