/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual

set_option doc.verso true in
/-!
# A bitwise scanner for delta-prefixed leaf payloads

The finite control distinguishes tree tags, the unary part of a delta header,
the two binary header fields, and raw payload bits. The pending-subtree counter
is changed only by fork tags and completed leaf payloads.

## Main definitions

* {lit}`Mode` records the current phase and its numeric counters.
* {lit}`step` consumes exactly one input bit.
* {lit}`scan` folds the transition over the input.

## Tags

Elias delta code, binary tree, streaming recognizer
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.Elias.Scanner

/-- Header and payload phases, with remaining lengths and partial binary values. -/
inductive Mode where
  | tree
  | zeros (count : ℕ)
  | size (remaining value : ℕ)
  | length (remaining value : ℕ)
  | payload (remaining : ℕ)
  | done
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- A phase and the number of pending subtrees. -/
abbrev State := Mode × ℕ

/-- Complete one leaf, recognizing the final pending subtree. -/
def finish (n : ℕ) : State := if n = 1 then (.done, 0) else (.tree, n - 1)

/-- Read one bit, including all phase changes that consume no additional input. -/
def step : State → Bool → State
  | (.tree, n), true => (.tree, n + 1)
  | (.tree, n), false => (.zeros 0, n)
  | (.zeros z, n), false => (.zeros (z + 1), n)
  | (.zeros z, n), true => if z = 0 then finish n else (.size z 1, n)
  | (.size r v, n), b =>
    if r = 1 then (.length (Nat.bit b v - 1) 1, n) else (.size (r - 1) (Nat.bit b v), n)
  | (.length r v, n), b =>
    if r = 1 then (.payload (Nat.bit b v - 1), n) else (.length (r - 1) (Nat.bit b v), n)
  | (.payload r, n), _ => if r = 1 then finish n else (.payload (r - 1), n)
  | (.done, n), _ => (.dead, n)
  | (.dead, n), _ => (.dead, n)

/-- Scan from one pending root. -/
def scan (w : List Bool) : State := w.foldl step (.tree, 1)

/-- Accept exactly when the complete root ends at the end of input. -/
def validBool (w : List Bool) : Bool := decide ((scan w).1 = .done)

/-- Positive pending counts and positive remaining lengths in the active phases. -/
def Active : State → Prop
  | (.done, n) | (.dead, n) => n = 0
  | (.tree, n) | (.zeros _, n) => 0 < n
  | (.size r v, n) | (.length r v, n) => 0 < n ∧ 0 < r ∧ 0 < v
  | (.payload r, n) => 0 < n ∧ 0 < r

/-- Completing an active leaf preserves the scanner invariant. -/
theorem active_finish (n : ℕ) (hn : 0 < n) : Active (finish n) := by
  unfold finish
  split <;> simp only [Active] <;> omega

/-- Consuming one bit preserves the invariant. -/
theorem active_step (s : State) (b : Bool) (h : Active s) : Active (step s b) := by
  rcases s with ⟨m, n⟩
  cases m with
  | tree =>
    change 0 < n at h
    cases b <;> change 0 < _ <;> omega
  | zeros z =>
    cases b with
    | false => exact h
    | true =>
      change Active (if z = 0 then finish n else (.size z 1, n))
      split
      · exact active_finish n h
      · exact ⟨h, by omega, by decide⟩
  | size r v =>
    obtain ⟨hn, hr, hv⟩ := h
    have hb : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
    change Active (if r = 1 then _ else _)
    split
    · exact ⟨hn, by omega, by decide⟩
    · exact ⟨hn, by omega, by omega⟩
  | length r v =>
    obtain ⟨hn, hr, hv⟩ := h
    have hb : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
    change Active (if r = 1 then _ else _)
    split
    · exact ⟨hn, by omega⟩
    · exact ⟨hn, by omega, by omega⟩
  | payload r =>
    obtain ⟨hn, hr⟩ := h
    change Active (if r = 1 then _ else _)
    split
    · exact active_finish n hn
    · exact ⟨hn, by omega⟩
  | done => exact h
  | dead => exact h

/-- Every prefix of a scan satisfies the invariant. -/
theorem active_foldl (w : List Bool) : ∀ s, Active s → Active (w.foldl step s) :=
  List.rec (fun _ h ↦ h) (fun b _ ih s h ↦ ih (step s b) (active_step s b h)) w

/-- The scanner starts and remains in an active or terminal state. -/
theorem scan_active (w : List Bool) : Active (scan w) :=
  active_foldl w (.tree, 1) (show 0 < 1 by decide)

/-- An incomplete raw payload stays in the payload phase. -/
theorem foldl_payload_short (w : List Bool) : ∀ r n, w.length < r →
    w.foldl step (.payload r, n) = (.payload (r - w.length), n) := by
  refine List.rec ?_ ?_ w
  · intro r n _
    rfl
  · intro b bs ih r n h
    have hr : r ≠ 1 := by simp only [List.length_cons] at h; omega
    simp only [List.foldl_cons, step, if_neg hr]
    rw [ih (r - 1) n (by simp only [List.length_cons] at h; omega)]
    congr 2
    simp only [List.length_cons]
    omega

/-- Consuming a complete nonempty raw payload completes one leaf. -/
theorem foldl_payload (w : List Bool) : ∀ n, w ≠ [] →
    w.foldl step (.payload w.length, n) = finish n := by
  refine List.rec ?_ ?_ w
  · intro n h
    exact (h rfl).elim
  · intro b bs ih n _
    cases bs with
    | nil => rfl
    | cons c cs =>
      simp only [List.length_cons, List.foldl_cons, step,
        show cs.length + 1 + 1 ≠ 1 by omega, ↓reduceIte]
      exact ih n (by intro h; cases h)

/-- A completed scanner with no further input remains completed. -/
theorem foldl_done (w : List Bool) (n : ℕ) :
    (w.foldl step (.done, n)).1 = .done ↔ w = [] := by
  have hd (bs : List Bool) : bs.foldl step (.dead, n) = (.dead, n) :=
    List.rec rfl (fun _ _ ih ↦ ih) bs
  cases w with
  | nil => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | cons b bs =>
    change (bs.foldl step (.dead, n)).1 = .done ↔ b :: bs = []
    rw [hd]
    constructor <;> intro h <;> cases h

/-- Acceptance after a declared payload supplies exactly that many raw bits and a suffix. -/
theorem payload_of_accept (w : List Bool) (m n : ℕ)
    (h : (w.foldl step (if m = 0 then finish n else (.payload m, n))).1 = .done) :
    ∃ s rest, s.length = m ∧ w = s ++ rest ∧ (rest.foldl step (finish n)).1 = .done := by
  by_cases hm : m = 0
  · subst m
    exact ⟨[], w, rfl, rfl, h⟩
  · rw [if_neg hm] at h
    by_cases hl : m ≤ w.length
    · have hs : (w.take m).length = m := List.length_take_of_le hl
      have hne : w.take m ≠ [] := by
        intro he
        rw [he] at hs
        exact hm hs.symm
      refine ⟨w.take m, w.drop m, hs, (List.take_append_drop m w).symm, ?_⟩
      have hf := foldl_payload (w.take m) n hne
      rw [hs] at hf
      rw [← List.take_append_drop m w, List.foldl_append, hf] at h
      exact h
    · rw [foldl_payload_short w m n (by omega)] at h
      cases h

/-- One input bit introduces at most one additional pending subtree. -/
theorem step_pending_le (s : State) (b : Bool) : (step s b).2 ≤ s.2 + 1 := by
  have hf (n : ℕ) : (finish n).2 ≤ n + 1 := by
    unfold finish
    split <;> dsimp only <;> omega
  rcases s with ⟨m, n⟩
  cases m <;> cases b <;> simp only [step] <;>
    first | exact Nat.le_refl _ | exact Nat.le_succ _ |
      (split <;> first | exact hf n | exact Nat.le_succ _)

/-- Pending subtrees are bounded by the initial count and the number of bits read. -/
theorem foldl_pending_le (w : List Bool) : ∀ s,
    (w.foldl step s).2 ≤ s.2 + w.length := by
  refine List.rec ?_ ?_ w
  · intro s
    exact Nat.le_refl _
  · intro b bs ih s
    have h := ih (step s b)
    have hb := step_pending_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The unary structural counter uses at most one plus the input length. -/
theorem scan_pending_le (w : List Bool) : (scan w).2 ≤ w.length + 1 := by
  have h := foldl_pending_le w (.tree, 1)
  change (scan w).2 ≤ 1 + w.length at h
  omega

end Geb.BitTree.Elias.Scanner
