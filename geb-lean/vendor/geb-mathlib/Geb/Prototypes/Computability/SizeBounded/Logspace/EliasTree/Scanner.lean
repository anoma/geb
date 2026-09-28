/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Elias.Scanner
import Mathlib.Tactic.SplitIfs

set_option doc.verso true in
/-!
# The Elias-length scanner on monotone counters

The streaming recognizer {name}`Geb.BitTree.Elias.Scanner.step` of the
Elias-length tree encoding keeps a pending-subtree count that rises at a fork
and falls at a completed leaf, and in each header phase a remaining count that
falls per bit while a value doubles. The successor-free subalgebra represents a
number by an end segment of the input, which can be shortened but not
lengthened, so every counter it keeps must be monotone. The scanner is
therefore restated here on monotone counters, as the binary-counter machine
{lit}`Geb.BitTree.EliasBinary.machine` keeps them: the forks and the completed
leaves in place of the pending count, whose equality is the completion of the
root; in a header, a width and a count rising towards it in place of a
remaining count, and a value that doubles and rises by a bit. The phase after
a leaf tag, before any zero of the run, is distinguished from the run itself,
so that the empty payload is recognized without a comparison against zero.

The projection {lit}`toState` reads the scanner's state off the counters, and
commutes with one bit under the invariant {lit}`Valid`, which bounds every
counter by the number of bits read: the bounds are what the subalgebra's
comparisons of end segments require.

# Main definitions

* {lit}`Phase`, {lit}`Counters` — the phases and the counters.
* {lit}`finishC`, {lit}`advance`, {lit}`init`, {lit}`run` — a completed leaf,
  one bit, the initial counters, and a word.
* {lit}`modeOf`, {lit}`toState` — the scanner's mode and state read off the
  counters.
* {lit}`Valid` — the counters are bounded by the number of bits read.

# Main statements

* {lit}`toState_advance` — the projection commutes with one bit.
* {lit}`valid_advance`, {lit}`valid_init` — the invariant is preserved.
* {lit}`toState_foldl`, {lit}`toState_run` — the projection commutes with a
  word.
* {lit}`run_phase_done_iff` — the counters end in the completed phase exactly
  when the scanner does.

# References

* \[Elias1975\]
* \[Kristiansen2005\]

# Tags

Elias delta code, streaming recognizer, monotone counter, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.EliasTree

open Geb.BitTree.Elias.Scanner (Mode State step finish scan)

public section

/-- The phases: the tree tags; the bit after a leaf tag; the zero run of a
delta header; the size, length and payload fields; and the two terminal
phases. -/
inductive Phase where
  | tree
  | header
  | zeros
  | size
  | length
  | payload
  | done
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- The monotone counters. The width is the zero run during it, the field's
width during the size field, and the bound the count rises to during the
length field and the payload. -/
@[ext] structure Counters where
  /-- The phase. -/
  phase : Phase
  /-- The number of fork tags read. -/
  forks : ℕ
  /-- The number of leaves completed. -/
  leaves : ℕ
  /-- The zero run, the field width, or the bound of the count. -/
  width : ℕ
  /-- The bits of the current field read, from zero in the size field and
  from one in the length field and the payload. -/
  count : ℕ
  /-- The value of the field read so far, from one. -/
  value : ℕ
  deriving DecidableEq, Repr, Inhabited

attribute [nolint unusedArguments] instReprCounters.repr

/-- A completed leaf: one more leaf, and the completed phase when it closes the
last pending subtree, which is when the leaves counted so far equal the
forks. -/
@[expose] def finishC (x : Counters) : Counters :=
  { x with phase := if x.forks = x.leaves then .done else .tree, leaves := x.leaves + 1 }

/-- One bit. In the size and length fields the value takes the bit; the count
rises, and on reaching the width the next field opens with the value as its
bound and the count at one. -/
@[expose] def advance (x : Counters) (b : Bool) : Counters :=
  match x.phase, b with
  | .tree, true => { x with forks := x.forks + 1 }
  | .tree, false => { x with phase := .header }
  | .header, true => finishC x
  | .header, false => { x with phase := .zeros, width := 1 }
  | .zeros, false => { x with width := x.width + 1 }
  | .zeros, true => { x with phase := .size, count := 0, value := 1 }
  | .size, b =>
    if x.count + 1 = x.width then
      { x with phase := .length, width := 2 * x.value + b.toNat, count := 1, value := 1 }
    else { x with count := x.count + 1, value := 2 * x.value + b.toNat }
  | .length, b =>
    if x.count + 1 = x.width then
      { x with
        phase := .payload
        width := 2 * x.value + b.toNat
        count := 1
        value := 2 * x.value + b.toNat }
    else { x with count := x.count + 1, value := 2 * x.value + b.toNat }
  | .payload, _ =>
    if x.count + 1 = x.width then finishC { x with count := x.count + 1 }
    else { x with count := x.count + 1 }
  | .done, _ => { x with phase := .dead }
  | .dead, _ => x

/-- The initial counters: the tree phase with every counter at zero. -/
@[expose] def init : Counters := ⟨.tree, 0, 0, 0, 0, 0⟩

/-- The counters after a word. -/
@[expose] def run (w : List Bool) : Counters := w.foldl advance init

/-- The scanner's mode read off a phase and the counters of its field: a
remaining count is the width less the count. -/
@[expose] def modeOf : Phase → ℕ → ℕ → ℕ → Mode
  | .tree, _, _, _ => .tree
  | .header, _, _, _ => .zeros 0
  | .zeros, z, _, _ => .zeros z
  | .size, z, c, v => .size (z - c) v
  | .length, z, c, v => .length (z - c) v
  | .payload, z, c, _ => .payload (z - c)
  | .done, _, _, _ => .done
  | .dead, _, _, _ => .dead

/-- The scanner's state read off the counters: the mode of the phase, and one
plus the forks less the leaves as the pending count. -/
@[expose] def toState (x : Counters) : State :=
  (modeOf x.phase x.width x.count x.value, x.forks + 1 - x.leaves)

/-- The counters after {lit}`k` bits are bounded by {lit}`k`: the leaves by
the forks and the forks by the bits; a zero run by the bits before it; the
count below the width; and in the length field and the payload, the count
three below the bits, which places the bit after the count below the word's
length. -/
@[expose] def Valid (k : ℕ) (x : Counters) : Prop :=
  match x.phase with
  | .tree => x.leaves ≤ x.forks ∧ x.forks ≤ k
  | .header => x.leaves ≤ x.forks ∧ x.forks ≤ k ∧ 1 ≤ k
  | .zeros => x.leaves ≤ x.forks ∧ x.forks ≤ k ∧ 1 ≤ x.width ∧ x.width + 1 ≤ k
  | .size =>
    x.leaves ≤ x.forks ∧ x.forks ≤ k ∧ x.count < x.width ∧ x.width ≤ k ∧ 3 ≤ k ∧ 1 ≤ x.value
  | .length => x.leaves ≤ x.forks ∧ x.forks ≤ k ∧ x.count < x.width ∧ x.count + 3 ≤ k ∧ 1 ≤ x.value
  | .payload => x.leaves ≤ x.forks ∧ x.forks ≤ k ∧ x.count < x.width ∧ x.count + 3 ≤ k
  | .done => True
  | .dead => True

/-- The projection commutes with one bit on valid counters. -/
theorem toState_advance (k : ℕ) (x : Counters) (b : Bool) (h : Valid k x) :
    toState (advance x b) = step (toState x) b := by
  rcases x with ⟨ph, f, l, z, c, v⟩
  cases ph <;> cases b <;> simp only [Valid] at h
  case tree.false => rfl
  case tree.true =>
    change (Mode.tree, f + 1 + 1 - l) = (Mode.tree, f + 1 - l + 1)
    rw [show f + 1 + 1 - l = f + 1 - l + 1 by omega]
  case header.false => rfl
  case header.true =>
    change (modeOf (if f = l then .done else .tree) z c v, f + 1 - (l + 1)) = finish (f + 1 - l)
    by_cases hf : f = l
    · rw [if_pos hf, finish, if_pos (show f + 1 - l = 1 by omega),
        show f + 1 - (l + 1) = 0 by omega]
      rfl
    · rw [if_neg hf, finish, if_neg (show ¬f + 1 - l = 1 by omega),
        show f + 1 - (l + 1) = f + 1 - l - 1 by omega]
      rfl
  case zeros.false => rfl
  case zeros.true =>
    change (Mode.size (z - 0) 1, f + 1 - l) =
      if z = 0 then finish (f + 1 - l) else (.size z 1, f + 1 - l)
    rw [if_neg (show ¬z = 0 by omega), Nat.sub_zero]
  case size.false =>
    change toState (if c + 1 = z then _ else _) = if z - c = 1 then _ else _
    by_cases he : c + 1 = z
    · rw [if_pos he, if_pos (show z - c = 1 by omega), Nat.bit_val]
      rfl
    · rw [if_neg he, if_neg (show ¬z - c = 1 by omega), Nat.bit_val]
      change (Mode.size (z - (c + 1)) (2 * v + 0), f + 1 - l) =
        (Mode.size (z - c - 1) (2 * v + 0), f + 1 - l)
      rw [show z - (c + 1) = z - c - 1 by omega]
  case size.true =>
    change toState (if c + 1 = z then _ else _) = if z - c = 1 then _ else _
    by_cases he : c + 1 = z
    · rw [if_pos he, if_pos (show z - c = 1 by omega), Nat.bit_val]
      rfl
    · rw [if_neg he, if_neg (show ¬z - c = 1 by omega), Nat.bit_val]
      change (Mode.size (z - (c + 1)) (2 * v + 1), f + 1 - l) =
        (Mode.size (z - c - 1) (2 * v + 1), f + 1 - l)
      rw [show z - (c + 1) = z - c - 1 by omega]
  case length.false =>
    change toState (if c + 1 = z then _ else _) = if z - c = 1 then _ else _
    by_cases he : c + 1 = z
    · rw [if_pos he, if_pos (show z - c = 1 by omega), Nat.bit_val]
      rfl
    · rw [if_neg he, if_neg (show ¬z - c = 1 by omega), Nat.bit_val]
      change (Mode.length (z - (c + 1)) (2 * v + 0), f + 1 - l) =
        (Mode.length (z - c - 1) (2 * v + 0), f + 1 - l)
      rw [show z - (c + 1) = z - c - 1 by omega]
  case length.true =>
    change toState (if c + 1 = z then _ else _) = if z - c = 1 then _ else _
    by_cases he : c + 1 = z
    · rw [if_pos he, if_pos (show z - c = 1 by omega), Nat.bit_val]
      rfl
    · rw [if_neg he, if_neg (show ¬z - c = 1 by omega), Nat.bit_val]
      change (Mode.length (z - (c + 1)) (2 * v + 1), f + 1 - l) =
        (Mode.length (z - c - 1) (2 * v + 1), f + 1 - l)
      rw [show z - (c + 1) = z - c - 1 by omega]
  case done.false | done.true | dead.false | dead.true => rfl
  all_goals
    change toState (if c + 1 = z then _ else _) = if z - c = 1 then _ else _
    by_cases he : c + 1 = z
    · rw [if_pos he, if_pos (show z - c = 1 by omega)]
      change (modeOf (if f = l then .done else .tree) z (c + 1) v, f + 1 - (l + 1)) =
        finish (f + 1 - l)
      by_cases hf : f = l
      · rw [if_pos hf, finish, if_pos (show f + 1 - l = 1 by omega),
          show f + 1 - (l + 1) = 0 by omega]
        rfl
      · rw [if_neg hf, finish, if_neg (show ¬f + 1 - l = 1 by omega),
          show f + 1 - (l + 1) = f + 1 - l - 1 by omega]
        rfl
    · rw [if_neg he, if_neg (show ¬z - c = 1 by omega)]
      change (Mode.payload (z - (c + 1)), f + 1 - l) = (Mode.payload (z - c - 1), f + 1 - l)
      rw [show z - (c + 1) = z - c - 1 by omega]

/-- One bit preserves the invariant, at one more bit read. -/
theorem valid_advance (k : ℕ) (x : Counters) (b : Bool) (h : Valid k x) :
    Valid (k + 1) (advance x b) := by
  rcases x with ⟨ph, f, l, z, c, v⟩
  cases ph <;> cases b <;> simp only [Valid] at h <;> simp only [advance, finishC] <;>
    (try split_ifs) <;> simp only [Valid, Bool.toNat_false, Bool.toNat_true] <;>
    (repeat' apply And.intro) <;> first | trivial | omega

/-- The initial counters are valid at no bits read. -/
theorem valid_init : Valid 0 init := ⟨Nat.le_refl 0, Nat.le_refl 0⟩

/-- The projection commutes with a word: after the word, the counters are valid
at the bits read and project to the scanner's state. -/
theorem toState_foldl (p : List Bool) : ∀ (k : ℕ) (x : Counters), Valid k x →
    Valid (k + p.length) (p.foldl advance x) ∧
      toState (p.foldl advance x) = p.foldl step (toState x) :=
  List.rec (fun k x h ↦ ⟨h, rfl⟩)
    (fun b p ih k x h ↦ by
      obtain ⟨hv, he⟩ := ih (k + 1) (advance x b) (valid_advance k x b h)
      rw [List.foldl_cons, List.foldl_cons, List.length_cons, ← toState_advance k x b h,
        show k + (p.length + 1) = k + 1 + p.length by omega]
      exact ⟨hv, he⟩) p

/-- The counters after a word project to the scanner's state on it. -/
theorem toState_run (w : List Bool) : toState (run w) = scan w :=
  (toState_foldl w 0 init valid_init).2

/-- The counters end in the completed phase exactly when the scanner does. -/
theorem run_phase_done_iff (w : List Bool) : (run w).phase = .done ↔ (scan w).1 = .done := by
  rw [← toState_run]
  rcases run w with ⟨ph, f, l, z, c, v⟩
  cases ph <;> simp [toState, modeOf]

end

end Geb.SizeBounded.Logspace.EliasTree
