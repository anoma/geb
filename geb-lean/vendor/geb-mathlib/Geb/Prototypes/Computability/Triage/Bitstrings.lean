/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Decode
public import Geb.Prototypes.Computability.Triage.Simulation
public import Geb.Prototypes.Computability.Triage.Encode

set_option doc.verso true in
/-!
# A total bitstring interface to one triage step

Malformed input, a terminal value, and a successful step are distinct outcomes.
The successful output is again a recognized binary-tree bitstring representing
a triage expression. The interface performs one step, never normalization.

## Main definitions

* {lit}`Outcome` distinguishes invalid input, a value, and a successor bitstring.
* {lit}`reduce` validates, takes one step, and serializes its successor.

## Main statements

* {lit}`reduce_encode` identifies the interface with the expression semantics.
* {lit}`reduce_next_sound` provides the represented source, target, and single-step proof.
* {lit}`reduce_value_iff` identifies precisely the terminal values.
* {lit}`reduce_next_length_le` proves the concrete factor-two output bound.

## Tags

tree calculus, bitstring, reduction, correctness, progress
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Triage

/-- A total reduction interface keeps malformed input distinct from normal forms. -/
inductive Outcome
  | invalid
  | value
  | next (word : List Bool)
  deriving DecidableEq, Repr

/-- Validate an input and perform exactly one branch-first step if it is an application. -/
def reduce (w : List Bool) : Outcome :=
  match decode w with
  | none => .invalid
  | some e => match Machine.execute e with
    | none => .value
    | some e' => .next e'.encodeFast

/-- On an encoded expression the bitstring operation is exactly the small-step operation. -/
theorem reduce_encode (e : Expr) : reduce e.encode =
    match step e with
    | none => .value
    | some e' => .next e'.encode := by simp [reduce]

/-- Invalid input means exactly failure of triage recognition. -/
theorem reduce_invalid_iff (w : List Bool) : reduce w = .invalid ↔ recognize w = false := by
  cases hd : decode w with
  | none => simp [reduce, recognize, hd]
  | some e => cases hs : step e <;> simp [reduce, recognize, hd, hs]

/-- A terminal result means that the input is the encoding of a value. -/
theorem reduce_value_iff (w : List Bool) :
    reduce w = .value ↔ ∃ v : Value, (Expr.value v).encode = w := by
  constructor
  · intro h
    cases hd : decode w with
    | none => simp [reduce, hd] at h
    | some e =>
      cases hs : step e with
      | some e' => simp [reduce, hd, hs] at h
      | none =>
        obtain ⟨v, rfl⟩ := (step_eq_none_iff e).mp hs
        exact ⟨v, encode_of_decode hd⟩
  · rintro ⟨v, rfl⟩
    simp [reduce]

/-- A returned successor represents exactly one valid contextual contraction. -/
theorem reduce_next_sound {w w' : List Bool} (h : reduce w = .next w') :
    ∃ e e' : Expr, e.encode = w ∧ e'.encode = w' ∧ step e = some e' ∧ Step e e' := by
  cases hd : decode w with
  | none => simp [reduce, hd] at h
  | some e =>
    cases hs : step e with
    | none => simp [reduce, hd, hs] at h
    | some e' =>
      have he : e'.encode = w' := by simpa [reduce, hd, hs] using h
      exact ⟨e, e', encode_of_decode hd, he, hs, step_sound e e' hs⟩

/-- A successful successor is itself a recognized triage expression. -/
theorem recognize_of_reduce_next {w w' : List Bool} (h : reduce w = .next w') :
    recognize w' = true := by
  obtain ⟨_, e', _, he', _, _⟩ := reduce_next_sound h
  exact (recognize_iff w').mpr ⟨e', he'⟩

/-- The actual successor bitstring is at most twice the input length. -/
theorem reduce_next_length_le {w w' : List Bool} (h : reduce w = .next w') :
    w'.length ≤ 2 * w.length := by
  obtain ⟨e, e', rfl, rfl, hs, _⟩ := reduce_next_sound h
  simpa only [Expr.length_encode] using step_bits_le e e' hs

end Geb.Triage
