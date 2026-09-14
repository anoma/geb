/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Size

set_option doc.verso true

/-!
# Canonical positive binary words

Positive binary integers have a leading one. Removing that bit identifies positive integers
with arbitrary finite bitstrings, read from most to least significant bit.

## Main definitions

* {lit}`payload` removes the leading one from a positive integer's binary representation.
* {lit}`fromPayload` restores the implicit leading one and reads the remaining digits.
* {lit}`readFixed` reads a fixed number of such remaining digits.

## Main statements

* {lit}`fromPayload_payload` and {lit}`payload_fromPayload` give the two inverse laws.
* {lit}`readFixed_eq_some` characterizes a successful fixed-width read.

## Tags

binary representation, prefix code, parsing
-/

@[expose] public section

namespace Geb.BitTree.Elias

/-- The digits after the leading one, from most to least significant. -/
def payload (n : ℕ) : List Bool := n.bits.reverse.tail

/-- Read a most-significant-first payload with an implicit leading one. -/
def fromPayload (bs : List Bool) : ℕ := bs.foldl (fun n b ↦ Nat.bit b n) 1

/-- A positive binary integer begins with one in most-significant-first order. -/
theorem reverse_bits_cons (n : ℕ) : n ≠ 0 → ∃ bs, n.bits.reverse = true :: bs := by
  apply Nat.binaryRec' (motive := fun n ↦ n ≠ 0 → ∃ bs, n.bits.reverse = true :: bs)
    ?_ ?_ n
  · intro h
    exact (h rfl).elim
  · intro b k hk ih _
    rw [Nat.bits_append_bit k b hk, List.reverse_cons]
    cases k with
    | zero =>
      have hb : b = true := hk rfl
      subst b
      exact ⟨[], rfl⟩
    | succ k =>
      obtain ⟨bs, hbs⟩ := ih (Nat.succ_ne_zero k)
      exact ⟨bs ++ [b], by rw [hbs]; rfl⟩

/-- The leading one and payload reconstruct a positive integer's binary digits. -/
theorem reverse_bits_eq (n : ℕ) (hn : n ≠ 0) : n.bits.reverse = true :: payload n := by
  obtain ⟨bs, hbs⟩ := reverse_bits_cons n hn
  simp only [payload, hbs, List.tail_cons]

/-- Reading the least-significant-first representation returns its original number. -/
theorem foldr_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  apply Nat.binaryRec' (motive := fun n ↦ n.bits.foldr Nat.bit 0 = n) ?_ ?_ n
  · rfl
  · intro b k hk ih
    rw [Nat.bits_append_bit k b hk, List.foldr_cons, ih]

/-- Restoring the implicit leading one recovers the positive integer. -/
theorem fromPayload_payload (n : ℕ) (hn : n ≠ 0) : fromPayload (payload n) = n := by
  have h : n.bits.reverse.foldl (fun n b ↦ Nat.bit b n) 0 = n := by
    rw [List.foldl_reverse]
    exact foldr_bits n
  rw [reverse_bits_eq n hn] at h
  exact h

/-- Appending a binary digit preserves positivity. -/
theorem bit_pos (b : Bool) (n : ℕ) (hn : 0 < n) : 0 < Nat.bit b n := by
  rw [Nat.bit_val]
  omega

/-- Appending digits preserves positivity and extends the canonical binary representation. -/
theorem foldl_bits (bs : List Bool) : ∀ n, 0 < n →
    0 < bs.foldl (fun n b ↦ Nat.bit b n) n ∧
      (bs.foldl (fun n b ↦ Nat.bit b n) n).bits = bs.reverse ++ n.bits :=
  List.rec (fun n hn ↦ ⟨hn, rfl⟩) (fun b bs ih n hn ↦ by
    obtain ⟨hp, he⟩ := ih (Nat.bit b n) (bit_pos b n hn)
    refine ⟨hp, ?_⟩
    rw [List.foldl_cons, he, Nat.bits_append_bit n b (by omega), List.reverse_cons]
    simp only [List.append_assoc, List.singleton_append]) bs

/-- Restoring the leading one always gives a positive number. -/
theorem fromPayload_pos (bs : List Bool) : 0 < fromPayload bs :=
  (foldl_bits bs 1 (by decide)).1

/-- The reconstructed number has exactly the prescribed digits after its leading one. -/
theorem payload_fromPayload (bs : List Bool) : payload (fromPayload bs) = bs := by
  have he := (foldl_bits bs 1 (by decide)).2
  simp only [payload, fromPayload, he, List.reverse_append, List.reverse_reverse,
    Nat.one_bits, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.tail_cons]

/-- A reconstructed payload has one extra bit for its leading one. -/
theorem size_fromPayload (bs : List Bool) : (fromPayload bs).size = bs.length + 1 := by
  rw [← Nat.size_eq_bits_len]
  change (bs.foldl (fun n b ↦ Nat.bit b n) 1).bits.length = _
  rw [(foldl_bits bs 1 (by decide)).2,
    List.length_append, List.length_reverse, Nat.one_bits]
  rfl

/-- Dropping the leading bit subtracts one from the binary size. -/
theorem length_payload (n : ℕ) : (payload n).length = n.size - 1 := by
  simp only [payload, List.length_tail, List.length_reverse, Nat.size_eq_bits_len]

/-- Positive numbers have positive binary size. -/
theorem size_pos (n : ℕ) (hn : n ≠ 0) : 0 < n.size := by
  have he := size_fromPayload (payload n)
  rw [fromPayload_payload n hn] at he
  omega

/-- Read a fixed-width payload, retaining the unconsumed suffix. -/
def readFixed (k : ℕ) (w : List Bool) : Option (ℕ × List Bool) :=
  if k ≤ w.length then some (fromPayload (w.take k), w.drop k) else none

/-- Reading exactly a payload's length recovers its value and leaves the suffix untouched. -/
theorem readFixed_append (bs rest : List Bool) :
    readFixed bs.length (bs ++ rest) = some (fromPayload bs, rest) := by
  simp only [readFixed, List.length_append, Nat.le_add_right, ↓reduceIte,
    List.take_left, List.drop_left]

/-- A successful fixed-width read is precisely a canonical payload followed by its suffix. -/
theorem readFixed_eq_some (k : ℕ) (w : List Bool) (n : ℕ) (rest : List Bool)
    (h : readFixed k w = some (n, rest)) :
    n ≠ 0 ∧ n.size = k + 1 ∧ w = payload n ++ rest := by
  unfold readFixed at h
  split at h
  next hk =>
    have he := Option.some.inj h
    have hn : fromPayload (w.take k) = n := congrArg Prod.fst he
    have hr : w.drop k = rest := congrArg Prod.snd he
    refine ⟨?_, ?_, ?_⟩
    · have hp := fromPayload_pos (w.take k)
      omega
    · rw [← hn, size_fromPayload, List.length_take_of_le hk]
    · rw [← hn, payload_fromPayload, ← hr, List.take_append_drop]
  next => contradiction

end Geb.BitTree.Elias
