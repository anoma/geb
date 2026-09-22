/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Elias.Code
public import Mathlib.Data.Nat.Size

set_option doc.verso true in
/-!
# Length-prefixed binary numerals

A natural number is coded by the gamma code of one more than its binary
length followed by its bits, least significant first, with no bit above the
leading one. The code is a prefix code, and the bits read in the order a
lockstep scan with a carry compares or adds numerals, and in the order a
scan reads a numeral into a counter by adding a doubling power to it. It
differs from the Elias delta code of {lit}`Geb.BitTree.Elias.encodeNat`, whose
payload omits the leading one and is most significant first, by one bit and
the order.

# Main definitions

* {lit}`natCode` — the code of a natural number.
* {lit}`fromBits`, {lit}`canonical` — the number with given bits, and the
  bit lists that are the bits of a number.
* {lit}`readBits`, {lit}`readNatCode` — a fixed number of bits, and one
  coded number, each with the unconsumed suffix.

# Main statements

* {lit}`fromBits_bits`, {lit}`bits_fromBits`, {lit}`canonical_bits` — the
  bits of a number are canonical and invert {lit}`fromBits`.
* {lit}`readNatCode_natCode_append` — the round-trip law with an arbitrary
  suffix.
* {lit}`readNatCode_eq_some` — a successful read identifies the code and the
  suffix.
* {lit}`natCode_injective` — the code is injective.

# References

* \[Elias1975\]

# Tags

binary numeral, prefix code, Elias gamma code
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.Numeral

open Geb.BitTree.Elias (encodeGamma readGamma)

public section

/-- The code of a natural number: the gamma code of one more than its binary
length, then its bits, least significant first. -/
@[expose] def natCode (n : ℕ) : List Bool := encodeGamma (n.size + 1) ++ n.bits

/-- The number with the given bits, least significant first. -/
@[expose] def fromBits (bs : List Bool) : ℕ := bs.foldr Nat.bit 0

/-- The bits of a number read back as the number. -/
theorem fromBits_bits (n : ℕ) : fromBits n.bits = n := Geb.BitTree.Elias.foldr_bits n

/-- A bit list is canonical when it does not end in {lit}`false`: the bit
lists that are the bits of a number. -/
@[expose] def canonical (bs : List Bool) : Bool := decide (bs.getLast? ≠ some false)

/-- The bits of a number are canonical. -/
theorem canonical_bits : ∀ n : ℕ, canonical n.bits = true :=
  Nat.binaryRec' (by decide) fun b n h ih ↦ by
    rw [Nat.bits_append_bit n b h]
    cases hb : n.bits with
    | nil =>
      have hn : n = 0 := by
        rw [← fromBits_bits n, hb]
        rfl
      rw [h hn]
      decide
    | cons c cs =>
      rw [hb] at ih
      unfold canonical at ih ⊢
      rw [List.getLast?_cons_cons]
      exact ih

/-- A nonempty canonical bit list reads back as a positive number. -/
theorem fromBits_ne_zero : ∀ bs : List Bool, bs ≠ [] → canonical bs = true → fromBits bs ≠ 0 :=
  List.rec (fun h _ ↦ (h rfl).elim) fun c cs ih _ hc ↦ by
    cases cs with
    | nil =>
      unfold canonical at hc
      rw [List.getLast?_singleton, decide_eq_true_iff] at hc
      cases c
      · exact (hc rfl).elim
      · decide
    | cons d ds =>
      have := ih (List.cons_ne_nil d ds) (by
        unfold canonical at hc ⊢
        rwa [List.getLast?_cons_cons] at hc)
      change Nat.bit c (fromBits (d :: ds)) ≠ 0
      rw [Nat.bit_val]
      omega

/-- The number with canonical bits has those bits. -/
theorem bits_fromBits : ∀ bs : List Bool, canonical bs = true → (fromBits bs).bits = bs :=
  List.rec (fun _ ↦ rfl) fun c cs ih hc ↦ by
    change (Nat.bit c (fromBits cs)).bits = c :: cs
    cases cs with
    | nil =>
      unfold canonical at hc
      rw [List.getLast?_singleton, decide_eq_true_iff] at hc
      cases c
      · exact (hc rfl).elim
      · change (Nat.bit true 0).bits = [true]
        rw [Nat.bits_append_bit 0 true fun _ ↦ rfl]
        rfl
    | cons d ds =>
      have hc' : canonical (d :: ds) = true := by
        unfold canonical at hc ⊢
        rwa [List.getLast?_cons_cons] at hc
      rw [Nat.bits_append_bit _ _ fun h ↦ absurd h (fromBits_ne_zero _ (List.cons_ne_nil d ds) hc'),
        ih hc']

/-- The length of a number's bits is its binary size. -/
theorem length_bits (n : ℕ) : n.bits.length = n.size := Nat.size_eq_bits_len n

/-- Read a fixed number of bits, retaining the unconsumed suffix. -/
@[expose] def readBits (k : ℕ) (w : List Bool) : Option (List Bool × List Bool) :=
  if k ≤ w.length then some (w.take k, w.drop k) else none

/-- Reading exactly a list's length recovers it and leaves the suffix. -/
theorem readBits_append (bs rest : List Bool) :
    readBits bs.length (bs ++ rest) = some (bs, rest) := by
  simp only [readBits, List.length_append, Nat.le_add_right, ↓reduceIte, List.take_left,
    List.drop_left]

/-- A successful read is a list of the given length followed by the suffix. -/
theorem readBits_eq_some (k : ℕ) (w bs rest : List Bool) (h : readBits k w = some (bs, rest)) :
    bs.length = k ∧ w = bs ++ rest := by
  unfold readBits at h
  split at h
  next hk =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨List.length_take_of_le hk, (List.take_append_drop k w).symm⟩
  next => cases h

/-- Read one coded number: the gamma code of one more than its length, that
many bits, canonical, and the suffix. -/
@[expose] def readNatCode (w : List Bool) : Option (ℕ × List Bool) :=
  (readGamma w).bind fun p ↦ (readBits (p.1 - 1) p.2).bind fun q ↦
    if canonical q.1 then some (fromBits q.1, q.2) else none

/-- A coded number reads back with its suffix intact. -/
theorem readNatCode_natCode_append (n : ℕ) (rest : List Bool) :
    readNatCode (natCode n ++ rest) = some (n, rest) := by
  rw [readNatCode, natCode, List.append_assoc,
    Geb.BitTree.Elias.readGamma_encodeGamma_append (n.size + 1) (Nat.succ_ne_zero _),
    Option.bind_some, Nat.add_sub_cancel, ← length_bits, readBits_append, Option.bind_some,
    canonical_bits, if_pos rfl, fromBits_bits]

/-- A successful read identifies the code and the suffix. -/
theorem readNatCode_eq_some (w : List Bool) (n : ℕ) (rest : List Bool)
    (h : readNatCode w = some (n, rest)) : w = natCode n ++ rest := by
  cases hg : readGamma w with
  | none => simp only [readNatCode, hg, Option.bind_none, reduceCtorEq] at h
  | some p =>
    rcases p with ⟨s, suffix⟩
    cases hb : readBits (s - 1) suffix with
    | none => simp only [readNatCode, hg, Option.bind_some, hb, Option.bind_none, reduceCtorEq] at h
    | some q =>
      rcases q with ⟨bs, rest'⟩
      simp only [readNatCode, hg, Option.bind_some, hb] at h
      by_cases hc : canonical bs = true
      · rw [if_pos hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hs, hw⟩ := Geb.BitTree.Elias.readGamma_eq_some w s suffix hg
        obtain ⟨hl, hsuf⟩ := readBits_eq_some (s - 1) suffix bs rest' hb
        rw [hw, hsuf, natCode, bits_fromBits bs hc, ← length_bits, bits_fromBits bs hc, hl,
          show s - 1 + 1 = s by omega, List.append_assoc]
      · rw [if_neg hc] at h
        cases h

/-- The code is injective. -/
theorem natCode_injective : Function.Injective natCode := by
  intro m n h
  have := readNatCode_natCode_append m []
  rw [h, readNatCode_natCode_append] at this
  exact (Prod.mk.inj (Option.some.inj this)).1.symm

end

end Geb.SizeBounded.Logspace.WTree.Numeral
