/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.CodeBits
import Geb.Prototypes.Computability.BitTree.Counter
import Mathlib.Util.CompileInductive -- shake: keep

set_option doc.verso true in
/-!
# Elias delta codes for natural numbers

The positive integer {lit}`n + 1` is encoded by the Elias delta code: the gamma code of its
binary size, followed by the remaining bits after its leading one. The gamma code prefixes
the binary representation by one zero for each bit after its leading one.
This is the delta code of Section V of \[Elias1975\], shifted to include zero.

## Main definitions

* {lit}`encodeNat` encodes a natural number.
* {lit}`readNat` decodes one number and retains its unconsumed suffix.

## Main statements

* {lit}`readNat_encodeNat_append` is the roundtrip law with an arbitrary suffix.
* {lit}`readNat_eq_some` proves that successful decoding identifies a canonical prefix.
* {lit}`length_encodeNat` gives the exact length.
* {lit}`length_encodeNat_le` bounds the length by three times the binary size.

## References

* \[Elias1975\]

## Tags

Elias delta code, Elias gamma code, prefix code, binary encoding
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.Elias

/-- Read the number of zeros preceding the next one, failing if there is no one. -/
def readZeros : List Bool → Option (ℕ × List Bool) :=
  List.rec none fun b bs next ↦
    if b then some (0, bs) else next.map fun p ↦ (p.1 + 1, p.2)

/-- One recursive clause of the zero-prefix reader. -/
theorem readZeros_cons (b : Bool) (bs : List Bool) :
    readZeros (b :: bs) =
      if b then some (0, bs) else (readZeros bs).map fun p ↦ (p.1 + 1, p.2) := rfl

/-- A unary length prefix reads back with its suffix intact. -/
theorem readZeros_append (k : ℕ) (rest : List Bool) :
    readZeros (List.replicate k false ++ true :: rest) = some (k, rest) := by
  apply Nat.rec (motive := fun k ↦
    readZeros (List.replicate k false ++ true :: rest) = some (k, rest)) ?_ ?_ k
  · rfl
  · intro k ih
    rw [List.replicate_succ, List.cons_append, readZeros_cons]
    simp only [Bool.false_eq_true, ↓reduceIte, ih, Option.map_some]

/-- Successful zero-prefix parsing identifies the exact consumed prefix. -/
theorem readZeros_eq_some (w : List Bool) : ∀ k rest,
    readZeros w = some (k, rest) → w = List.replicate k false ++ true :: rest :=
  List.rec
    (fun k rest h ↦ by cases h)
    (fun b bs ih k rest h ↦ by
      cases b with
      | true =>
        change some (0, bs) = some (k, rest) at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rfl
      | false =>
        rw [readZeros_cons] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hx : readZeros bs with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at h
        | some p =>
          rcases p with ⟨j, suffix⟩
          rw [hx] at h
          have he := Option.some.inj h
          have hk := congrArg Prod.fst he
          have hr := congrArg Prod.snd he
          change j + 1 = k at hk
          change suffix = rest at hr
          rw [← hk, ← hr, List.replicate_succ, List.cons_append, ih j suffix hx]) w

/-- Gamma code of a positive integer; zero is assigned the same word as one. -/
def encodeGamma (n : ℕ) : List Bool :=
  List.replicate (n.size - 1) false ++ true :: payload n

/-- Read one gamma-coded positive integer. -/
def readGamma (w : List Bool) : Option (ℕ × List Bool) :=
  (readZeros w).bind fun p ↦ readFixed p.1 p.2

/-- A gamma-coded positive integer reads back with its suffix intact. -/
theorem readGamma_encodeGamma_append (n : ℕ) (hn : n ≠ 0) (rest : List Bool) :
    readGamma (encodeGamma n ++ rest) = some (n, rest) := by
  simp only [readGamma, encodeGamma, List.append_assoc, List.cons_append, readZeros_append,
    Option.bind_some]
  rw [← length_payload, readFixed_append, fromPayload_payload n hn]

/-- Successful gamma decoding identifies a positive number and its exact canonical prefix. -/
theorem readGamma_eq_some (w : List Bool) (n : ℕ) (rest : List Bool)
    (h : readGamma w = some (n, rest)) : n ≠ 0 ∧ w = encodeGamma n ++ rest := by
  cases hx : readZeros w with
  | none => simp only [readGamma, hx, Option.bind_none, reduceCtorEq] at h
  | some p =>
    rcases p with ⟨k, suffix⟩
    have hf : readFixed k suffix = some (n, rest) := by
      simpa only [readGamma, hx, Option.bind_some] using h
    obtain ⟨hn, hs, hw⟩ := readFixed_eq_some k suffix n rest hf
    refine ⟨hn, ?_⟩
    have hl : n.size - 1 = k := by omega
    rw [readZeros_eq_some w k suffix hx, hw, encodeGamma, hl]
    simp only [List.append_assoc, List.cons_append]

/-- Elias delta code of the positive integer one greater than the argument. -/
def encodeNat (n : ℕ) : List Bool := encodeGamma (n + 1).size ++ payload (n + 1)

/-- Decode one shifted Elias delta code and retain the remaining input. -/
def readNat (w : List Bool) : Option (ℕ × List Bool) :=
  (readGamma w).bind fun p ↦
    (readFixed (p.1 - 1) p.2).bind fun q ↦ some (q.1 - 1, q.2)

/-- Encoding followed by decoding recovers both the number and any appended suffix. -/
theorem readNat_encodeNat_append (n : ℕ) (rest : List Bool) :
    readNat (encodeNat n ++ rest) = some (n, rest) := by
  have hp := size_pos (n + 1) (by omega)
  simp only [readNat, encodeNat, List.append_assoc]
  rw [readGamma_encodeGamma_append (n + 1).size (by omega)]
  simp only [Option.bind_some]
  rw [← length_payload, readFixed_append, fromPayload_payload (n + 1) (by omega)]
  rfl

/-- A successfully decoded word has exactly the canonical code as its consumed prefix. -/
theorem readNat_eq_some (w : List Bool) (n : ℕ) (rest : List Bool)
    (h : readNat w = some (n, rest)) : w = encodeNat n ++ rest := by
  cases hg : readGamma w with
  | none => simp only [readNat, hg, Option.bind_none, reduceCtorEq] at h
  | some p =>
    rcases p with ⟨k, suffix⟩
    obtain ⟨hk, hw⟩ := readGamma_eq_some w k suffix hg
    cases hf : readFixed (k - 1) suffix with
    | none => simp only [readNat, hg, hf, Option.bind_some, Option.bind_none, reduceCtorEq] at h
    | some p =>
      rcases p with ⟨m, tail⟩
      obtain ⟨hm, hs, ht⟩ := readFixed_eq_some (k - 1) suffix m tail hf
      have he : (m - 1, tail) = (n, rest) := Option.some.inj (by
        simpa only [readNat, hg, hf, Option.bind_some] using h)
      have hn := congrArg Prod.fst he
      have hr := congrArg Prod.snd he
      change m - 1 = n at hn
      change tail = rest at hr
      have hm' : m = n + 1 := by omega
      rw [hm'] at hs
      have hk' : k = (n + 1).size := by omega
      rw [hw, ht, hm', hk', hr, encodeNat, List.append_assoc]

/-- Success is equivalent to having the canonical encoding as a prefix. -/
theorem readNat_eq_some_iff (w : List Bool) (n : ℕ) (rest : List Bool) :
    readNat w = some (n, rest) ↔ w = encodeNat n ++ rest :=
  ⟨readNat_eq_some w n rest, fun h ↦ h ▸ readNat_encodeNat_append n rest⟩

/-- Both the encoded value and the end of its code are uniquely determined. -/
theorem encodeNat_append_injective (n m : ℕ) (s t : List Bool)
    (h : encodeNat n ++ s = encodeNat m ++ t) : n = m ∧ s = t := by
  have he := congrArg readNat h
  rw [readNat_encodeNat_append, readNat_encodeNat_append] at he
  exact Prod.mk.inj (Option.some.inj he)

/-- Distinct natural numbers have distinct delta codes. -/
theorem encodeNat_injective : Function.Injective encodeNat := by
  intro n m h
  exact (encodeNat_append_injective n m [] [] (by simpa using h)).1

/-- Gamma coding adds one zero for each bit after the leading one. -/
theorem length_encodeGamma (n : ℕ) :
    (encodeGamma n).length = 2 * (n.size - 1) + 1 := by
  simp only [encodeGamma, List.length_append, List.length_replicate, List.length_cons,
    length_payload]
  omega

/-- The exact length of the shifted Elias delta code. -/
theorem length_encodeNat (n : ℕ) :
    (encodeNat n).length = (n + 1).size + 2 * ((n + 1).size.size - 1) := by
  have hp := size_pos (n + 1) (by omega)
  simp only [encodeNat, List.length_append, length_encodeGamma, length_payload]
  omega

/-- Delta coding uses at most three times the binary size of the shifted argument. -/
theorem length_encodeNat_le (n : ℕ) : (encodeNat n).length ≤ 3 * (n + 1).size := by
  have hs : (n + 1).size.size ≤ (n + 1).size :=
    Counter.size_le_of_lt_pow _ _ (Nat.lt_two_pow_self (n := (n + 1).size))
  rw [length_encodeNat]
  omega

/-- Every encoded natural number consumes at least one bit. -/
theorem length_encodeNat_pos (n : ℕ) : 0 < (encodeNat n).length := by
  have hp := size_pos (n + 1) (by omega)
  rw [length_encodeNat]
  omega

/-- Successful parsing strictly shortens the input. -/
theorem readNat_rest_length_lt (w : List Bool) (n : ℕ) (rest : List Bool)
    (h : readNat w = some (n, rest)) : rest.length < w.length := by
  have hp := length_encodeNat_pos n
  rw [readNat_eq_some w n rest h, List.length_append]
  omega

end Geb.BitTree.Elias
