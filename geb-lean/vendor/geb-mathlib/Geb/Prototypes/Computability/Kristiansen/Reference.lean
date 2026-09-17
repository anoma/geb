/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Kristiansen.Suffix
public import Geb.Prototypes.Computability.BitTree.Counter

set_option doc.verso true in
/-!
# Suffix references

The representation used in the soundness argument of \[Kristiansen2005\]
Theorem 4.7: a short word is stored directly, and a long word by an input index
and its suffix length. The input words are external to the reference.

## Main definitions

* {lit}`Reference` is a short word or a bounded suffix length of one input.
* {lit}`Reference.value` reads the represented word.
* {lit}`Reference.encode` encodes the reference as a binary word.

## Main statements

* {lit}`Reference.length_encode_le` bounds the representation by a constant plus
  the binary size of the input-length bound.
* {lit}`exists_reference` represents every algebra output.
* {lit}`exists_reference_bounded` combines representation and its length bound.

## Implementation notes

This is a storage representation theorem. It does not assert that evaluation,
encoding, or reading a reference has been implemented by a Turing machine.
The input index has a unary encoding; the arity is fixed for each expression,
so this contributes only a constant to the representation length.

## References

* \[Kristiansen2005\], Theorem 4.7.

## Tags

suffix, binary encoding, space complexity, function algebra
-/

set_option doc.verso true

namespace Geb.Kristiansen

public section

/-- A short word or the length of a suffix of an input. Input data is a parameter,
not a field of the representation. -/
@[expose] def Reference {n : ℕ} (K : ℕ) (x : Fin n → List Bool) : Type :=
  { w : List Bool // w.length ≤ K } ⊕ (Σ i : Fin n, Fin ((x i).length + 1))

/-- Read the reference, using the external input environment. -/
@[expose] def Reference.value {n K : ℕ} {x : Fin n → List Bool} : Reference K x → List Bool
  | .inl w => w.1
  | .inr ⟨i, l⟩ => (x i).drop ((x i).length - l)

/-- The representation uses a status bit, then either the short word or a
unary-delimited input index followed by a binary suffix length. -/
@[expose] def Reference.encode {n K : ℕ} {x : Fin n → List Bool} : Reference K x → List Bool
  | .inl w => false :: w.1
  | .inr ⟨i, l⟩ => true :: (List.replicate i.val false ++ true :: l.val.bits)

/-- A reference occupies at most a constant plus the binary size of the input bound. -/
theorem Reference.length_encode_le {n K m : ℕ} {x : Fin n → List Bool}
    (r : Reference K x) (hx : ∀ i, (x i).length ≤ m) :
    r.encode.length ≤ K + n + m.size + 2 := by
  cases r with
  | inl w =>
    have := w.2
    simp only [Reference.encode, List.length_cons]
    omega
  | inr p =>
    obtain ⟨i, l⟩ := p
    have hi := i.isLt
    have hl : l.val ≤ m := by have := l.isLt; have := hx i; omega
    have hs := BitTree.Counter.size_mono hl
    simp only [Reference.encode, List.length_cons, List.length_append, List.length_replicate,
      Nat.size_eq_bits_len]
    omega

/-- A word within the constant bound or an input suffix has a reference. -/
theorem exists_reference_of_short_or_suffix {n K : ℕ} {x : Fin n → List Bool} {w : List Bool}
    (h : w.length ≤ K ∨ ∃ i, w <:+ x i) :
    ∃ r : Reference K x, r.value = w := by
  rcases h with hw | ⟨i, hi⟩
  · exact ⟨.inl ⟨w, hw⟩, rfl⟩
  · exact ⟨.inr ⟨i, ⟨w.length, Nat.lt_succ_of_le hi.length_le⟩⟩,
      (List.suffix_iff_eq_drop.mp hi).symm⟩

/-- The output of any expression can be represented relative to its original inputs. -/
theorem exists_reference {n : ℕ} (e : LOf n) (x : Fin n → List Bool) :
    ∃ r : Reference (SizeBounded.nsiConst e.1.1.1) x, r.value = e.sem x :=
  exists_reference_of_short_or_suffix (short_or_suffix e x)

/-- Algebra outputs admit references whose bit length is logarithmic in the input bound. -/
theorem exists_reference_bounded {n : ℕ} (e : LOf n) (x : Fin n → List Bool) (m : ℕ)
    (hx : ∀ i, (x i).length ≤ m) :
    ∃ r : Reference (SizeBounded.nsiConst e.1.1.1) x,
      r.value = e.sem x ∧ r.encode.length ≤ SizeBounded.nsiConst e.1.1.1 + n + m.size + 2 := by
  obtain ⟨r, hr⟩ := exists_reference e x
  exact ⟨r, hr, r.length_encode_le hx⟩

end

end Geb.Kristiansen
