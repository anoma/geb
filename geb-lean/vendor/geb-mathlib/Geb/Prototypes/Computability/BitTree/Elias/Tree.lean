/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Encoding
public import Geb.Prototypes.Computability.BitTree.Elias.Code

set_option doc.verso true

/-!
# Binary trees with length-prefixed leaf payloads

The tree shape retains one tag per node. Leaf payloads are preceded by their
lengths, so payload bits are stored without escaping.

## Main definitions

* {lit}`lengths` lists the payload lengths in left-to-right leaf order.
* {lit}`encode` uses one tag per node and a delta length header per leaf.
* {lit}`decode` reads a complete tree; {lit}`validBool` tests whether it succeeds.

## Main statements

* {lit}`length_encode` counts node tags, raw payload bits and length headers.
* {lit}`readTree_encode_append` proves the fuel-bounded parser's prefix roundtrip.
* {lit}`validBool_iff_existsUnique` characterizes the recognized language.

## Tags

binary tree, bitstring, length prefix, encoding
-/

@[expose] public section

namespace Geb.BitTree.Elias

/-- Payload lengths in left-to-right leaf order. -/
def lengths : Tree → List ℕ := WType.elim (List ℕ) fun x ↦
  match x with
  | ⟨some s, _⟩ => [s.length]
  | ⟨none, f⟩ => f false ++ f true

@[simp] theorem lengths_leaf (s : List Bool) : lengths (leaf s) = [s.length] := rfl

@[simp] theorem lengths_fork (l r : Tree) : lengths (fork l r) = lengths l ++ lengths r := rfl

/-- There is one payload length per leaf. -/
theorem length_lengths (t : Tree) : (lengths t).length = (counts t).2.1 :=
  tree_ind (P := fun t ↦ (lengths t).length = (counts t).2.1)
    (fun _ ↦ rfl)
    (fun l r hl hr ↦ by
      beta_reduce
      rw [lengths_fork, List.length_append, hl, hr]
      rfl) t

/-- The sum of the lengths is the total number of payload bits. -/
theorem sum_lengths (t : Tree) : (lengths t).sum = (counts t).2.2 :=
  tree_ind (P := fun t ↦ (lengths t).sum = (counts t).2.2)
    (fun _ ↦ Nat.add_zero _)
    (fun l r hl hr ↦ by
      beta_reduce
      rw [lengths_fork, List.sum_append, hl, hr]
      rfl) t

/-- Read a payload of the specified length, rejecting truncated input. -/
def readPayload (n : ℕ) (w : List Bool) : Option (List Bool × List Bool) :=
  if n ≤ w.length then some (w.take n, w.drop n) else none

/-- Reading a payload preserves the unconsumed suffix. -/
theorem readPayload_append (s rest : List Bool) :
    readPayload s.length (s ++ rest) = some (s, rest) := by
  simp only [readPayload, List.length_append, Nat.le_add_right, ↓reduceIte,
    List.take_left, List.drop_left]

/-- A successful payload read gives its length and the exact input decomposition. -/
theorem readPayload_eq_some {n : ℕ} {w s rest : List Bool}
    (h : readPayload n w = some (s, rest)) : s.length = n ∧ w = s ++ rest := by
  unfold readPayload at h
  split at h
  next hn =>
    cases h
    exact ⟨List.length_take_of_le hn, (List.take_append_drop n w).symm⟩
  next => cases h

/-- Preorder tree tags with a delta-coded length followed by each leaf's raw payload. -/
def encode : Tree → List Bool := WType.elim (List Bool) fun x ↦
  match x with
  | ⟨some s, _⟩ => false :: (encodeNat s.length ++ s)
  | ⟨none, f⟩ => true :: (f false ++ f true)

@[simp] theorem encode_leaf (s : List Bool) :
    encode (leaf s) = false :: (encodeNat s.length ++ s) := rfl

@[simp] theorem encode_fork (l r : Tree) :
    encode (fork l r) = true :: (encode l ++ encode r) := rfl

/-- The exact representation length separates node tags, raw bits and length headers. -/
theorem length_encode (t : Tree) :
    (encode t).length = 2 * (counts t).1 + 1 + (counts t).2.2 +
      ((lengths t).map fun n ↦ (encodeNat n).length).sum :=
  tree_ind (P := fun t ↦ (encode t).length = 2 * (counts t).1 + 1 + (counts t).2.2 +
      ((lengths t).map fun n ↦ (encodeNat n).length).sum)
    (fun s ↦ by
      simp only [encode_leaf, List.length_cons, List.length_append, counts_leaf, lengths_leaf,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
    (fun l r hl hr ↦ by
      simp only [encode_fork, List.length_cons, List.length_append, counts_fork, lengths_fork,
        List.map_append, List.sum_append]
      omega) t

/-- The total header cost is logarithmic in each shifted payload length. -/
theorem length_encode_le (t : Tree) :
    (encode t).length ≤ 2 * (counts t).1 + 1 + (counts t).2.2 +
      3 * ((lengths t).map fun n ↦ (n + 1).size).sum :=
  tree_ind (P := fun t ↦ (encode t).length ≤ 2 * (counts t).1 + 1 + (counts t).2.2 +
      3 * ((lengths t).map fun n ↦ (n + 1).size).sum)
    (fun s ↦ by
      have h := length_encodeNat_le s.length
      simp only [encode_leaf, List.length_cons, List.length_append, counts_leaf, lengths_leaf,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
    (fun l r hl hr ↦ by
      simp only [encode_fork, List.length_cons, List.length_append, counts_fork, lengths_fork,
        List.map_append, List.sum_append]
      omega) t

/-- There is enough input length to bound every recursive descent in the tree parser. -/
theorem forks_lt_length_encode (t : Tree) : (counts t).1 < (encode t).length := by
  rw [length_encode]
  omega

/-- One tree-parser layer: a leaf payload or two recursively read children. -/
def readTreeStep (readChild : List Bool → Option (Tree × List Bool))
    (w : List Bool) : Option (Tree × List Bool) :=
  match w with
  | [] => none
  | false :: suffix => (readNat suffix).bind fun p ↦
      (readPayload p.1 p.2).map fun q ↦ (leaf q.1, q.2)
  | true :: suffix => (readChild suffix).bind fun p ↦
      (readChild p.2).map fun q ↦ (fork p.1 q.1, q.2)

/-- A fuel-bounded tree parser, with the bound controlling recursive tree descent. -/
def readTree : ℕ → List Bool → Option (Tree × List Bool) :=
  Nat.rec (fun _ ↦ none) fun _ readChild ↦ readTreeStep readChild

/-- The parser's successor-fuel equation. -/
theorem readTree_succ (fuel : ℕ) (w : List Bool) :
    readTree (fuel + 1) w = readTreeStep (readTree fuel) w := rfl

/-- A bound larger than the number of forks suffices for every encoded tree. -/
theorem readTree_encode_append (t : Tree) : ∀ fuel, (counts t).1 + 1 ≤ fuel →
    ∀ rest, readTree fuel (encode t ++ rest) = some (t, rest) :=
  tree_ind (P := fun t ↦ ∀ fuel, (counts t).1 + 1 ≤ fuel →
      ∀ rest, readTree fuel (encode t ++ rest) = some (t, rest))
    (fun s fuel hf rest ↦ by
      cases fuel with
      | zero =>
        exfalso
        have hh : 0 + 1 ≤ 0 := hf
        omega
      | succ fuel =>
        simp only [encode_leaf, List.cons_append, readTree_succ, readTreeStep,
          List.append_assoc, readNat_encodeNat_append, Option.bind_some, readPayload_append,
          Option.map_some])
    (fun l r hl hr fuel hf rest ↦ by
      cases fuel with
      | zero => exfalso; omega
      | succ fuel =>
        rw [counts_fork] at hf
        simp only [encode_fork, List.cons_append, readTree_succ, readTreeStep,
          List.append_assoc]
        rw [hl fuel (by omega), Option.bind_some, hr fuel (by omega), Option.map_some]) t

/-- Every successful tree parse consumes exactly the canonical encoding of its result. -/
theorem readTree_eq_some (fuel : ℕ) : ∀ w t rest,
    readTree fuel w = some (t, rest) → w = encode t ++ rest :=
  Nat.rec (fun w t rest h ↦ by cases h)
    (fun fuel ih w t rest h ↦ by
      cases w with
      | nil => cases h
      | cons b suffix =>
        cases b with
        | false =>
          cases hn : readNat suffix with
          | none =>
            simp only [readTree_succ, readTreeStep, hn, Option.bind_none, reduceCtorEq] at h
          | some p =>
            rcases p with ⟨n, input⟩
            cases hp : readPayload n input with
            | none =>
              simp only [readTree_succ, readTreeStep, hn, Option.bind_some, hp,
                Option.map_none, reduceCtorEq] at h
            | some p =>
              rcases p with ⟨bs, tail⟩
              have he : (leaf bs, tail) = (t, rest) := Option.some.inj (by
                simpa only [readTree_succ, readTreeStep, hn, Option.bind_some, hp,
                  Option.map_some] using h)
              obtain ⟨ht, hr⟩ := Prod.mk.inj he
              obtain ⟨hlen, hinput⟩ := readPayload_eq_some hp
              rw [← ht, ← hr, encode_leaf, List.cons_append,
                readNat_eq_some suffix n input hn, hinput, ← hlen, List.append_assoc]
        | true =>
          cases hl : readTree fuel suffix with
          | none =>
            simp only [readTree_succ, readTreeStep, hl, Option.bind_none, reduceCtorEq] at h
          | some p =>
            rcases p with ⟨l, middle⟩
            cases hr : readTree fuel middle with
            | none =>
              simp only [readTree_succ, readTreeStep, hl, Option.bind_some, hr,
                Option.map_none, reduceCtorEq] at h
            | some p =>
              rcases p with ⟨r, tail⟩
              have he : (fork l r, tail) = (t, rest) := Option.some.inj (by
                simpa only [readTree_succ, readTreeStep, hl, Option.bind_some, hr,
                  Option.map_some] using h)
              obtain ⟨ht, hs⟩ := Prod.mk.inj he
              rw [← ht, ← hs, encode_fork, List.cons_append, ih suffix l middle hl,
                ih middle r tail hr, List.append_assoc]) fuel

/-- Decode exactly one complete tree, rejecting trailing or incomplete input. -/
def decode (w : List Bool) : Option Tree :=
  match readTree w.length w with
  | some (t, []) => some t
  | _ => none

/-- The input length supplies enough parser fuel for every encoded tree. -/
@[simp] theorem decode_encode (t : Tree) : decode (encode t) = some t := by
  have h := readTree_encode_append t (encode t).length (forks_lt_length_encode t) []
  simp only [List.append_nil] at h
  rw [decode, h]

/-- Successful complete decoding identifies the whole input as the resulting tree's encoding. -/
theorem decode_eq_some (w : List Bool) (t : Tree) (h : decode w = some t) : encode t = w := by
  cases hp : readTree w.length w with
  | none => simp only [decode, hp, reduceCtorEq] at h
  | some p =>
    rcases p with ⟨t', rest⟩
    cases rest with
    | nil =>
      have he : t' = t := Option.some.inj (by simpa only [decode, hp] using h)
      rw [he] at hp
      simpa only [List.append_nil] using (readTree_eq_some w.length w t [] hp).symm
    | cons _ _ => simp only [decode, hp, reduceCtorEq] at h

/-- The length-prefixed tree encoding is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro t t' h
  have he := congrArg decode h
  rw [decode_encode, decode_encode] at he
  exact Option.some.inj he

/-- The complete decoder decides membership in the encoded-tree language. -/
def validBool (w : List Bool) : Bool := (decode w).isSome

/-- Every encoded tree is accepted by the complete decoder. -/
@[simp] theorem validBool_encode (t : Tree) : validBool (encode t) = true := by
  rw [validBool, decode_encode]
  rfl

/-- Acceptance is exactly existence of an encoded tree. -/
theorem validBool_iff (w : List Bool) : validBool w = true ↔ ∃ t, encode t = w := by
  constructor
  · intro h
    cases hd : decode w with
    | none => simp only [validBool, hd, Option.isSome_none, Bool.false_eq_true] at h
    | some t => exact ⟨t, decode_eq_some w t hd⟩
  · rintro ⟨t, rfl⟩
    exact validBool_encode t

/-- Every accepted word represents exactly one tree of bitstrings. -/
theorem validBool_iff_existsUnique (w : List Bool) :
    validBool w = true ↔ ∃! t, encode t = w := by
  rw [validBool_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ht, fun t' ht' ↦ encode_injective (ht'.trans ht.symm)⟩
  · rintro ⟨t, ht, _⟩
    exact ⟨t, ht⟩

end Geb.BitTree.Elias
