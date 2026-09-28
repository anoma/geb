/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Elias.Scanner
public import Geb.Prototypes.Computability.BitTree.Elias.Code

set_option doc.verso true in
/-!
# Streaming recognition of Elias delta headers

The scanner reads a unary size prefix and two fixed-width binary fields. Complete fields
change phases on their last bit; incomplete fields retain a header phase and cannot accept.

## Main statements

* {lit}`foldl_header` relates successful integer parsing to the streaming header phases.
* {lit}`header_reject` excludes acceptance when the integer header is incomplete.

## Tags

Elias delta code, streaming recognizer, simulation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.Elias.Scanner

/-- Scanning a unary zero prefix increases the prefix count by its length. -/
theorem foldl_replicate_false (k z n : ℕ) :
    (List.replicate k false).foldl step (.zeros z, n) = (.zeros (z + k), n) := by
  revert z
  apply Nat.rec (motive := fun k ↦ ∀ z,
    (List.replicate k false).foldl step (.zeros z, n) = (.zeros (z + k), n)) ?_ ?_ k
  · intro z
    rfl
  · intro k ih z
    rw [List.replicate_succ, List.foldl_cons]
    change (List.replicate k false).foldl step (.zeros (z + 1), n) = _
    rw [ih]
    congr 2
    omega

/-- A nonempty fixed-width field ends at its final bit, in either binary header phase. -/
theorem foldl_field (isSize : Bool) (bs : List Bool) : ∀ v n, bs ≠ [] →
    bs.foldl step ((if isSize then .size bs.length v else .length bs.length v), n) =
      ((if isSize then .length (bs.foldl (fun a b ↦ Nat.bit b a) v - 1) 1
        else .payload (bs.foldl (fun a b ↦ Nat.bit b a) v - 1)), n) :=
  List.rec (fun _ _ h ↦ (h rfl).elim) (fun b bs ih v n _ ↦ by
    cases bs with
    | nil => cases isSize <;> rfl
    | cons c bs =>
      have he : bs.length + 1 + 1 ≠ 1 := by omega
      cases isSize <;>
        simpa only [List.foldl_cons, List.length_cons, step, he, Bool.false_eq_true, ↓reduceIte,
          Nat.add_sub_cancel] using ih (Nat.bit b v) n (by simp)) bs

/-- A field shorter than its remaining width stays in the same header phase. -/
theorem foldl_short_field (isSize : Bool) (bs : List Bool) : ∀ r v n, bs.length < r →
    bs.foldl step ((if isSize then .size r v else .length r v), n) =
      ((if isSize then .size (r - bs.length) (bs.foldl (fun a b ↦ Nat.bit b a) v)
        else .length (r - bs.length) (bs.foldl (fun a b ↦ Nat.bit b a) v)), n) :=
  List.rec (fun _ _ _ _ ↦ rfl) (fun b bs ih r v n h ↦ by
    have hr : r ≠ 1 := by simp only [List.length_cons] at h; omega
    have ht : bs.length < r - 1 := by simp only [List.length_cons] at h; omega
    have he : r - 1 - bs.length = r - (bs.length + 1) := by omega
    cases isSize <;>
      simpa only [List.foldl_cons, List.length_cons, step, hr, Bool.false_eq_true,
        ↓reduceIte, he] using
        ih (r - 1) (Nat.bit b v) n ht) bs

/-- A positive integer has an empty binary payload exactly when it is one. -/
theorem payload_eq_nil_iff (k : ℕ) (hk : k ≠ 0) : payload k = [] ↔ k = 1 := by
  constructor
  · intro h
    have he := fromPayload_payload k hk
    rw [h] at he
    exact he.symm
  · rintro rfl
    rfl

/-- Scanning a gamma prefix either completes zero or starts the remaining length field. -/
theorem foldl_gamma (k : ℕ) (hk : k ≠ 0) (n : ℕ) :
    (encodeGamma k).foldl step (.zeros 0, n) =
      if k = 1 then finish n else (.length (k - 1) 1, n) := by
  have hp := payload_eq_nil_iff k hk
  by_cases hnil : payload k = []
  · have he := hp.mp hnil
    subst k
    rfl
  · have hlen : (payload k).length ≠ 0 := by
      intro he
      exact hnil (List.eq_nil_of_length_eq_zero he)
    have hk1 : k ≠ 1 := fun he ↦ hnil (hp.mpr he)
    rw [encodeGamma, ← length_payload, List.foldl_append, foldl_replicate_false]
    simp only [Nat.zero_add, List.foldl_cons, step, hlen, ↓reduceIte]
    have hf := foldl_field true (payload k) 1 n hnil
    simp only [↓reduceIte] at hf
    rw [hf]
    change (Mode.length (fromPayload (payload k) - 1) 1, n) = _
    rw [fromPayload_payload k hk, if_neg hk1]

/-- Scanning a complete delta code sets its raw-payload countdown. -/
theorem foldl_encodeNat (m n : ℕ) :
    (encodeNat m).foldl step (.zeros 0, n) =
      if m = 0 then finish n else (.payload m, n) := by
  cases m with
  | zero => rfl
  | succ m =>
    have hp : m + 1 + 1 ≠ 0 := by omega
    have hs : (m + 1 + 1).size ≠ 0 := by have h := size_pos _ hp; omega
    have hnil : payload (m + 1 + 1) ≠ [] := by
      intro he
      have hh := (payload_eq_nil_iff _ hp).mp he
      omega
    have hs1 : (m + 1 + 1).size ≠ 1 := by
      intro he
      apply hnil
      apply List.eq_nil_of_length_eq_zero
      rw [length_payload, he]
    have hf := foldl_field false (payload (m + 1 + 1)) 1 n hnil
    simp only [Bool.false_eq_true, ↓reduceIte] at hf
    rw [encodeNat, List.foldl_append, foldl_gamma _ hs n, if_neg hs1,
      ← length_payload, hf]
    change (Mode.payload (fromPayload (payload (m + 1 + 1)) - 1), n) = _
    rw [fromPayload_payload _ hp]
    rfl

/-- A successfully parsed header has the same effect as its bitwise scan. -/
theorem foldl_header (w : List Bool) (m : ℕ) (rest : List Bool) (n : ℕ)
    (h : readNat w = some (m, rest)) :
    w.foldl step (.zeros 0, n) =
      rest.foldl step (if m = 0 then finish n else (.payload m, n)) := by
  rw [readNat_eq_some w m rest h, List.foldl_append, foldl_encodeNat]

/-- A prefix with no terminating one remains in the unary header phase. -/
theorem foldl_zeros_none (w : List Bool) : ∀ z n, readZeros w = none →
    w.foldl step (.zeros z, n) = (.zeros (z + w.length), n) :=
  List.rec (fun _ _ _ ↦ rfl) (fun b bs ih z n h ↦ by
    cases b with
    | true => cases h
    | false =>
      have ht : readZeros bs = none := by
        cases hx : readZeros bs with
        | none => rfl
        | some p =>
          rw [readZeros_cons, hx] at h
          simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, reduceCtorEq] at h
      rw [List.foldl_cons]
      change bs.foldl step (.zeros (z + 1), n) = _
      rw [ih (z + 1) n ht]
      congr 2
      simp only [List.length_cons]
      omega) w

/-- Failure of a fixed-width read means the available input is too short. -/
theorem readFixed_none_lt (k : ℕ) (w : List Bool) (h : readFixed k w = none) :
    w.length < k := by
  unfold readFixed at h
  split at h
  next => contradiction
  next hk => omega

/-- An incomplete gamma prefix cannot leave the header phases. -/
theorem gamma_reject (w : List Bool) (n : ℕ) (h : readGamma w = none) :
    (w.foldl step (.zeros 0, n)).1 ≠ .done := by
  cases hz : readZeros w with
  | none => rw [foldl_zeros_none w 0 n hz]; intro he; cases he
  | some p =>
    rcases p with ⟨z, suffix⟩
    have hf : readFixed z suffix = none := by
      simpa only [readGamma, hz, Option.bind_some] using h
    have hlt := readFixed_none_lt z suffix hf
    have hz0 : z ≠ 0 := by omega
    rw [readZeros_eq_some w z suffix hz, List.foldl_append, foldl_replicate_false]
    simp only [Nat.zero_add, List.foldl_cons, step, hz0, ↓reduceIte]
    have he := foldl_short_field true suffix z 1 n hlt
    simp only [↓reduceIte] at he
    rw [he]
    intro hh
    cases hh

/-- An incomplete delta header cannot cause acceptance. -/
theorem header_reject (w : List Bool) (n : ℕ) (h : readNat w = none) :
    (w.foldl step (.zeros 0, n)).1 ≠ .done := by
  cases hg : readGamma w with
  | none => exact gamma_reject w n hg
  | some p =>
    rcases p with ⟨k, suffix⟩
    obtain ⟨hk, hw⟩ := readGamma_eq_some w k suffix hg
    have hf : readFixed (k - 1) suffix = none := by
      cases hx : readFixed (k - 1) suffix with
      | none => rfl
      | some p =>
        simp only [readNat, hg, Option.bind_some, hx, reduceCtorEq] at h
    have hlt := readFixed_none_lt (k - 1) suffix hf
    have hk1 : k ≠ 1 := by omega
    rw [hw, List.foldl_append, foldl_gamma k hk n, if_neg hk1]
    have he := foldl_short_field false suffix (k - 1) 1 n hlt
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    rw [he]
    intro hh
    cases hh

end Geb.BitTree.Elias.Scanner
