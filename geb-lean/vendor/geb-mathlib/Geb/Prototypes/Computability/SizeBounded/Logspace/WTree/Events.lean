/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Elias.ScannerHeader
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Attr.Core
public import Aesop

set_option doc.verso true in
/-!
# The events of the Elias-length tree scanner

A bit read by the streaming scanner {name}`Geb.BitTree.Elias.Scanner.step`
raises one of four events or none: a fork tag or a leaf tag in the tree
phase, the completion of a delta header, at which a payload of the length the
header carries begins at the next bit, and the completion of a leaf. A scanner
that recognizes more than the tree structure keeps further registers that
change only at these events, so it is the product of the streaming scanner
with a register updated by the event of each bit, {lit}`Ext` and
{lit}`extStep`, and its behaviour on an encoded tree follows from where the
events fall: a zero run, a size or length field and a payload raise no event
before their last bit, and the last bit of a header raises the completion of
the header, of a payload the completion of the leaf.

# Main definitions

* {lit}`Event`, {lit}`Event.silent`, {lit}`eventS` — the events, the absence of
  one, and the event a bit raises at a state.
* {lit}`Ext`, {lit}`extStep` — the streaming scanner with a position and a
  register updated at events, and its step.

# Main statements

* {lit}`foldl_extStep_replicate_false`, {lit}`foldl_extStep_short_field`,
  {lit}`foldl_extStep_field`, {lit}`foldl_extStep_gamma`,
  {lit}`foldl_extStep_encodeNat`, {lit}`foldl_extStep_payload` — the extended
  scanner over the segments of a leaf's encoding: the register changes at the
  last bit of a header and of a payload alone.

# References

* \[Elias1975\]

# Tags

Elias delta code, streaming recognizer, event, product automaton
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree.Elias (encodeNat encodeGamma payload)
open Geb.BitTree.Elias.Scanner (Mode State step finish)

public section

/-- The events one bit can raise. -/
structure Event where
  /-- A fork tag in the tree phase. -/
  fork : Bool
  /-- A leaf tag in the tree phase. -/
  tag : Bool
  /-- A delta header completes: a payload of this length begins at the next
  bit. -/
  payload : Option ℕ
  /-- A leaf completes at this bit. -/
  done : Bool
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprEvent.repr

/-- No event. -/
@[expose] def Event.silent : Event := ⟨false, false, none, false⟩

/-- The event a bit raises at a state: the tags in the tree phase; the header
completing on the bit closing an empty zero run, which is the header of an
empty payload and completes the leaf as well, or on the last bit of the length
field; and the leaf completing on the last bit of the payload. -/
@[expose] def eventS : State → Bool → Event
  | (.tree, _), true => ⟨true, false, none, false⟩
  | (.tree, _), false => ⟨false, true, none, false⟩
  | (.zeros z, _), true => if z = 0 then ⟨false, false, some 0, true⟩ else .silent
  | (.length r v, _), b => if r = 1 then ⟨false, false, some (Nat.bit b v - 1), false⟩ else .silent
  | (.payload r, _), _ => if r = 1 then ⟨false, false, none, true⟩ else .silent
  | _, _ => .silent

/-- The streaming scanner with the number of bits read and a register. -/
structure Ext (α : Type) where
  /-- The scanner's state. -/
  state : State
  /-- The number of bits read. -/
  pos : ℕ
  /-- The register. -/
  extra : α

/-- One bit: the scanner steps, the position advances, and the register is
updated by the event, at the position of the bit. -/
@[expose] def extStep {α : Type} (upd : ℕ → Event → α → α) (s : Ext α) (b : Bool) : Ext α :=
  ⟨step s.state b, s.pos + 1, upd s.pos (eventS s.state b) s.extra⟩

variable {α : Type} (upd : ℕ → Event → α → α) (hu : ∀ p x, upd p .silent x = x)

include hu

/-- A zero run raises no event. -/
theorem foldl_extStep_replicate_false (k : ℕ) :
    ∀ (z n pos : ℕ) (x : α), (List.replicate k false).foldl (extStep upd) ⟨(.zeros z, n), pos, x⟩ =
      ⟨(.zeros (z + k), n), pos + k, x⟩ :=
  Nat.rec (fun z n pos x ↦ rfl) (fun k ih z n pos x ↦ by
    rw [List.replicate_succ, List.foldl_cons]
    change (List.replicate k false).foldl (extStep upd)
      ⟨(.zeros (z + 1), n), pos + 1, upd pos .silent x⟩ = _
    rw [hu, ih, show z + 1 + k = z + (k + 1) by omega, show pos + 1 + k = pos + (k + 1) by omega]) k

/-- A field shorter than its remaining width raises no event. -/
theorem foldl_extStep_short_field (isSize : Bool) (bs : List Bool) :
    ∀ (r v n pos : ℕ) (x : α), bs.length < r →
      bs.foldl (extStep upd) ⟨((if isSize then .size r v else .length r v), n), pos, x⟩ =
        ⟨((if isSize then .size (r - bs.length) (bs.foldl (fun a b ↦ Nat.bit b a) v)
          else .length (r - bs.length) (bs.foldl (fun a b ↦ Nat.bit b a) v)), n),
            pos + bs.length, x⟩ :=
  List.rec (fun _ _ _ _ _ _ ↦ rfl) (fun b bs ih r v n pos x h ↦ by
    have hr : r ≠ 1 := by simp only [List.length_cons] at h; omega
    have ht : bs.length < r - 1 := by simp only [List.length_cons] at h; omega
    have he : r - 1 - bs.length = r - (bs.length + 1) := by omega
    have hp : pos + 1 + bs.length = pos + (bs.length + 1) := by omega
    have ih' := ih (r - 1) (Nat.bit b v) n (pos + 1) x ht
    cases isSize
    · simp only [Bool.false_eq_true, ↓reduceIte] at ih' ⊢
      rw [List.foldl_cons]
      simp only [extStep, step, eventS, hr, ↓reduceIte, hu]
      rw [ih', he, hp]
      rfl
    · simp only [↓reduceIte] at ih' ⊢
      rw [List.foldl_cons]
      simp only [extStep, step, eventS, hr, ↓reduceIte, hu]
      rw [ih', he, hp]
      rfl) bs

/-- A nonempty field ends at its last bit: a size field raises no event, a
length field raises the completion of the header at the last bit, at the
position of that bit. -/
theorem foldl_extStep_field (isSize : Bool) (bs : List Bool) (v n pos : ℕ) (x : α)
    (hbs : bs ≠ []) :
    bs.foldl (extStep upd) ⟨((if isSize then .size bs.length v else .length bs.length v), n),
      pos, x⟩ =
      ⟨((if isSize then .length (bs.foldl (fun a b ↦ Nat.bit b a) v - 1) 1
        else .payload (bs.foldl (fun a b ↦ Nat.bit b a) v - 1)), n), pos + bs.length,
        if isSize then x else
          upd (pos + bs.length - 1)
            ⟨false, false, some (bs.foldl (fun a b ↦ Nat.bit b a) v - 1), false⟩ x⟩ := by
  obtain ⟨bs', b, rfl⟩ : ∃ bs' b, bs = bs' ++ [b] := by
    cases hb : bs.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hb) hbs
    | cons b bs' => exact ⟨bs'.reverse, b, by rw [← List.reverse_reverse bs, hb, List.reverse_cons]⟩
  have hl : bs'.length < (bs' ++ [b]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  rw [List.foldl_append, foldl_extStep_short_field upd hu isSize bs' _ v n pos x hl,
    List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil,
    List.length_append, List.length_singleton]
  have hr : bs'.length + 1 - bs'.length = 1 := by omega
  have hp : pos + bs'.length + 1 = pos + (bs'.length + 1) := by omega
  have hq : pos + (bs'.length + 1) - 1 = pos + bs'.length := by omega
  cases isSize
  · simp only [Bool.false_eq_true, ↓reduceIte, hr, extStep, step, eventS, hp, hq]
  · simp only [↓reduceIte, hr, extStep, step, eventS, hu, hp]

/-- A gamma code: the code of one is the header of an empty payload,
completing the header and the leaf together; any other opens the length field
and raises no event. -/
theorem foldl_extStep_gamma (k : ℕ) (hk : k ≠ 0) (n pos : ℕ) (x : α) :
    (encodeGamma k).foldl (extStep upd) ⟨(.zeros 0, n), pos, x⟩ =
      if k = 1 then ⟨finish n, pos + 1, upd pos ⟨false, false, some 0, true⟩ x⟩
      else ⟨(.length (k - 1) 1, n), pos + (encodeGamma k).length, x⟩ := by
  have hp := Geb.BitTree.Elias.Scanner.payload_eq_nil_iff k hk
  by_cases hnil : payload k = []
  · have he := hp.mp hnil
    subst k
    rfl
  · have hlen : (payload k).length ≠ 0 := by
      intro he
      exact hnil (List.eq_nil_of_length_eq_zero he)
    have hk1 : k ≠ 1 := fun he ↦ hnil (hp.mpr he)
    rw [if_neg hk1, encodeGamma, ← Geb.BitTree.Elias.length_payload, List.foldl_append,
      foldl_extStep_replicate_false upd hu, List.foldl_cons]
    simp only [extStep, step, eventS, Nat.zero_add, hlen, ↓reduceIte, hu]
    have hf := foldl_extStep_field upd hu true (payload k) 1 n (pos + (payload k).length + 1) x hnil
    simp only [↓reduceIte] at hf
    rw [hf]
    change (⟨(Mode.length (Geb.BitTree.Elias.fromPayload (payload k) - 1) 1, n), _, x⟩ : Ext α) = _
    rw [Geb.BitTree.Elias.fromPayload_payload k hk, List.length_append, List.length_replicate,
      List.length_cons, show pos + (payload k).length + 1 + (payload k).length =
        pos + ((payload k).length + ((payload k).length + 1)) by omega]

/-- A delta code completes the header at its last bit, with the payload length
it carries, and, when that length is zero, the leaf. -/
theorem foldl_extStep_encodeNat (m n pos : ℕ) (x : α) :
    (encodeNat m).foldl (extStep upd) ⟨(.zeros 0, n), pos, x⟩ =
      ⟨(if m = 0 then finish n else (.payload m, n)), pos + (encodeNat m).length,
        upd (pos + (encodeNat m).length - 1) ⟨false, false, some m, decide (m = 0)⟩ x⟩ := by
  cases m with
  | zero => rfl
  | succ m =>
    have hp : m + 1 + 1 ≠ 0 := by omega
    have hs : (m + 1 + 1).size ≠ 0 := by have h := Geb.BitTree.Elias.size_pos _ hp; omega
    have hnil : payload (m + 1 + 1) ≠ [] := by
      intro he
      have hh := (Geb.BitTree.Elias.Scanner.payload_eq_nil_iff _ hp).mp he
      omega
    have hs1 : (m + 1 + 1).size ≠ 1 := by
      intro he
      apply hnil
      apply List.eq_nil_of_length_eq_zero
      rw [Geb.BitTree.Elias.length_payload, he]
    have hf := foldl_extStep_field upd hu false (payload (m + 1 + 1)) 1 n
      (pos + (encodeGamma (m + 1 + 1).size).length) x hnil
    simp only [Bool.false_eq_true, ↓reduceIte] at hf
    rw [encodeNat, List.foldl_append, foldl_extStep_gamma upd hu _ hs, if_neg hs1,
      ← Geb.BitTree.Elias.length_payload, hf]
    change (⟨(Mode.payload (Geb.BitTree.Elias.fromPayload (payload (m + 1 + 1)) - 1), n), _,
      upd _ ⟨false, false, some (Geb.BitTree.Elias.fromPayload (payload (m + 1 + 1)) - 1), false⟩
        x⟩ : Ext α) = _
    have e₁ : m + 1 + 1 - 1 = m + 1 := by omega
    have e₂ : pos + (encodeGamma (m + 1 + 1).size).length + (payload (m + 1 + 1)).length =
        pos + ((encodeGamma (m + 1 + 1).size).length + (payload (m + 1 + 1)).length) := by omega
    rw [Geb.BitTree.Elias.fromPayload_payload _ hp, List.length_append, e₁, e₂,
      if_neg (Nat.add_one_ne_zero m), decide_eq_false (Nat.add_one_ne_zero m)]

/-- A nonempty payload completes the leaf at its last bit. -/
theorem foldl_extStep_payload (s : List Bool) (n pos : ℕ) (x : α) (hs : s ≠ []) :
    s.foldl (extStep upd) ⟨(.payload s.length, n), pos, x⟩ =
      ⟨finish n, pos + s.length, upd (pos + s.length - 1) ⟨false, false, none, true⟩ x⟩ := by
  obtain ⟨s', b, rfl⟩ : ∃ s' b, s = s' ++ [b] := by
    cases hb : s.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hb) hs
    | cons b s' => exact ⟨s'.reverse, b, by rw [← List.reverse_reverse s, hb, List.reverse_cons]⟩
  have hshort : ∀ (r pos : ℕ) (x : α), s'.length < r →
      s'.foldl (extStep upd) ⟨(.payload r, n), pos, x⟩ =
        ⟨(.payload (r - s'.length), n), pos + s'.length, x⟩ := by
    refine List.rec (fun _ _ _ _ ↦ rfl) (fun b s' ih r pos x h ↦ ?_) s'
    have hr : r ≠ 1 := by simp only [List.length_cons] at h; omega
    have he : r - 1 - s'.length = r - (s'.length + 1) := by omega
    have hp : pos + 1 + s'.length = pos + (s'.length + 1) := by omega
    rw [List.foldl_cons]
    simp only [extStep, step, eventS, hr, ↓reduceIte, hu]
    rw [ih (r - 1) (pos + 1) x (by simp only [List.length_cons] at h; omega), List.length_cons, he,
      hp]
  rw [List.foldl_append, List.length_append, List.length_singleton,
    hshort (s'.length + 1) pos x (by omega), List.foldl_cons, List.foldl_nil]
  have hr : s'.length + 1 - s'.length = 1 := by omega
  have hp : pos + s'.length + 1 = pos + (s'.length + 1) := by omega
  have hq : pos + (s'.length + 1) - 1 = pos + s'.length := by omega
  simp only [extStep, step, eventS, hr, ↓reduceIte, hp, hq]

end

end Geb.SizeBounded.Logspace.WTree
