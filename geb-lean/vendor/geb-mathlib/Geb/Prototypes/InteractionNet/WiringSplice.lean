/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.Wiring

set_option doc.verso true in
/-!
# Splicing wires

Joining two endpoints removes them and joins their former partners. On the original
endpoint type, the same surgery isolates the two endpoints as a detached wire. Conjugating
the matching by a transposition implements this surgery while preserving the matching
invariant by construction. When the endpoints were already paired, removing them creates
one closed wire, which the net must retain.

## Main definitions

* {lit}`Wiring.force` — isolate a chosen pair and splice their former incident wires.

## References

* \[DeFalco2010\], Section 2 and Definition 4.1, describe gluing by following wires
  through identified boundary ports and retaining closed wire components.

## Tags

interaction net, wire, splicing, gluing, matching
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

universe u v

variable {P : Type u} [DecidableEq P]

/-- Exchanging two endpoints twice is the identity, using decidable endpoint equality. -/
theorem exchange_involutive (a b : P) :
    Function.Involutive (Equiv.swapCore a b) := by
  intro p
  simp only [Equiv.swapCore]
  split_ifs <;> simp_all

/-- The endpoint transposition with a constructive inverse proof. -/
def exchange (a b : P) : Equiv.Perm P :=
  (exchange_involutive a b).toPerm (Equiv.swapCore a b)

private theorem exchange_self (a : P) : exchange a a = Equiv.refl P := by
  ext p
  change (if p = a then a else if p = a then a else p) = p
  split_ifs with h <;> simp only [h]

private theorem exchange_left (a b : P) : exchange a b a = b := if_pos rfl

private theorem exchange_right (a b : P) : exchange a b b = a := by
  change (if b = a then b else if b = b then a else b) = a
  by_cases h : b = a <;> simp only [h, ↓reduceIte]

private theorem exchange_other {a b p : P} (ha : p ≠ a) (hb : p ≠ b) :
    exchange a b p = p := by
  change (if p = a then b else if p = b then a else p) = p
  rw [if_neg ha, if_neg hb]

/-- Isolate two endpoints as a wire, reconnecting their previous partners. -/
def force (w : Wiring P) (a b : P) : Wiring P :=
  w.map (exchange b (w.partner a))

/-- Isolating endpoints that already share a wire does not change the matching. -/
theorem force_of_partner_eq (w : Wiring P) {a b : P} (h : w.partner a = b) :
    w.force a b = w := by
  simp only [force, h, exchange_self, map_refl]

/-- The first isolated endpoint is paired with the second. -/
@[simp] theorem force_left (w : Wiring P) {a b : P} (h : a ≠ b) :
    (w.force a b).partner a = b := by
  change exchange b (w.partner a) (w.partner (exchange b (w.partner a) a)) = b
  rw [exchange_other h (w.fixedPointFree a).symm, exchange_right]

/-- The second isolated endpoint is paired with the first. -/
@[simp] theorem force_right (w : Wiring P) {a b : P} (h : a ≠ b) :
    (w.force a b).partner b = a := by
  simpa only [force_left w h] using (w.force a b).partner_partner a

omit [DecidableEq P] in
/-- A partner equality can be reversed by following the wire. -/
theorem partner_eq_iff (w : Wiring P) {a b : P} : w.partner a = b ↔ a = w.partner b :=
  w.involutive.eq_iff

/-- Outside the endpoints and their partners, splicing leaves the wire unchanged. -/
theorem force_other (w : Wiring P) {a b p : P}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpwa : p ≠ w.partner a) (hpwb : p ≠ w.partner b) :
    (w.force a b).partner p = w.partner p := by
  change exchange b (w.partner a) (w.partner (exchange b (w.partner a) p)) = w.partner p
  rw [exchange_other hpb hpwa]
  exact exchange_other
    (fun h ↦ hpwb ((w.partner_eq_iff).mp h))
    (fun h ↦ hpa (w.involutive.injective h))

/-- Splicing joins the original partners of the two endpoints. -/
theorem force_partner_left (w : Wiring P) {a b : P} (hab : a ≠ b) :
    (w.force a b).partner (w.partner a) = w.partner b := by
  change exchange b (w.partner a) (w.partner (exchange b (w.partner a) (w.partner a))) =
    w.partner b
  rw [exchange_right]
  exact exchange_other (w.fixedPointFree b)
    (fun he ↦ hab (w.involutive.injective he).symm)

/-- The original partners also satisfy the reverse wire equation after splicing. -/
theorem force_partner_right (w : Wiring P) {a b : P} (hab : a ≠ b) :
    (w.force a b).partner (w.partner b) = w.partner a := by
  simpa only [force_partner_left w hab] using
    (w.force a b).partner_partner (w.partner a)

/-- A pointwise description of a splice, including its detached endpoints. -/
theorem force_apply (w : Wiring P) {a b : P} (hab : a ≠ b) (p : P) :
    (w.force a b).partner p =
      if p = a then b else if p = b then a else
        if w.partner p = a then w.partner b else
          if w.partner p = b then w.partner a else w.partner p := by
  by_cases hpa : p = a
  · subst p
    simp only [force_left w hab, ↓reduceIte]
  by_cases hpb : p = b
  · subst p
    simp only [hpa, ↓reduceIte, force_right w hab]
  rw [if_neg hpa, if_neg hpb]
  by_cases hwa : w.partner p = a
  · rw [if_pos hwa, (w.partner_eq_iff.mp hwa), force_partner_left w hab]
  by_cases hwb : w.partner p = b
  · rw [if_neg hwa, if_pos hwb, (w.partner_eq_iff.mp hwb), force_partner_right w hab]
  rw [if_neg hwa, if_neg hwb]
  exact force_other w hpa hpb (fun h ↦ hwa (w.partner_eq_iff.mpr h))
    (fun h ↦ hwb (w.partner_eq_iff.mpr h))

/-- The order of the two endpoints within one splice is immaterial. -/
theorem force_comm (w : Wiring P) {a b : P} (hab : a ≠ b) :
    w.force a b = w.force b a := by
  ext p
  rw [force_apply w hab, force_apply w hab.symm]
  split_ifs <;> simp_all

/-- Splicing elsewhere preserves a wire whose endpoints are outside the cut. -/
theorem force_keeps (w : Wiring P) {a b c d : P} (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hw : w.partner a = b) : (w.force c d).partner a = b := by
  rw [force_apply w hcd, if_neg hac, if_neg had, hw,
    if_neg hbc, if_neg hbd]

set_option maxHeartbeats 400000 in
-- Elaboration exceeds the default limit under the pinned v4.29 toolchain.
/-- Two splices with disjoint endpoint pairs commute on the full endpoint type. -/
theorem force_force (w : Wiring P) {a b c d : P} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (w.force a b).force c d = (w.force c d).force a b := by
  ext p
  by_cases hpa : p = a
  · subst p
    rw [force_keeps _ hcd hac had hbc hbd (force_left w hab), force_left _ hab]
  by_cases hpb : p = b
  · subst p
    rw [force_keeps _ hcd hbc hbd hac had (force_right w hab), force_right _ hab]
  by_cases hpc : p = c
  · subst p
    rw [force_left _ hcd,
      force_keeps _ hab hac.symm hbc.symm had.symm hbd.symm (force_left w hcd)]
  by_cases hpd : p = d
  · subst p
    rw [force_right _ hcd,
      force_keeps _ hab had.symm hbd.symm hac.symm hbc.symm (force_right w hcd)]
  simp only [force_apply _ hab, force_apply _ hcd]
  simp only [hpa, hpb, hpc, hpd, hac, had, hbc, hbd,
    Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, ↓reduceIte]
  have ha := w.partner_partner a
  have hb := w.partner_partner b
  have hc := w.partner_partner c
  have hd := w.partner_partner d
  have hp := w.partner_partner p
  split_ifs <;> simp_all

/-- The closed wire created by removing an already connected pair of endpoints. -/
def loopDelta (w : Wiring P) (a b : P) : ℕ := if w.partner a = b then 1 else 0

/-- The creation of a closed wire does not depend on the order of its endpoints. -/
theorem loopDelta_comm (w : Wiring P) (a b : P) : w.loopDelta a b = w.loopDelta b a := by
  have h : w.partner a = b ↔ w.partner b = a :=
    ⟨fun h ↦ (w.partner_eq_iff.mp h).symm, fun h ↦ w.partner_eq_iff.mpr h.symm⟩
  simp only [loopDelta, h]

/-- Disjoint splices create the same total number of closed wires in either order. -/
theorem loopDelta_force (w : Wiring P) {a b c d : P} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    w.loopDelta a b + (w.force a b).loopDelta c d =
      w.loopDelta c d + (w.force c d).loopDelta a b := by
  simp only [loopDelta, force_apply _ hab, force_apply _ hcd]
  simp only [hac, had, Ne.symm hac, Ne.symm hbc, ↓reduceIte]
  have ha := w.partner_partner a
  have hb := w.partner_partner b
  have hc := w.partner_partner c
  have hd := w.partner_partner d
  split_ifs <;> simp_all

/-- An isolated pair cannot be incident to another endpoint. -/
theorem force_closed (w : Wiring P) {a b : P} (hab : a ≠ b) (p : P)
    (hp : p ≠ a ∧ p ≠ b) :
    (w.force a b).partner p ≠ a ∧ (w.force a b).partner p ≠ b := by
  constructor
  · intro h
    exact hp.2 (by simpa only [force_left w hab] using
      (w.force a b).partner_eq_iff.mp h)
  · intro h
    exact hp.1 (by simpa only [force_right w hab] using
      (w.force a b).partner_eq_iff.mp h)

/-- Splice two endpoints and remove their detached pair from the endpoint type. -/
def splice (w : Wiring P) (a b : P) (hab : a ≠ b) : Wiring {p // p ≠ a ∧ p ≠ b} :=
  (w.force a b).restrict (fun p ↦ p ≠ a ∧ p ≠ b) (w.force_closed hab)

/-- A splice reads its surviving partners from the isolated-pair matching. -/
@[simp] theorem splice_partner (w : Wiring P) (a b : P) (hab : a ≠ b)
    (p : {p // p ≠ a ∧ p ≠ b}) :
    ((w.splice a b hab).partner p).val = (w.force a b).partner p := rfl

/-- Renaming endpoints commutes with wire splicing. -/
theorem force_map {Q : Type v} [DecidableEq Q] (e : P ≃ Q) (w : Wiring P)
    {a b : P} (hab : a ≠ b) :
    (w.force a b).map e = (w.map e).force (e a) (e b) := by
  ext q
  obtain ⟨p, rfl⟩ := e.surjective q
  rw [map_partner, force_apply _ (fun h ↦ hab (e.injective h)), force_apply w hab]
  simp only [map_partner, Equiv.apply_eq_iff_eq]
  split_ifs <;> rfl

/-- Renaming endpoints preserves the creation of a closed wire. -/
theorem loopDelta_map {Q : Type v} [DecidableEq Q] (e : P ≃ Q) (w : Wiring P) (a b : P) :
    (w.map e).loopDelta (e a) (e b) = w.loopDelta a b := by
  simp only [loopDelta, map_partner, Equiv.apply_eq_iff_eq]

end Geb.InteractionNet.Wiring

end
