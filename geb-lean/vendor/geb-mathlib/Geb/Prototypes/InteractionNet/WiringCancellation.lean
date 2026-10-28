/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.WiringSubdivision
public import Geb.Prototypes.InteractionNet.WiringCompose

set_option doc.verso true in
/-!
# Closing a distinguished pair of wire endpoints

Two Boolean endpoints can be joined and removed from a matching. Their former partners
are connected, unless the endpoints already formed a wire, in which case the operation
creates one closed component. The remaining matching embeds in the original endpoint
space after its distinguished pair has been forced.

## Main definitions

* {lit}`Wiring.closeWire` — close the distinguished endpoints and retain the closed component.

## Main statements

* {lit}`Wiring.closeWire_respects` — the remaining matching agrees with the ambient splice.

## Tags

interaction net, wire, splice, cancellation, closed component
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

variable {P : Type*}

/-- Removing both Boolean positions leaves precisely the other summand. -/
def closeWireEquiv (P : Type*) :
    {p : Bool ⊕ P // p ≠ .inl false ∧ p ≠ .inl true} ≃ P where
  toFun p := match p with
    | ⟨.inl false, h⟩ => (h.1 rfl).elim
    | ⟨.inl true, h⟩ => (h.2 rfl).elim
    | ⟨.inr p, _⟩ => p
  invFun p := ⟨.inr p, by constructor <;> intro h <;> cases h⟩
  left_inv p := by
    rcases p with ⟨b | p, h⟩
    · cases b
      · exact (h.1 rfl).elim
      · exact (h.2 rfl).elim
    · rfl
  right_inv _ := rfl

variable [DecidableEq P]

/-- Join and remove the distinguished endpoints, counting a closed wire when they were paired. -/
def closeWire (w : Wiring (Bool ⊕ P)) : Wiring P × ℕ :=
  ((w.splice (.inl false) (.inl true) (by intro h; cases h)).map (closeWireEquiv P),
    w.loopDelta (.inl false) (.inl true))

/-- The remaining endpoints retain their ambient partners after closing the distinguished pair. -/
theorem closeWire_respects (w : Wiring (Bool ⊕ P)) :
    Respects (.inr) (closeWire w).1 (w.force (.inl false) (.inl true)) :=
  (respects_map_symm (closeWireEquiv P) _).trans
    (respects_restrict _ _ (w.force_closed (by intro h; cases h)))

/-- Closing a distinguished pair joins the two wire partners at its other ends. -/
theorem closeWire_partner (w : Wiring (Bool ⊕ P)) {a b : P}
    (ha : w.partner (.inl false) = .inr a) (hb : w.partner (.inl true) = .inr b) :
    (closeWire w).1.partner a = b := by
  apply Sum.inr_injective (α := Bool)
  apply (closeWire_respects w a).symm.trans
  change (w.force (.inl false) (.inl true)).partner (.inr a) = .inr b
  have h := (w.partner_eq_iff.mp ha).symm
  rw [force_apply w (by intro h; cases h)]
  simp only [Sum.inr_ne_inl, ↓reduceIte, h, hb]

/-- A matching that avoids both distinguished positions survives their closure unchanged. -/
theorem closeWire_respects_of_inr {Q : Type*} {e : Q ↪ P} {v : Wiring Q}
    {w : Wiring (Bool ⊕ P)} (h : Respects (e.trans .inr) v w) :
    Respects e v (closeWire w).1 := by
  intro p
  apply Sum.inr_injective (α := Bool)
  apply (closeWire_respects w (e p)).symm.trans
  exact force_keeps w (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) (h p)

/-- Attach both ends of a separate wire to the distinguished endpoints of another matching. -/
def closeWirePorts (P : Type*) : Bool × Bool ↪ Bool ⊕ (Bool ⊕ P) where
  toFun p := if p.2 then .inr (.inl p.1) else .inl p.1
  inj' := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    cases b <;> cases c <;> simp_all

/-- Closing through a separate wire gives the same remaining matching and closed-wire count. -/
theorem closeWire_subdivision (w : Wiring (Bool ⊕ P)) (loops : ℕ) :
    let s := glue (closeWirePorts P) [true, false] (wire.sum w, loops)
    Respects (Function.Embedding.inr.trans .inr) (closeWire w).1 s.1 ∧
      s.2 = loops + (closeWire w).2 := by
  let e := shiftEndpoint (Sum.inl true : Bool ⊕ P)
  let v := (wire.sum w).force (.inl true) (.inr (.inl true))
  have hs : Respects e w v := shiftEndpoint_respects w (.inl true)
  have hf := hs.force (a := .inl false) (b := .inl true) (by intro h; cases h)
  have he : e (.inl false) = .inr (.inl false) := rfl
  have ht : e (.inl true) = .inl false := by
    change (if (Sum.inl true : Bool ⊕ P) = .inl true then (Sum.inl false : Bool ⊕ (Bool ⊕ P))
      else .inr (.inl true)) = _
    exact if_pos rfl
  rw [he, ht, force_comm v (by intro h; cases h)] at hf
  have hm := (closeWire_respects w).trans hf
  have hem : Function.Embedding.inr.trans e =
      (Function.Embedding.inr.trans .inr : P ↪ Bool ⊕ (Bool ⊕ P)) := by
    ext p
    rfl
  rw [hem] at hm
  refine ⟨hm, ?_⟩
  have hd := hs.loopDelta (.inl true) (.inl false)
  rw [ht, he] at hd
  have hc : w.loopDelta (.inl true) (.inl false) = (closeWire w).2 := by
    change w.loopDelta (.inl true) (.inl false) = w.loopDelta (.inl false) (.inl true)
    by_cases h : w.partner (.inl false) = .inl true
    · have hr := (w.partner_eq_iff.mp h).symm
      simp only [loopDelta, h, hr, ↓reduceIte]
    · have hr : w.partner (.inl true) ≠ .inl false :=
        fun hr ↦ h (w.partner_eq_iff.mpr hr.symm)
      simp only [loopDelta, h, hr, ↓reduceIte]
  change loops + 0 + v.loopDelta (.inl false) (.inr (.inl false)) = _
  rw [← hd, hc, Nat.add_zero]

/-- Closing distinguished endpoints leaves a disjoint matching unchanged. -/
theorem closeWire_sum {Q : Type*} [DecidableEq Q] (w : Wiring (Bool ⊕ P)) (v : Wiring Q) :
    closeWire ((w.sum v).map (Equiv.sumAssoc Bool P Q)) =
      ((closeWire w).1.sum v, (closeWire w).2) := by
  let e := Equiv.sumAssoc Bool P Q
  have h := ((closeWire_respects w).sum (respects_refl v)).trans
    (respects_map e ((w.force (.inl false) (.inl true)).sum v))
  rw [force_sum_left w v (by intro h; cases h), force_map e _ (by intro h; cases h)] at h
  have he : (Function.Embedding.sumMap (.inr) (.refl Q)).trans e.toEmbedding =
      (Function.Embedding.inr : P ⊕ Q ↪ Bool ⊕ (P ⊕ Q)) := by
    ext p
    cases p <;> rfl
  rw [he] at h
  apply Prod.ext
  · have hr := closeWire_respects ((w.sum v).map e)
    have hw := hr.map_eq h (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [map_refl] using hw
  · cases hw : w.partner (.inl false) with
    | inl b => simp [closeWire, loopDelta, map, sum, Equiv.sumAssoc, hw]
    | inr p => simp [closeWire, loopDelta, map, sum, Equiv.sumAssoc, hw]

end Geb.InteractionNet.Wiring

end
