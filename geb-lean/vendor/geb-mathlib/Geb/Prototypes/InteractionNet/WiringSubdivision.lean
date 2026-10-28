/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Inserting a wire before an endpoint

Adding a separate wire and splicing one of its ends to an existing endpoint merely
moves that endpoint to the wire's other end. The matching of surviving endpoints is
unchanged and no closed wire is created. This is the local cancellation used when a
variable fragment is attached to a replacement root.

## Main definitions

* {lit}`Wiring.wire` — one wire with two Boolean endpoints.
* {lit}`Wiring.shiftEndpoint` — replace a selected endpoint by the new external wire end.

## Main statements

* {lit}`Wiring.shiftEndpoint_respects` — splicing the new wire preserves the old matching.
* {lit}`Wiring.shiftEndpoint_loopDelta` — endpoint extension creates no closed component.

## Tags

interaction net, wire, subdivision, substitution, cancellation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

variable {P : Type*} [DecidableEq P]

/-- One wire, with its two ends indexed by Boolean values. -/
def wire : Wiring Bool where
  partner := Bool.not
  involutive p := by cases p <;> rfl
  fixedPointFree p h := by cases p <;> cases h

/-- Replace one endpoint by a new wire end while retaining every other endpoint. -/
def shiftEndpoint (p : P) : P ↪ Bool ⊕ P where
  toFun q := if q = p then .inl false else .inr q
  inj' q r h := by
    by_cases hq : q = p <;> by_cases hr : r = p
    · exact hq.trans hr.symm
    · simp only [hq, hr, ↓reduceIte] at h
      cases h
    · simp only [hq, hr, ↓reduceIte] at h
      cases h
    · simpa only [hq, hr, ↓reduceIte, Sum.inr.injEq] using h

/-- Moving an endpoint along a new wire preserves every surviving partner. -/
theorem shiftEndpoint_respects (w : Wiring P) (p : P) :
    Respects (shiftEndpoint p) w ((wire.sum w).force (.inl true) (.inr p)) := by
  intro q
  change ((wire.sum w).force (.inl true) (.inr p)).partner
    (if q = p then .inl false else .inr q) =
      if w.partner q = p then .inl false else .inr (w.partner q)
  by_cases hq : q = p
  · subst q
    rw [force_apply _ (by intro h; cases h)]
    simp [wire, sum, w.fixedPointFree p]
  · rw [force_apply _ (by intro h; cases h)]
    simp [hq, wire, sum]

/-- Splicing a separate wire to an existing endpoint never creates a closed wire. -/
theorem shiftEndpoint_loopDelta (w : Wiring P) (p : P) :
    (wire.sum w).loopDelta (.inl true) (.inr p) = 0 := rfl

/-- Include a disjoint wire alongside an already embedded collection of endpoints. -/
def adjoinWire {Q : Type*} (e : P ↪ Q) (a b : Q) (hab : a ≠ b)
    (ha : ∀ p, e p ≠ a) (hb : ∀ p, e p ≠ b) : Bool ⊕ P ↪ Q where
  toFun p := match p with | .inl false => a | .inl true => b | .inr p => e p
  inj' := by
    rintro (u | p) (v | q) h
    · cases u <;> cases v
      · rfl
      · exact (hab h).elim
      · exact (hab h.symm).elim
      · rfl
    · cases u
      · exact (ha q h.symm).elim
      · exact (hb q h.symm).elim
    · cases v
      · exact (ha p h).elim
      · exact (hb p h).elim
    · exact congrArg Sum.inr (e.injective h)

/-- Moving along an adjoined wire changes only the selected endpoint's ambient position. -/
theorem adjoinWire_shift {Q : Type*} (e : P ↪ Q) (a b : Q) (hab : a ≠ b)
    (ha : ∀ p, e p ≠ a) (hb : ∀ p, e p ≠ b) (p q : P) :
    ((shiftEndpoint p).trans (adjoinWire e a b hab ha hb)) q = if q = p then a else e q := by
  change (adjoinWire e a b hab ha hb) (if q = p then .inl false else .inr q) = _
  split_ifs <;> rfl

/-- Endpoint extension can be performed inside an ambient matching containing the new wire. -/
theorem Respects.shiftEndpoint {Q : Type*} [DecidableEq Q] {e : P ↪ Q}
    {s : Wiring P} {t : Wiring Q} (h : Respects e s t) (p : P) (a b : Q)
    (hab : a ≠ b) (ha : ∀ q, e q ≠ a) (hb : ∀ q, e q ≠ b) (wire_eq : t.partner a = b) :
    Respects ((Wiring.shiftEndpoint p).trans (adjoinWire e a b hab ha hb))
      s (t.force b (e p)) := by
  have he : Respects (adjoinWire e a b hab ha hb) (wire.sum s) t := by
    rintro (bit | q)
    · cases bit
      · exact wire_eq
      · change t.partner b = a
        have hr := congrArg t.partner wire_eq
        simpa only [partner_partner] using hr.symm
    · exact h q
  exact (shiftEndpoint_respects s p).trans (he.force (by intro h; cases h))

/-- A wire avoiding the cuts actually processed is unchanged by finite gluing. -/
theorem glue_keeps_on {I : Type*} (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ)
    {p q : P} (hp : ∀ i ∈ order, ∀ b, p ≠ ports (i, b))
    (hq : ∀ i ∈ order, ∀ b, q ≠ ports (i, b)) (hw : s.1.partner p = q) :
    (glue ports order s).1.partner p = q := by
  revert s
  refine List.rec (fun _ _ _ h ↦ h) (fun i order ih hp hq s hw ↦ ?_) order hp hq
  apply ih (fun j hj ↦ hp j (List.mem_cons_of_mem _ hj))
    (fun j hj ↦ hq j (List.mem_cons_of_mem _ hj)) (glueAt ports s i)
  exact force_keeps s.1 (pair_ne ports i) (hp i List.mem_cons_self false)
    (hp i List.mem_cons_self true) (hq i List.mem_cons_self false)
    (hq i List.mem_cons_self true) hw

/-- Distinct cuts with one side's partners outside every cut create no closed wires. -/
theorem glue_loops_of_free_side {I : Type*} (ports : I × Bool ↪ P) (order : List I)
    (unique : order.Nodup) (s : Wiring P × ℕ) (side : Bool)
    (free : ∀ i ∈ order, ∀ j ∈ order, ∀ b,
      s.1.partner (ports (i, side)) ≠ ports (j, b)) :
    (glue ports order s).2 = s.2 := by
  revert s unique
  refine List.rec (fun _ _ _ ↦ rfl) (fun i order ih unique s free ↦ ?_) order
  have hn := List.nodup_cons.mp unique
  have hl : s.1.loopDelta (ports (i, false)) (ports (i, true)) = 0 := by
    apply if_neg
    intro h
    cases side with
    | false => exact free i List.mem_cons_self i List.mem_cons_self true h
    | true =>
      exact free i List.mem_cons_self i List.mem_cons_self false
        (s.1.partner_eq_iff.mp h).symm
  change (glue ports order (glueAt ports s i)).2 = s.2
  have he : (glue ports order (glueAt ports s i)).2 = (glueAt ports s i).2 := by
    apply ih hn.2
    intro j hj k hk b
    have hji : j ≠ i := fun h ↦ hn.1 (h ▸ hj)
    have hp : (s.1.force (ports (i, false)) (ports (i, true))).partner (ports (j, side)) =
        s.1.partner (ports (j, side)) :=
      force_keeps s.1 (pair_ne ports i)
        (pair_ne_of_ne ports hji side false) (pair_ne_of_ne ports hji side true)
        (free j (List.mem_cons_of_mem _ hj) i List.mem_cons_self false)
        (free j (List.mem_cons_of_mem _ hj) i List.mem_cons_self true) rfl
    exact hp.trans_ne (free j (List.mem_cons_of_mem _ hj) k (List.mem_cons_of_mem _ hk) b)
  simpa only [glueAt, hl, Nat.add_zero] using he

/-- Distinct cuts whose right partners avoid every cut cannot create a closed wire. -/
theorem glue_loops_of_free_right {I : Type*} (ports : I × Bool ↪ P) (order : List I)
    (unique : order.Nodup) (s : Wiring P × ℕ)
    (free : ∀ i ∈ order, ∀ j ∈ order, ∀ b,
      s.1.partner (ports (i, true)) ≠ ports (j, b)) :
    (glue ports order s).2 = s.2 :=
  glue_loops_of_free_side ports order unique s true free

end Geb.InteractionNet.Wiring

end
