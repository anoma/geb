/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Equiv.Basic

set_option doc.verso true in
/-!
# Wire matchings and transport

A wiring pairs each endpoint with exactly one distinct endpoint. It is a fixed-point-free
involution, transported along equivalences by conjugation. Closed wires without endpoints
are accounted for separately in a net. This separates the ordinary wires and loops of
\[DeFalco2010\], Definition 3.1.

## Main definitions

* {lit}`Wiring` — a fixed-point-free involution on endpoints.
* {lit}`Wiring.map` — transport along an endpoint equivalence.

## Main statements

* {lit}`Wiring.map_trans` — successive endpoint renamings compose.
* {lit}`Wiring.map_symm_map` — reversing a renaming recovers the original wiring.

## References

* \[DeFalco2010\], Definitions 3.1 and 3.2.

## Tags

interaction net, matching, involution, wire, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

universe u v w

/-- A wire matching: each endpoint has a distinct partner, and partnership is involutive. -/
@[ext] structure Wiring (P : Type u) : Type u where
  /-- The other endpoint of a wire. -/
  partner : P → P
  /-- Traversing the same wire twice returns to its starting endpoint. -/
  involutive : Function.Involutive partner
  /-- A wire has two distinct endpoints. -/
  fixedPointFree : ∀ p, partner p ≠ p

namespace Wiring

variable {P : Type u} {Q : Type v} {R : Type w}

/-- Traversing wires is a permutation whose inverse is itself. -/
def equiv (w : Wiring P) : Equiv.Perm P :=
  w.involutive.toPerm w.partner

/-- Traversing a wire twice gives the original endpoint. -/
@[simp] theorem partner_partner (w : Wiring P) (p : P) :
    w.partner (w.partner p) = p := w.involutive p

/-- Transport a matching along an equivalence of endpoint types. -/
def map (e : P ≃ Q) (w : Wiring P) : Wiring Q where
  partner p := e (w.partner (e.symm p))
  involutive p := by simp only [Equiv.symm_apply_apply, partner_partner, Equiv.apply_symm_apply]
  fixedPointFree p h := w.fixedPointFree (e.symm p) (by
    have he := congrArg e.symm h
    simpa only [Equiv.symm_apply_apply] using he)

/-- Transport commutes with the partner operation. -/
@[simp] theorem map_partner (e : P ≃ Q) (w : Wiring P) (p : P) :
    (w.map e).partner (e p) = e (w.partner p) := by
  simp only [map, Equiv.symm_apply_apply]

/-- A wire after renaming is the corresponding wire before renaming. -/
theorem map_partner_eq_iff (e : P ≃ Q) (w : Wiring P) (p q : Q) :
    (w.map e).partner p = q ↔ w.partner (e.symm p) = e.symm q := by
  constructor
  · intro h
    change e (w.partner (e.symm p)) = q at h
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
  · intro h
    change e (w.partner (e.symm p)) = q
    rw [h, Equiv.apply_symm_apply]

/-- The identity endpoint renaming leaves a matching unchanged. -/
@[simp] theorem map_refl (w : Wiring P) : w.map (Equiv.refl P) = w := by
  ext p
  rfl

/-- Transport by a composite equivalence is successive transport. -/
theorem map_trans (e : P ≃ Q) (f : Q ≃ R) (w : Wiring P) :
    w.map (e.trans f) = (w.map e).map f := by
  ext p
  rfl

/-- Transport back along the inverse equivalence recovers the original matching. -/
@[simp] theorem map_symm_map (e : P ≃ Q) (w : Wiring P) : (w.map e).map e.symm = w := by
  ext p
  simp only [map, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- Restrict a matching to a collection of endpoints closed under taking partners. -/
def restrict (w : Wiring P) (s : P → Prop) (h : ∀ p, s p → s (w.partner p)) :
    Wiring {p // s p} where
  partner p := ⟨w.partner p, h p p.property⟩
  involutive p := Subtype.ext (w.partner_partner p)
  fixedPointFree p he := w.fixedPointFree p (congrArg Subtype.val he)

/-- Restricting endpoints leaves every surviving partner unchanged. -/
@[simp] theorem restrict_partner (w : Wiring P) (s : P → Prop)
    (h : ∀ p, s p → s (w.partner p)) (p : {p // s p}) :
    ((w.restrict s h).partner p).val = w.partner p := rfl

/-- Disjoint union of matchings, with no wire crossing between the two summands. -/
def sum (w : Wiring P) (v : Wiring Q) : Wiring (P ⊕ Q) where
  partner := Sum.map w.partner v.partner
  involutive p := by
    cases p with
    | inl p => exact congrArg Sum.inl (w.partner_partner p)
    | inr p => exact congrArg Sum.inr (v.partner_partner p)
  fixedPointFree p h := by
    cases p with
    | inl p => exact w.fixedPointFree p (Sum.inl.inj h)
    | inr p => exact v.fixedPointFree p (Sum.inr.inj h)

/-- The left summand's wires are unchanged by disjoint union. -/
@[simp] theorem sum_inl (w : Wiring P) (v : Wiring Q) (p : P) :
    (w.sum v).partner (.inl p) = .inl (w.partner p) := rfl

/-- The right summand's wires are unchanged by disjoint union. -/
@[simp] theorem sum_inr (w : Wiring P) (v : Wiring Q) (p : Q) :
    (w.sum v).partner (.inr p) = .inr (v.partner p) := rfl

end Wiring

end Geb.InteractionNet

end
