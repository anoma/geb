/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ActivePair

set_option doc.verso true in
/-!
# Opening an active pair

Removing the two cells of an active pair exposes their auxiliary ports as an ordered
boundary. Their shared principal wire is consumed. The other wires, external boundary
and closed components remain available to the replacement net.

## Main definitions

* {lit}`PortNet.RemainingCell` — cells outside the selected pair.
* {lit}`PortNet.PairBoundary` — the ordered auxiliary ports of the pair.
* {lit}`PortNet.openEndpoint` — expose the pair's auxiliary ports and keep other cell ports.
* {lit}`PortNet.closeEndpoint` — locate an exposed endpoint in the original net.

## References

* \[DeFalco2010\], Sections 4 and 5, describe the context decomposition of an active pair.

## Tags

interaction net, active pair, context, boundary, cell removal
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w

variable {α : Type u} {C : Type v} {Γ : Type w}

/-- The cells outside a selected pair. -/
abbrev RemainingCell (a b : C) := {c // c ≠ a ∧ c ≠ b}

/-- The selected cells' auxiliary ports, in their original order. -/
abbrev PairBoundary (arity : α → ℕ) (label : C → α) (a b : C) :=
  Fin (arity (label a)) ⊕ Fin (arity (label b))

/-- Endpoints other than the selected principal wire. -/
abbrev PairRemainder (arity : α → ℕ) (label : C → α) (Γ : Type w) (a b : C) :=
  {p : Endpoint arity label Γ //
    p ≠ principal arity label a ∧ p ≠ principal arity label b}

/-- The endpoint type after exposing the selected pair's auxiliary ports. -/
abbrev OpenEndpoint (arity : α → ℕ) (label : C → α) (Γ : Type w) (a b : C) :=
  Endpoint arity (fun c : RemainingCell a b ↦ label c) (Γ ⊕ PairBoundary arity label a b)

/-- The numeric position of an auxiliary port is never zero. -/
theorem aux_ne_principal (arity : α → ℕ) (label : C → α) (a b : C)
    (p : Fin (arity (label a))) :
    (Sum.inr ⟨a, p.succ⟩ : Endpoint arity label Γ) ≠ principal arity label b := by
  intro h
  have hpos := congrArg (fun q : CellPort arity label ↦ q.2.val) (Sum.inr.inj h)
  exact Nat.noConfusion hpos

/-- Locate an endpoint of the opened context in the original net. -/
def closeEndpoint (arity : α → ℕ) (label : C → α) (a b : C) :
    OpenEndpoint arity label Γ a b → PairRemainder arity label Γ a b
  | .inl (.inl γ) => ⟨.inl γ, by constructor <;> intro h <;> cases h⟩
  | .inl (.inr (.inl p)) =>
    ⟨.inr ⟨a, p.succ⟩, aux_ne_principal arity label a a p,
      aux_ne_principal arity label a b p⟩
  | .inl (.inr (.inr p)) =>
    ⟨.inr ⟨b, p.succ⟩, aux_ne_principal arity label b a p,
      aux_ne_principal arity label b b p⟩
  | .inr ⟨c, p⟩ => ⟨.inr ⟨c.val, p⟩,
      (fun h ↦ c.property.1 (congrArg Sigma.fst (Sum.inr.inj h))),
      (fun h ↦ c.property.2 (congrArg Sigma.fst (Sum.inr.inj h)))⟩

variable [DecidableEq C]

/-- Move a selected cell's auxiliary ports to the boundary and preserve every other endpoint. -/
def openEndpoint (arity : α → ℕ) (label : C → α) (a b : C) :
    PairRemainder arity label Γ a b → OpenEndpoint arity label Γ a b := by
  rintro ⟨p, hp⟩
  cases p with
  | inl γ => exact .inl (.inl γ)
  | inr p =>
    rcases p with ⟨c, p⟩
    by_cases hca : c = a
    · subst c
      cases p using Fin.cases with
      | zero => exact (hp.1 rfl).elim
      | succ p => exact .inl (.inr (.inl p))
    · by_cases hcb : c = b
      · subst c
        cases p using Fin.cases with
        | zero => exact (hp.2 rfl).elim
        | succ p => exact .inl (.inr (.inr p))
      · exact .inr ⟨⟨c, hca, hcb⟩, p⟩

/-- Closing an opened endpoint returns the original endpoint. -/
theorem close_openEndpoint (arity : α → ℕ) (label : C → α) (a b : C)
    (p : PairRemainder arity label Γ a b) :
    closeEndpoint arity label a b (openEndpoint arity label a b p) = p := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl γ => rfl
  | inr p =>
    rcases p with ⟨c, p⟩
    by_cases hca : c = a
    · subst c
      cases p using Fin.cases with
      | zero => exact (hp.1 rfl).elim
      | succ p => simp [openEndpoint, closeEndpoint]
    · by_cases hcb : c = b
      · subst c
        cases p using Fin.cases with
        | zero => exact (hp.2 rfl).elim
        | succ p => simp [openEndpoint, closeEndpoint, hca]
      · simp [openEndpoint, closeEndpoint, hca, hcb]

/-- Opening a located context endpoint recovers the same context endpoint. -/
theorem open_closeEndpoint (arity : α → ℕ) (label : C → α) {a b : C} (hab : a ≠ b)
    (p : OpenEndpoint arity label Γ a b) :
    openEndpoint arity label a b (closeEndpoint arity label a b p) = p := by
  rcases p with ((γ | (p | p)) | ⟨c, p⟩)
  · rfl
  · simp [closeEndpoint, openEndpoint]
  · simp [closeEndpoint, openEndpoint, hab.symm]
  · simp [closeEndpoint, openEndpoint, c.property.1, c.property.2]

/-- Removing the principal wire exposes exactly the boundary of the pair's replacement. -/
def openEndpointEquiv (arity : α → ℕ) (label : C → α) {a b : C} (hab : a ≠ b) :
    PairRemainder arity label Γ a b ≃ OpenEndpoint arity label Γ a b where
  toFun := openEndpoint arity label a b
  invFun := closeEndpoint arity label a b
  left_inv := close_openEndpoint arity label a b
  right_inv := open_closeEndpoint arity label hab

/-- Consume the principal wire and expose the active pair's auxiliary ports as a boundary. -/
def openPair {arity : α → ℕ} {label : C → α} (n : PortNet arity label Γ)
    {a b : C} (h : n.Active a b) :
    PortNet arity (fun c : RemainingCell a b ↦ label c) (Γ ⊕ PairBoundary arity label a b) :=
  ⟨(n.wiring.restrict _ (active_closed h)).map
      (openEndpointEquiv arity label (active_ne h)), n.loops⟩

/-- Opening a pair preserves every active pair on the remaining cells. -/
theorem openPair_active {arity : α → ℕ} {label : C → α} (n : PortNet arity label Γ)
    {a b : C} (h : n.Active a b) (c d : RemainingCell a b) (hcd : n.Active c d) :
    (n.openPair h).Active c d := by
  change ((n.wiring.restrict _ (active_closed h)).map
    (openEndpointEquiv arity label (active_ne h))).partner _ = _
  rw [Wiring.map_partner_eq_iff]
  exact Subtype.ext hcd

end Geb.InteractionNet.PortNet

end
