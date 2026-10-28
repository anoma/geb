/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Geb.Prototypes.InteractionNet.WiringSplice

set_option doc.verso true in
/-!
# Active pairs of cells

An active pair consists of two cells whose principal ports share a wire. Each principal
port has exactly one partner, so two active pairs that share a cell are the same pair,
possibly with their orientation reversed. Distinct active pairs therefore occupy disjoint
cells, even when their auxiliary ports are connected to one another.

## Main definitions

* {lit}`PortNet.principal` — port zero of a cell.
* {lit}`PortNet.Active` — a wire joining two principal ports.

## Main statements

* {lit}`PortNet.active_ne` — the two cells in an active pair are distinct.
* {lit}`PortNet.active_right_unique` — a principal port has at most one active partner.
* {lit}`PortNet.active_disjoint` — different active pairs have disjoint cells.

## References

* \[DeFalco2010\], Proposition 5.3, uses this disjointness in the interaction diamond.

## Tags

interaction net, active pair, principal port, disjointness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w

variable {α : Type u} {C : Type v} {Γ : Type w}

/-- The principal port of a cell, as an endpoint of a net. -/
def principal (arity : α → ℕ) (label : C → α) (c : C) : Endpoint arity label Γ :=
  .inr ⟨c, 0⟩

variable {arity : α → ℕ} {label : C → α}

/-- Two cells form an active pair when their principal ports share a wire. -/
def Active (n : PortNet arity label Γ) (a b : C) : Prop :=
  n.wiring.partner (principal arity label a) = principal arity label b

/-- Reversing a principal wire reverses the orientation of its active pair. -/
theorem active_symm {n : PortNet arity label Γ} {a b : C} (h : n.Active a b) :
    n.Active b a := by
  change n.wiring.partner (principal arity label b) = principal arity label a
  rw [← h, Wiring.partner_partner]

/-- An active pair has two different cells. -/
theorem active_ne {n : PortNet arity label Γ} {a b : C} (h : n.Active a b) : a ≠ b := by
  intro hab
  subst b
  exact n.wiring.fixedPointFree (principal arity label a) h

/-- A principal port has at most one active partner. -/
theorem active_right_unique {n : PortNet arity label Γ} {a b c : C}
    (h : n.Active a b) (h' : n.Active a c) : b = c :=
  congrArg Sigma.fst (Sum.inr.inj (h.symm.trans h'))

/-- Once the first cell is outside another pair, its active partner is outside it too. -/
theorem active_disjoint {n : PortNet arity label Γ} {a b c d : C}
    (h : n.Active a b) (h' : n.Active c d) (hac : a ≠ c) (had : a ≠ d) :
    b ≠ c ∧ b ≠ d := by
  constructor
  · intro hbc
    subst c
    exact had (active_right_unique (active_symm h) h')
  · intro hbd
    subst d
    exact hac (active_right_unique (active_symm h) (active_symm h'))

/-- Removing an active pair's principal wire leaves a matching on the other endpoints. -/
theorem active_closed {n : PortNet arity label Γ} {a b : C} (h : n.Active a b)
    (p : Endpoint arity label Γ)
    (hp : p ≠ principal arity label a ∧ p ≠ principal arity label b) :
    n.wiring.partner p ≠ principal arity label a ∧
      n.wiring.partner p ≠ principal arity label b := by
  constructor
  · intro he
    exact hp.2 ((n.wiring.partner_eq_iff.mp he).trans h)
  · intro he
    exact hp.1 ((n.wiring.partner_eq_iff.mp he).trans (active_symm h))

end Geb.InteractionNet.PortNet

end
