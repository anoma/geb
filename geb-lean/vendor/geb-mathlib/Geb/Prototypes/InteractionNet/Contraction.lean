/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.OpenPair
public import Geb.Prototypes.InteractionNet.PortNetPlug
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Graph contraction

Contracting an active pair consumes its two cells and principal wire, inserts the
rule's right-hand side, and reconnects each auxiliary port to the corresponding boundary
port of the replacement. The construction preserves the external boundary and produces
a wire matching by construction. The cells of the result distinguish surviving cells
from freshly inserted cells, independently of how a concrete runtime allocates them.

## Main definitions

* {lit}`PortRule` — a finite right-hand side with the active pair's ordered boundary.
* {lit}`PortNet.contract` — replace any selected active pair by a matching right-hand side.

## Main statements

* {lit}`PortNet.contract_active` — another active pair survives a contraction.
* {lit}`PortNet.contract_rhs_active` — a replacement's internal active pairs remain active.

## References

* \[DeFalco2010\], Definitions 5.1 and 5.2 and Proposition 5.3.

## Tags

interaction net, graph reduction, contraction, active pair, allocation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

universe u v w x

variable {α : Type u}

/-- A finite rule body, indexed by cells, with the left then right auxiliary boundary. -/
abbrev PortRule (arity : α → ℕ) (a b : α) :=
  Σ cells : ℕ, Σ label : Fin cells → α, PortNet arity label (Fin (arity a) ⊕ Fin (arity b))

namespace PortNet

open scoped FinEnum

variable {C : Type v} {D : Type w} {Γ : Type x}
variable [DecidableEq C] [DecidableEq D] [DecidableEq Γ]
variable {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- Replace an active pair, enumerating its auxiliary boundary in a canonical finite order. -/
def contract (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    PortNet arity (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ :=
  (n.openPair h).plug rhs (FinEnum.toList _) FinEnum.nodup_toList FinEnum.mem_toList

/-- The cells of another active pair survive, and their principal wire remains intact. -/
theorem contract_active (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity label' (PairBoundary arity label a b))
    (c d : RemainingCell a b) (hcd : n.Active c d) :
    (n.contract h rhs).Active (.inl c) (.inl d) :=
  plug_left_active _ _ _ _ _ (n.openPair_active h c d hcd)

/-- Insertion preserves the replacement's internal active pairs. -/
theorem contract_rhs_active (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity label' (PairBoundary arity label a b)) {c d : D}
    (hcd : rhs.Active c d) : (n.contract h rhs).Active (.inr c) (.inr d) :=
  plug_right_active _ _ _ _ _ hcd

end PortNet

end Geb.InteractionNet

end
