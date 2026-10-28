/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionPorts
public import Geb.Prototypes.InteractionNet.RemainingCells

set_option doc.verso true in
/-!
# Renaming the results of independent contractions

The two orders retain identical original cells and insert identical replacement cells.
The cell bijection induces an endpoint bijection that agrees with the exchange of the
two allocated components in their ambient graph. External boundary positions and internal
port positions are unchanged.

## Main definitions

* {lit}`PortNet.doubleEmbedding` — locate the result of two disjoint contractions.

## Main statements

* {lit}`PortNet.doubleEmbedding_commute` — cell renaming agrees with ambient allocation renaming.

## Tags

interaction net, contraction, renaming, endpoint, allocation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {E : Type x} {Γ : Type y}
variable [DecidableEq C] [DecidableEq D]

/-- Locate surviving and inserted endpoints after two disjoint contractions. -/
def doubleEmbedding (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Endpoint arity
      (Sum.elim (fun p : RemainingCell (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D)
        (.inl ⟨d, had.symm, hbd.symm⟩) ↦ Sum.elim (fun c ↦ label c.val) labelD p.val) labelE) Γ ↪
          DoubleEndpoint arity label labelD labelE Γ a b c d :=
  (contractEmbedding arity (Sum.elim (fun c : RemainingCell a b ↦ label c) labelD) labelE
    (show (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D) ≠
      .inl ⟨d, had.symm, hbd.symm⟩ from
        fun h ↦ hcd (congrArg Subtype.val (Sum.inl.inj h)))).trans
    ((contractEmbedding arity label labelD hab).sumMap (.refl _))

/-- The cell bijection matches both result embeddings after exchanging allocation order. -/
theorem doubleEmbedding_commute [DecidableEq E] (arity : α → ℕ) (label : C → α)
    (labelD : D → α) (labelE : E → α) {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (p : Endpoint arity
      (Sum.elim (fun p : RemainingCell (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D)
        (.inl ⟨d, had.symm, hbd.symm⟩) ↦ Sum.elim (fun c ↦ label c.val) labelD p.val) labelE) Γ) :
    doubleEmbedding arity label labelD labelE hab hcd hac had hbc hbd p =
      sumRightComm _ _ _
        (doubleEmbedding arity label labelE labelD hcd hab hac.symm hbc.symm had.symm hbd.symm
          (endpointEquiv arity (Equiv.refl Γ)
            (contractionCellsEquiv a b c d hac had hbc hbd)
            (contractionCellsEquiv_label label labelD labelE a b c d hac had hbc hbd) p)) := by
  rcases p with γ | ⟨(⟨c | d, h⟩ | e), p⟩ <;> rfl

end Geb.InteractionNet.PortNet

end
