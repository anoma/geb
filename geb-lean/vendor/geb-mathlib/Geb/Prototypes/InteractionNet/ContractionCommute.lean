/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionRenaming
public import Geb.Prototypes.InteractionNet.ContractionSequence
public import Geb.Prototypes.InteractionNet.WiringCompose

set_option doc.verso true in
/-!
# Commutation of independent graph contractions

Two distinct active pairs occupy disjoint cells. Allocating both right-hand sides in a
common graph exposes two disjoint families of wire splices. The families commute, and the
resulting cell bijection preserves symbols, port positions, external boundary positions
and closed wires. Thus either contraction can be followed by the residual of the other,
with isomorphic results.

## Main definitions

* {lit}`PortNet.doubleGlue` — the two families of splices in a common ambient graph.
* {lit}`PortNet.contractCommute` — the boundary-preserving isomorphism between the two results.

## Main statements

* {lit}`PortNet.doubleGlue_comm` — the ambient matchings agree after allocation renaming.
* {lit}`PortNet.doubleGlue_spec` — two graph contractions have the ambient gluing's wires and loops.

## References

* \[DeFalco2010\], Proposition 5.3 and Corollary 5.4.

## Tags

interaction net, confluence, diamond, graph contraction, renaming
-/

set_option doc.verso true
set_option synthInstance.maxSize 256

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {E : Type x} {Γ : Type y}
variable [DecidableEq C] [DecidableEq D] [DecidableEq E] [DecidableEq Γ]
variable {arity : α → ℕ} {label : C → α} {labelD : D → α} {labelE : E → α}

/-- Glue both replacements in the common endpoint space, keeping discarded endpoints isolated. -/
def doubleGlue (n : PortNet arity label Γ) {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (rhs : PortNet arity labelD (PairBoundary arity label a b))
    (rhs' : PortNet arity labelE (PairBoundary arity label c d)) :
    Wiring (DoubleEndpoint arity label labelD labelE Γ a b c d) × ℕ :=
  Wiring.glue (secondPorts arity label labelD labelE a b hcd) (FinEnum.toList _)
    (Wiring.glue (firstPorts arity label labelD labelE hab c d) (FinEnum.toList _)
      ((n.wiring.sum rhs.wiring).sum rhs'.wiring, n.loops + rhs.loops + rhs'.loops))

/-- Disjoint contractions' ambient gluings agree after exchanging replacement components. -/
theorem doubleGlue_comm (n : PortNet arity label Γ) {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (rhs : PortNet arity labelD (PairBoundary arity label a b))
    (rhs' : PortNet arity labelE (PairBoundary arity label c d)) :
    ((n.doubleGlue hcd hab rhs' rhs).1.map (sumRightComm _ _ _),
      (n.doubleGlue hcd hab rhs' rhs).2) = n.doubleGlue hab hcd rhs rhs' := by
  unfold doubleGlue
  rw [← Wiring.glue_map, ← Wiring.glue_map, secondPorts_swap, firstPorts_swap,
    Wiring.map_sumRightComm, Nat.add_right_comm n.loops rhs'.loops rhs.loops]
  exact (Wiring.glue_glue _ _
    (contractionPorts_disjoint arity label labelD labelE hab hcd hac had hbc hbd) _ _ _).symm

/-- The two-step contraction embeds in its ambient gluing and has exactly its closed-wire count. -/
theorem doubleGlue_spec (n : PortNet arity label Γ) {a b c d : C}
    (hab : n.Active a b) (hcd : n.Active c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (rhs : PortNet arity labelD (PairBoundary arity label a b))
    (rhs' : PortNet arity labelE (PairBoundary arity label c d)) :
    let residual := n.contract_active hab rhs ⟨c, hac.symm, hbc.symm⟩
      ⟨d, had.symm, hbd.symm⟩ hcd
    let result := (n.contract hab rhs).contract residual rhs'
    let ambient := n.doubleGlue (active_ne hab) (active_ne hcd) rhs rhs'
    Wiring.Respects (doubleEmbedding arity label labelD labelE
      (active_ne hab) (active_ne hcd) hac had hbc hbd) result.wiring ambient.1 ∧
      result.loops = ambient.2 := by
  have hs := n.contract_contract_spec hab rhs
    (n.contract_active hab rhs ⟨c, hac.symm, hbc.symm⟩ ⟨d, had.symm, hbd.symm⟩ hcd) rhs'
  dsimp only at hs
  rw [residualPorts_eq arity label labelD labelE (active_ne hab) (active_ne hcd)
    hac had hbc hbd] at hs
  exact hs

/-- Independent contractions commute by an explicit boundary-preserving cell renaming. -/
def contractCommute (n : PortNet arity label Γ) {a b c d : C}
    (hab : n.Active a b) (hcd : n.Active c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (rhs : PortNet arity labelD (PairBoundary arity label a b))
    (rhs' : PortNet arity labelE (PairBoundary arity label c d)) :
    Iso ((n.contract hab rhs).contract
      (n.contract_active hab rhs ⟨c, hac.symm, hbc.symm⟩ ⟨d, had.symm, hbd.symm⟩ hcd) rhs')
      ((n.contract hcd rhs').contract
        (n.contract_active hcd rhs' ⟨a, hac, had⟩ ⟨b, hbc, hbd⟩ hab) rhs) where
  cells := contractionCellsEquiv a b c d hac had hbc hbd
  label_eq := contractionCellsEquiv_label label labelD labelE a b c d hac had hbc hbd
  wiring_eq := by
    have h₁ := n.doubleGlue_spec hab hcd hac had hbc hbd rhs rhs'
    have h₂ := n.doubleGlue_spec hcd hab hac.symm hbc.symm had.symm hbd.symm rhs' rhs
    have he := n.doubleGlue_comm (active_ne hab) (active_ne hcd) hac had hbc hbd rhs rhs'
    have hm := h₂.1.trans (Wiring.respects_map (sumRightComm _ _ _) _)
    have hw := congrArg Prod.fst he
    change (n.doubleGlue (active_ne hcd) (active_ne hab) rhs' rhs).1.map
      (sumRightComm _ _ _) = (n.doubleGlue (active_ne hab) (active_ne hcd) rhs rhs').1 at hw
    rw [hw] at hm
    exact h₁.1.map_eq hm _
      (doubleEmbedding_commute arity label labelD labelE (active_ne hab) (active_ne hcd)
        hac had hbc hbd)
  loops_eq := by
    have h₁ := n.doubleGlue_spec hab hcd hac had hbc hbd rhs rhs'
    have h₂ := n.doubleGlue_spec hcd hab hac.symm hbc.symm had.symm hbd.symm rhs' rhs
    have he := n.doubleGlue_comm (active_ne hab) (active_ne hcd) hac had hbc hbd rhs rhs'
    exact h₁.2.trans ((congrArg Prod.snd he).symm.trans h₂.2.symm)

end Geb.InteractionNet.PortNet

end
