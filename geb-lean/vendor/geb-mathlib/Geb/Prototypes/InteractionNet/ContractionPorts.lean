/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionEmbedding
public import Geb.Prototypes.InteractionNet.WiringSwap

set_option doc.verso true in
/-!
# Ports of two disjoint contractions

The two replacement graphs occupy separate components of one ambient endpoint space.
Each contraction connects only its own original auxiliary ports and its own replacement
boundary. Distinct active pairs therefore determine disjoint families of cuts. Changing
allocation order only renames the two replacement components.

## Main definitions

* {lit}`PortNet.DoubleEndpoint` — original endpoints and the two replacement components.
* {lit}`PortNet.firstPorts` — the first pair's cuts in that space.
* {lit}`PortNet.secondPorts` — the second pair's cuts in that space.

## Main statements

* {lit}`PortNet.residualPorts_eq` — the second pair keeps its original auxiliary endpoints.
* {lit}`PortNet.contractionPorts_disjoint` — disjoint pairs have disjoint cut endpoints.

## Tags

interaction net, contraction, port, disjointness, allocation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {E : Type x} {Γ : Type y}

/-- Endpoints of the original graph and two separately allocated replacements. -/
abbrev DoubleEndpoint (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    (Γ : Type y) (a b c d : C) :=
  (Endpoint arity label Γ ⊕ Endpoint arity labelD (PairBoundary arity label a b)) ⊕
    Endpoint arity labelE (PairBoundary arity label c d)

variable [DecidableEq C]

/-- The first pair's cuts in the original graph and two replacements. -/
def firstPorts (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    {a b : C} (hab : a ≠ b) (c d : C) :
    PairBoundary arity label a b × Bool ↪ DoubleEndpoint arity label labelD labelE Γ a b c d :=
  (contractPorts arity label labelD hab).trans .inl

/-- The second pair's cuts, independently of the first pair's contraction. -/
def secondPorts (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    (a b : C) {c d : C} (hcd : c ≠ d) :
    PairBoundary arity label c d × Bool ↪ DoubleEndpoint arity label labelD labelE Γ a b c d :=
  (contractPorts arity label labelE hcd).trans (.sumMap .inl (.refl _))

/-- The residual pair's cuts use the same original endpoints as a direct second-pair contraction. -/
theorem residualPorts_eq [DecidableEq D]
    (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd' : (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D) ≠
      .inl ⟨d, had.symm, hbd.symm⟩) :
    (contractPorts arity (Sum.elim (fun c : RemainingCell a b ↦ label c) labelD) labelE hcd').trans
      ((contractEmbedding (Γ := Γ) arity label labelD hab).sumMap (.refl _)) =
        secondPorts arity label labelD labelE a b hcd := by
  ext ⟨i, side⟩
  cases i <;> cases side <;> rfl

/-- The two disjoint pairs use disjoint old auxiliary ports and disjoint replacement boundaries. -/
theorem contractionPorts_disjoint (arity : α → ℕ) (label : C → α)
    (labelD : D → α) (labelE : E → α) {a b c d : C} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∀ i side j side', firstPorts (Γ := Γ) arity label labelD labelE hab c d (i, side) ≠
      secondPorts arity label labelD labelE a b hcd (j, side') := by
  intro i side j side' h
  cases i <;> cases j <;> cases side <;> cases side'
  all_goals first
    | exact hac (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
    | exact had (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
    | exact hbc (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
    | exact hbd (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))))
    | cases h

/-- Exchanging allocation order sends the other order's first cuts to the second cuts. -/
theorem firstPorts_swap (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    (a b : C) {c d : C} (hcd : c ≠ d) :
    (firstPorts (Γ := Γ) arity label labelE labelD hcd a b).trans
      (sumRightComm _ _ _).toEmbedding = secondPorts arity label labelD labelE a b hcd := by
  ext ⟨i, side⟩
  cases i <;> cases side <;> rfl

/-- Exchanging allocation order sends the other order's second cuts to the first cuts. -/
theorem secondPorts_swap (arity : α → ℕ) (label : C → α) (labelD : D → α) (labelE : E → α)
    {a b : C} (hab : a ≠ b) (c d : C) :
    (secondPorts (Γ := Γ) arity label labelE labelD c d hab).trans
      (sumRightComm _ _ _).toEmbedding = firstPorts arity label labelD labelE hab c d := by
  ext ⟨i, side⟩
  cases i <;> cases side <;> rfl

end Geb.InteractionNet.PortNet

end
