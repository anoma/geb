/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionEmbedding

set_option doc.verso true in
/-!
# Two graph contractions in one endpoint space

Both replacement graphs can be included in a common ambient matching before either
contraction. The first contraction leaves the second replacement untouched. The second
then acts on the surviving first result and that replacement. The two-step result agrees
with the two corresponding families of ambient wire splices, including all closed loops.

## Main statements

* {lit}`PortNet.contract_contract_spec` — two graph contractions refine two ambient gluings.

## Tags

interaction net, contraction, graph embedding, sequential composition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {E : Type x} {Γ : Type y}
variable [DecidableEq C] [DecidableEq D] [DecidableEq E] [DecidableEq Γ]
variable {arity : α → ℕ} {label : C → α} {labelD : D → α} {labelE : E → α}

set_option synthInstance.maxSize 256 in
/-- Two contractions agree with their local splices in an ambient graph containing both rules. -/
theorem contract_contract_spec (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity labelD (PairBoundary arity label a b))
    {c d : RemainingCell a b ⊕ D} (h' : (n.contract h rhs).Active c d)
    (rhs' : PortNet arity labelE
      (PairBoundary arity (Sum.elim (fun c : RemainingCell a b ↦ label c) labelD) c d)) :
    let firstLabel := Sum.elim (fun c : RemainingCell a b ↦ label c) labelD
    let e := (contractEmbedding arity label labelD (active_ne h)).sumMap
      (Function.Embedding.refl (Endpoint arity labelE (PairBoundary arity firstLabel c d)))
    let first := Wiring.glue ((contractPorts arity label labelD (active_ne h)).trans .inl)
      (FinEnum.toList (PairBoundary arity label a b))
      ((n.wiring.sum rhs.wiring).sum rhs'.wiring, n.loops + rhs.loops + rhs'.loops)
    let second := Wiring.glue ((contractPorts arity firstLabel labelE (active_ne h')).trans e)
      (FinEnum.toList (PairBoundary arity firstLabel c d)) first
    Wiring.Respects ((contractEmbedding arity firstLabel labelE (active_ne h')).trans e)
      ((n.contract h rhs).contract h' rhs').wiring second.1 ∧
      ((n.contract h rhs).contract h' rhs').loops = second.2 := by
  let firstLabel := Sum.elim (fun c : RemainingCell a b ↦ label c) labelD
  let e := (contractEmbedding (Γ := Γ) arity label labelD (active_ne h)).sumMap
    (Function.Embedding.refl (Endpoint arity labelE (PairBoundary arity firstLabel c d)))
  let initial := ((n.wiring.sum rhs.wiring).sum rhs'.wiring,
    n.loops + rhs.loops + rhs'.loops)
  let ports := (contractPorts (Γ := Γ) arity label labelD (active_ne h)).trans
    (Function.Embedding.inl (β := Endpoint arity labelE (PairBoundary arity firstLabel c d)))
  let order := FinEnum.toList (PairBoundary arity label a b)
  let first := Wiring.glue ports order initial
  have ha := n.contract_in h rhs .inl initial
    (Wiring.respects_inl _ _) rhs'.loops rfl
  have hr := (Wiring.respects_inr (n.wiring.sum rhs.wiring) rhs'.wiring).glue_outside
    ports order initial.2 (by intro i b p he; cases he)
  have hb : Wiring.Respects e ((n.contract h rhs).wiring.sum rhs'.wiring) first.1 := by
    intro p
    cases p with
    | inl p => exact ha.1 p
    | inr p => exact hr p
  have hs := (n.contract h rhs).contract_in h' rhs' e first hb 0
    (by simpa only [Nat.add_zero] using ha.2)
  exact ⟨hs.1, by simpa only [Nat.add_zero] using hs.2⟩

end Geb.InteractionNet.PortNet

end
