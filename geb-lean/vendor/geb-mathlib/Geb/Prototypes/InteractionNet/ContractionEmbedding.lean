/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Contraction
public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Contraction in an ambient graph

A contraction can be observed in the disjoint union of its input and rule body. Gluing
the corresponding auxiliary and boundary ports isolates all discarded endpoints. The
resulting net embeds in this ambient matching. This observation preserves the loop count
and makes it possible to compare contractions without repeatedly changing endpoint types.

## Main definitions

* {lit}`PortNet.openEmbedding` — locate an opened context in the original endpoint type.
* {lit}`PortNet.contractEmbedding` — locate the contraction's surviving endpoints.
* {lit}`PortNet.contractPorts` — the ambient pairs joined by the contraction.

## Main statements

* {lit}`PortNet.contract_spec` — contraction agrees with ambient gluing on wires and loops.

## Tags

interaction net, contraction, graph embedding, local rewiring
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

universe u v w x

variable {α : Type u} {C : Type v} {D : Type w} {Γ : Type x}
variable [DecidableEq C]

/-- Locate the opened context's endpoints in the original net. -/
def openEmbedding (arity : α → ℕ) (label : C → α) {a b : C} (hab : a ≠ b) :
    OpenEndpoint arity label Γ a b ↪ Endpoint arity label Γ :=
  (openEndpointEquiv arity label hab).symm.toEmbedding.trans (.subtype _)

/-- Opening an active pair preserves every wire visible through its endpoint injection. -/
theorem openPair_respects {arity : α → ℕ} {label : C → α} (n : PortNet arity label Γ)
    {a b : C} (h : n.Active a b) :
    Wiring.Respects (openEmbedding arity label (active_ne h)) (n.openPair h).wiring n.wiring :=
  (Wiring.respects_map_symm _ _).trans (Wiring.respects_restrict _ _ _)

/-- Locate the contraction's endpoints in the disjoint union of input and replacement. -/
def contractEmbedding (arity : α → ℕ) (label : C → α) (label' : D → α)
    {a b : C} (hab : a ≠ b) :
    Endpoint arity (Sum.elim (fun c : RemainingCell a b ↦ label c) label') Γ ↪
      Endpoint arity label Γ ⊕ Endpoint arity label' (PairBoundary arity label a b) :=
  ((plugEndpointEquiv arity (fun c : RemainingCell a b ↦ label c) label').symm.toEmbedding.trans
    (.subtype _)).trans ((openEmbedding arity label hab).sumMap (.refl _))

/-- The pairs joined by a contraction, expressed in the original and replacement endpoints. -/
def contractPorts (arity : α → ℕ) (label : C → α) (label' : D → α)
    {a b : C} (hab : a ≠ b) :
    PairBoundary arity label a b × Bool ↪
      Endpoint arity label Γ ⊕ Endpoint arity label' (PairBoundary arity label a b) :=
  (plugPorts arity (fun c : RemainingCell a b ↦ label c) label' Γ).trans
    ((openEmbedding arity label hab).sumMap (.refl _))

/-- The external boundary retains its original endpoint. -/
@[simp] theorem contractEmbedding_boundary (arity : α → ℕ) (label : C → α) (label' : D → α)
    {a b : C} (hab : a ≠ b) (p : Γ) :
    contractEmbedding arity label label' hab (.inl p) = .inl (.inl p) := rfl

/-- A surviving cell port retains its original endpoint. -/
@[simp] theorem contractEmbedding_old (arity : α → ℕ) (label : C → α) (label' : D → α)
    {a b : C} (hab : a ≠ b) (c : RemainingCell a b) (p : Fin (arity (label c) + 1)) :
    contractEmbedding (Γ := Γ) arity label label' hab (.inr ⟨.inl c, p⟩) =
      .inl (.inr ⟨c.val, p⟩) := rfl

/-- An inserted cell port retains its endpoint from the replacement. -/
@[simp] theorem contractEmbedding_new (arity : α → ℕ) (label : C → α) (label' : D → α)
    {a b : C} (hab : a ≠ b) (c : D) (p : Fin (arity (label' c) + 1)) :
    contractEmbedding (Γ := Γ) arity label label' hab (.inr ⟨.inr c, p⟩) =
      .inr (.inr ⟨c, p⟩) := rfl

variable [DecidableEq D] [DecidableEq Γ]

/-- Contraction agrees with gluing in the original endpoint space, including closed wires. -/
theorem contract_spec {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity label' (PairBoundary arity label a b)) :
    let g := Wiring.glue (contractPorts arity label label' (active_ne h))
      (FinEnum.toList _) (n.wiring.sum rhs.wiring, n.loops + rhs.loops)
    Wiring.Respects (contractEmbedding arity label label' (active_ne h))
      (n.contract h rhs).wiring g.1 ∧ (n.contract h rhs).loops = g.2 := by
  have hb := (n.openPair_respects h).sum (Wiring.respects_refl rhs.wiring)
  have hg := hb.glue (plugPorts arity (fun c : RemainingCell a b ↦ label c) label' Γ)
    (FinEnum.toList _) ((n.openPair h).wiring.sum rhs.wiring, n.loops + rhs.loops)
    (n.wiring.sum rhs.wiring, n.loops + rhs.loops) rfl
  constructor
  · let ports := plugPorts (I := PairBoundary arity label a b) arity
      (fun c : RemainingCell a b ↦ label c) label' Γ
    let start := ((n.openPair h).wiring.sum rhs.wiring, n.loops + rhs.loops)
    let order := FinEnum.toList (PairBoundary arity label a b)
    have ho := Wiring.respects_glued ports order FinEnum.nodup_toList FinEnum.mem_toList start
    exact ((Wiring.respects_map_symm (plugEndpointEquiv arity
      (fun c : RemainingCell a b ↦ label c) label')
        (Wiring.glued ports order FinEnum.nodup_toList FinEnum.mem_toList start).1).trans ho).trans
          hg.1
  · exact hg.2

/-- A contraction can be performed inside a larger matching, retaining its external loop offset. -/
theorem contract_in {P : Type*} [DecidableEq P]
    {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label Γ) {a b : C} (h : n.Active a b)
    (rhs : PortNet arity label' (PairBoundary arity label a b))
    (e : Endpoint arity label Γ ⊕ Endpoint arity label' (PairBoundary arity label a b) ↪ P)
    (ambient : Wiring P × ℕ) (he : Wiring.Respects e (n.wiring.sum rhs.wiring) ambient.1)
    (extra : ℕ) (hl : n.loops + rhs.loops + extra = ambient.2) :
    let g := Wiring.glue ((contractPorts arity label label' (active_ne h)).trans e)
      (FinEnum.toList _) ambient
    Wiring.Respects ((contractEmbedding arity label label' (active_ne h)).trans e)
      (n.contract h rhs).wiring g.1 ∧ (n.contract h rhs).loops + extra = g.2 := by
  have hs := n.contract_spec h rhs
  have hg := he.glue_offset (contractPorts arity label label' (active_ne h))
    (FinEnum.toList _) (n.wiring.sum rhs.wiring, n.loops + rhs.loops) ambient extra hl
  exact ⟨hs.1.trans hg.1, (congrArg (· + extra) hs.2).trans hg.2⟩

end Geb.InteractionNet.PortNet

end
