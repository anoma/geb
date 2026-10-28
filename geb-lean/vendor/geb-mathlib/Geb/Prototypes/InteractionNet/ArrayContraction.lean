/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ArrayNet
public import Geb.Prototypes.InteractionNet.ArrayReadback
public import Geb.Prototypes.InteractionNet.FiniteCells

set_option doc.verso true in
/-!
# Executable array graph contraction

Contraction appends the replacement's endpoint array, executes the auxiliary wire splices,
and compacts the surviving endpoints. The result has fresh finite ordinal cell indices.
The matching invariant is preserved throughout. Reading the final array agrees with
abstract graph contraction followed by this explicit cell reindexing.

## Main definitions

* {lit}`ArrayNet.resultLabel` — labels of surviving and inserted cells.
* {lit}`ArrayNet.contract` — allocate, locally rewire and compact an active-pair replacement.

## Main statements

* {lit}`ArrayNet.contract_read` — array execution refines abstract graph contraction.
* {lit}`ArrayNet.contractIso` — the refinement as a boundary-preserving cell isomorphism.

## Tags

interaction net, runtime, contraction, allocation, compaction, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.ArrayNet

open scoped FinEnum

universe u v

variable {α : Type u} {cells rhsCells : ℕ} {Γ : Type v} [FinEnum Γ]
variable {arity : α → ℕ} {label : Fin cells → α} {labelR : Fin rhsCells → α}

/-- Enumerate the input cells that remain after deleting the selected pair. -/
@[instance_reducible] local instance remainingCellsEnum (a b : Fin cells) :
    FinEnum (PortNet.RemainingCell a b) :=
  PortNet.subtypeEnum (fun c ↦ c ≠ a ∧ c ≠ b)

/-- The labels of surviving and inserted cells in their new finite ordinal enumeration. -/
def resultLabel (label : Fin cells → α) (labelR : Fin rhsCells → α) (a b : Fin cells) :
    Fin (FinEnum.card (PortNet.RemainingCell a b ⊕ Fin rhsCells)) → α :=
  fun i ↦ Sum.elim (fun c : PortNet.RemainingCell a b ↦ label c) labelR (FinEnum.equiv.symm i)

/-- Reindex result endpoints by their new cell indices, then by their compact array positions. -/
def resultPorts (arity : α → ℕ) (label : Fin cells → α) (labelR : Fin rhsCells → α)
    (a b : Fin cells) :
    Endpoint arity (Sum.elim (fun c : PortNet.RemainingCell a b ↦ label c) labelR) Γ ≃
      Fin (FinEnum.card (Endpoint arity (resultLabel label labelR a b) Γ)) :=
  (endpointEquiv arity (Equiv.refl Γ) FinEnum.equiv
    (fun c ↦ congrArg (Sum.elim (fun c : PortNet.RemainingCell a b ↦ label c) labelR)
      (Equiv.symm_apply_apply FinEnum.equiv c))).trans FinEnum.equiv

/-- Locate each compact result endpoint in the allocated and rewired endpoint array. -/
def livePorts (arity : α → ℕ) (label : Fin cells → α) (labelR : Fin rhsCells → α)
    {a b : Fin cells} (hab : a ≠ b) :
    Fin (FinEnum.card (Endpoint arity (resultLabel label labelR a b) Γ)) ↪
      Fin (FinEnum.card (Endpoint arity label Γ) +
        FinEnum.card (Endpoint arity labelR (PortNet.PairBoundary arity label a b))) :=
  (resultPorts arity label labelR a b).symm.toEmbedding.trans
    ((PortNet.contractEmbedding arity label labelR hab).trans
      (ambientEquiv arity label labelR a b).toEmbedding)

/-- The indexed contraction matching is represented by the live positions in the rewired array. -/
theorem livePorts_respects (n : ArrayNet arity label Γ) {a b : Fin cells}
    (h : n.read.Active a b) (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    Wiring.Respects (livePorts arity label labelR (PortNet.active_ne h))
      ((n.read.contract h rhs.read).wiring.map (resultPorts arity label labelR a b))
      (n.gluePair h rhs).1.read :=
  (Wiring.respects_map_symm (resultPorts arity label labelR a b) _).trans
    (n.gluePair_spec h rhs).1

/-- Allocate, locally rewire and compact a selected graph contraction. -/
def contract (n : ArrayNet arity label Γ) {a b : Fin cells} (h : n.read.Active a b)
    (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    ArrayNet arity (resultLabel label labelR a b) Γ :=
  let g := n.gluePair h rhs
  ⟨g.1.pullback (livePorts arity label labelR (PortNet.active_ne h))
    (ArrayWiring.closed_of_respects (n.livePorts_respects h rhs)), g.2⟩

/-- Reading array contraction gives abstract contraction with its finite cell enumeration. -/
theorem contract_read (n : ArrayNet arity label Γ) {a b : Fin cells} (h : n.read.Active a b)
    (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    (n.contract h rhs).read = (n.read.contract h rhs.read).indexed := by
  apply PortNet.ext
  · change ((n.gluePair h rhs).1.pullback
      (livePorts arity label labelR (PortNet.active_ne h))
      (ArrayWiring.closed_of_respects (n.livePorts_respects h rhs))).read.map _ = _
    rw [ArrayWiring.pullback_eq (n.livePorts_respects h rhs)]
    simp only [resultPorts, Wiring.map_trans, Wiring.map_symm_map, PortNet.indexed]
    rfl
  · exact (n.gluePair_spec h rhs).2.symm

/-- Array contraction and abstract graph contraction differ only by explicit cell reindexing. -/
def contractIso (n : ArrayNet arity label Γ) {a b : Fin cells} (h : n.read.Active a b)
    (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    (n.read.contract h rhs.read).Iso (n.contract h rhs).read := by
  rw [contract_read]
  exact PortNet.indexedIso _

end Geb.InteractionNet.ArrayNet

end
