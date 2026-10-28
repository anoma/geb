/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ArrayWiring
public import Geb.Prototypes.InteractionNet.FinitePorts
public import Geb.Prototypes.InteractionNet.ContractionEmbedding

set_option doc.verso true in
/-!
# Indexed graphs stored as partner arrays

An array net enumerates the external boundary and ordered cell ports, then stores their
wire matching in a contiguous partner array. Reading the array recovers the abstract
port net. To contract a pair, allocation appends the replacement's endpoint array and
local rewiring joins corresponding auxiliary and replacement-boundary endpoints.
The surviving graph embeds in the resulting array with the same closed-wire count.

## Main definitions

* {lit}`ArrayNet` — a finite indexed cell family with array-backed wiring.
* {lit}`ArrayNet.read` — recover its abstract port net.
* {lit}`ArrayNet.gluePair` — allocate a replacement and execute its local splices.

## Main statements

* {lit}`ArrayNet.read_encode` — storing and reading a net preserves it.
* {lit}`ArrayNet.gluePair_spec` — allocation and local rewiring represent graph contraction.

## Tags

interaction net, runtime, graph, array, allocation, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

universe u v

variable {α : Type u} {cells rhsCells : ℕ} {Γ : Type v} [FinEnum Γ]

/-- A finite indexed cell family whose boundary and port matching is stored in an array. -/
structure ArrayNet (arity : α → ℕ) (label : Fin cells → α) (Γ : Type v) [FinEnum Γ] where
  /-- The array of partners in the canonical boundary and cell-port enumeration. -/
  wiring : ArrayWiring (FinEnum.card (Endpoint arity label Γ))
  /-- Closed wire components without endpoints. -/
  loops : ℕ

namespace ArrayNet

variable {arity : α → ℕ} {label : Fin cells → α} {labelR : Fin rhsCells → α}

/-- Read a partner array through the canonical endpoint enumeration. -/
def read (n : ArrayNet arity label Γ) : PortNet arity label Γ :=
  ⟨n.wiring.read.map FinEnum.equiv.symm, n.loops⟩

/-- Store all partners of an indexed port net in their canonical array positions. -/
def encode (n : PortNet arity label Γ) : ArrayNet arity label Γ :=
  ⟨ArrayWiring.encode (n.wiring.map FinEnum.equiv), n.loops⟩

/-- Storing and reading an indexed graph preserves its wires and closed components. -/
@[simp] theorem read_encode (n : PortNet arity label Γ) : (encode n).read = n := by
  apply PortNet.ext
  · simp only [read, encode, ArrayWiring.read_encode, Wiring.map_symm_map]
  · rfl

/-- The endpoint enumeration embeds the read-back graph into its partner array. -/
theorem read_respects (n : ArrayNet arity label Γ) :
    Wiring.Respects FinEnum.equiv.toEmbedding n.read.wiring n.wiring.read :=
  Wiring.respects_map_symm FinEnum.equiv.symm n.wiring.read

/-- Locate input and replacement endpoints in their disjoint, contiguous allocation. -/
def ambientEquiv (arity : α → ℕ) (label : Fin cells → α) (labelR : Fin rhsCells → α)
    (a b : Fin cells) :
    Endpoint arity label Γ ⊕ Endpoint arity labelR (PortNet.PairBoundary arity label a b) ≃
      Fin (FinEnum.card (Endpoint arity label Γ) +
        FinEnum.card (Endpoint arity labelR (PortNet.PairBoundary arity label a b))) :=
  (Equiv.sumCongr FinEnum.equiv FinEnum.equiv).trans finSumFinEquiv

/-- Append a replacement's partner array and perform the active pair's auxiliary splices. -/
def gluePair (n : ArrayNet arity label Γ) {a b : Fin cells} (h : n.read.Active a b)
    (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    ArrayWiring (FinEnum.card (Endpoint arity label Γ) +
      FinEnum.card (Endpoint arity labelR (PortNet.PairBoundary arity label a b))) × ℕ :=
  ArrayWiring.glue
    ((PortNet.contractPorts arity label labelR (PortNet.active_ne h)).trans
      (ambientEquiv arity label labelR a b).toEmbedding)
    (FinEnum.toList _) (n.wiring.append rhs.wiring, n.loops + rhs.loops)

/-- Array allocation and local splicing represent the abstract contraction and its loop count. -/
theorem gluePair_spec (n : ArrayNet arity label Γ) {a b : Fin cells} (h : n.read.Active a b)
    (rhs : ArrayNet arity labelR (PortNet.PairBoundary arity label a b)) :
    Wiring.Respects
      ((PortNet.contractEmbedding arity label labelR (PortNet.active_ne h)).trans
        (ambientEquiv arity label labelR a b).toEmbedding)
      (n.read.contract h rhs.read).wiring (n.gluePair h rhs).1.read ∧
        (n.read.contract h rhs.read).loops = (n.gluePair h rhs).2 := by
  have he := (n.read_respects.sum rhs.read_respects).trans
    (Wiring.respects_map finSumFinEquiv (n.wiring.read.sum rhs.wiring.read))
  rw [← ArrayWiring.read_append] at he
  have hs := n.read.contract_in h rhs.read (ambientEquiv arity label labelR a b).toEmbedding
    ((n.wiring.append rhs.wiring).read, n.loops + rhs.loops) he 0 (Nat.add_zero _)
  have hg := ArrayWiring.read_glue
    ((PortNet.contractPorts arity label labelR (PortNet.active_ne h)).trans
      (ambientEquiv arity label labelR a b).toEmbedding)
    (FinEnum.toList _) (n.wiring.append rhs.wiring, n.loops + rhs.loops)
  dsimp only at hs
  rw [← hg] at hs
  exact ⟨hs.1, (Nat.add_zero _).symm.trans hs.2⟩

end ArrayNet

end Geb.InteractionNet

end
