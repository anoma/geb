/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.FiniteWiring
public import Geb.Prototypes.InteractionNet.FinitePorts
public import Geb.Mathlib.Data.FinEnum
public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Closing part of a graph boundary

A matching can close a selected boundary block while leaving the other block directly
exposed. The operation retains the original cells and counts any closed wires produced by
the attachment. Unlike complete boundary assembly, it needs no additional identity wires
at the external positions.

## Main definitions

* {lit}`PortNet.close` — attach a matching to one boundary block.

## Main statements

* {lit}`PortNet.close_spec` — the result embeds in the original graph and matching.
* {lit}`PortNet.close_in` — perform partial closure in a larger matching.

## Tags

interaction net, boundary, partial closure, matching, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C Γ B : Type} {arity : α → ℕ} {label : C → α}

/-- The selected matching and the graph before its selected boundary is removed. -/
abbrev ClosureEndpoint (arity : α → ℕ) (label : C → α) (Γ B : Type) :=
  B ⊕ Endpoint arity label (Γ ⊕ B)

/-- Join each matching endpoint to the corresponding selected graph boundary position. -/
def closePorts (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    B × Bool ↪ ClosureEndpoint arity label Γ B where
  toFun p := if p.2 then .inr (.inl (.inr p.1)) else .inl p.1
  inj' := by rintro ⟨p, b⟩ ⟨q, c⟩ h; cases b <;> cases c <;> simp_all

/-- Closure retains the unselected boundary block and every original cell port. -/
def closeEndpointEquiv (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    {p : ClosureEndpoint arity label Γ B // ∀ i b, p ≠ closePorts arity label Γ B (i, b)} ≃
      Endpoint arity label Γ where
  toFun p := match p with
    | ⟨.inl i, h⟩ => (h i false rfl).elim
    | ⟨.inr (.inl (.inl i)), _⟩ => .inl i
    | ⟨.inr (.inl (.inr i)), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr p), _⟩ => .inr p
  invFun p := match p with
    | .inl i => ⟨.inr (.inl (.inl i)), by intro j b; cases b <;> intro h <;> cases h⟩
    | .inr p => ⟨.inr (.inr p), by intro j b; cases b <;> intro h <;> cases h⟩
  left_inv p := match p with
    | ⟨.inl i, h⟩ => (h i false rfl).elim
    | ⟨.inr (.inl (.inl _)), _⟩ => rfl
    | ⟨.inr (.inl (.inr i)), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr _), _⟩ => rfl
  right_inv p := by cases p <;> rfl

/-- Locate the live endpoints left after partial closure. -/
def closeEmbedding (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    Endpoint arity label Γ ↪ ClosureEndpoint arity label Γ B :=
  (closeEndpointEquiv arity label Γ B).symm.toEmbedding.trans (.subtype _)

variable [FinEnum C] [FinEnum Γ] [FinEnum B]

/-- Attach a matching to the selected boundary block, retaining the other boundary directly. -/
def close (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) : PortNet arity label Γ :=
  let dec : DecidableEq (ClosureEndpoint arity label Γ B) := inferInstance
  let := sigmaEnum (C := fun c ↦ Fin (arity (label c) + 1))
  let : DecidableEq (ClosureEndpoint arity label Γ B) := dec
  let g := Wiring.gluedFinite (closePorts arity label Γ B) (FinEnum.toList B)
    FinEnum.nodup_toList FinEnum.mem_toList (w.sum n.wiring, n.loops)
  ⟨g.1.map (closeEndpointEquiv arity label Γ B), g.2⟩

/-- Partial closure agrees with its cuts in the common matching and graph endpoint space. -/
theorem close_spec (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B) :
    let g := Wiring.glue (closePorts arity label Γ B) (FinEnum.toList B)
      (w.sum n.wiring, n.loops)
    Wiring.Respects (closeEmbedding arity label Γ B) (n.close w).wiring g.1 ∧
      (n.close w).loops = g.2 := by
  simp only [close, Wiring.gluedFinite_eq]
  exact ⟨(Wiring.respects_map_symm (closeEndpointEquiv arity label Γ B) _).trans
    (Wiring.respects_glued _ _ FinEnum.nodup_toList FinEnum.mem_toList _), rfl⟩

/-- Partial closure preserves an ambient embedding and any independent closed-wire offset. -/
theorem close_in {P : Type} [DecidableEq P]
    (n : PortNet arity label (Γ ⊕ B)) (w : Wiring B)
    (e : ClosureEndpoint arity label Γ B ↪ P) (s : Wiring P × ℕ)
    (he : Wiring.Respects e (w.sum n.wiring) s.1) (extra : ℕ)
    (hl : n.loops + extra = s.2) :
    let g := Wiring.glue ((closePorts arity label Γ B).trans e) (FinEnum.toList B) s
    Wiring.Respects ((closeEmbedding arity label Γ B).trans e) (n.close w).wiring g.1 ∧
      (n.close w).loops + extra = g.2 := by
  have h := n.close_spec w
  have hg := he.glue_offset (closePorts arity label Γ B) (FinEnum.toList B)
    (w.sum n.wiring, n.loops) s extra hl
  exact ⟨h.1.trans hg.1, (congrArg (· + extra) h.2).trans hg.2⟩

end Geb.InteractionNet.PortNet

end
