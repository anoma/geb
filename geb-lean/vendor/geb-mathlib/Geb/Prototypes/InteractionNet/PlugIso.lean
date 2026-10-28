/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PlugEmbedding
public import Geb.Prototypes.InteractionNet.ContractionIso

set_option doc.verso true in
/-!
# Boundary insertion preserves graph isomorphisms

Renaming cells independently in a context and its inserted graph commutes with gluing
their common boundary. The surviving cells have the corresponding disjoint-union
bijection, and the resulting closed-wire counts agree.

## Main definitions

* {lit}`PortNet.Iso.plug` — insert isomorphic graphs into isomorphic contexts.

## Tags

interaction net, boundary, insertion, isomorphism, cell, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

variable {α C C' D D' Γ I : Type} {arity : α → ℕ}
variable {label : C → α} {label₁ : C' → α} {label' : D → α} {label₁' : D' → α}
variable [DecidableEq C] [DecidableEq C'] [DecidableEq D] [DecidableEq D']
variable [DecidableEq Γ] [DecidableEq I]

/-- Independent cell renamings commute with insertion at a common ordered boundary. -/
def Iso.plug {n : PortNet arity label (Γ ⊕ I)} {n' : PortNet arity label₁ (Γ ⊕ I)}
    {m : PortNet arity label' I} {m' : PortNet arity label₁' I}
    (h : n.Iso n') (k : m.Iso m') (order : List I) (unique : order.Nodup)
    (cover : ∀ i, i ∈ order) :
    (n.plug m order unique cover).Iso (n'.plug m' order unique cover) := by
  let e := Equiv.sumCongr h.cells k.cells
  have labels (c : C ⊕ D) : Sum.elim label₁ label₁' (e c) = Sum.elim label label' c := by
    cases c with
    | inl c => exact h.label_eq c
    | inr c => exact k.label_eq c
  let ambient := Equiv.sumCongr
    (endpointEquiv arity (Equiv.refl (Γ ⊕ I)) h.cells h.label_eq)
    (endpointEquiv arity (Equiv.refl I) k.cells k.label_eq)
  have hs : Wiring.Respects ambient.toEmbedding (n.wiring.sum m.wiring)
      (n'.wiring.sum m'.wiring) := h.respects.sum k.respects
  have hp : (plugPorts arity label label' Γ).trans ambient.toEmbedding =
      plugPorts arity label₁ label₁' Γ := by
    ext p
    rcases p with ⟨i, bit⟩
    cases bit <;> rfl
  have hg := hs.glue (plugPorts arity label label' Γ) order
    (n.wiring.sum m.wiring, n.loops + m.loops)
    (n'.wiring.sum m'.wiring, n'.loops + m'.loops) (congrArg₂ (· + ·) h.loops_eq k.loops_eq)
  rw [hp] at hg
  have hn := n.plug_spec m order unique cover
  have hm := n'.plug_spec m' order unique cover
  refine ⟨e, labels, ?_, hn.2.trans (hg.2.trans hm.2.symm)⟩
  apply (hn.1.trans hg.1).map_eq hm.1 (endpointEquiv arity (Equiv.refl Γ) e labels)
  intro p
  rcases p with γ | ⟨c | d, p⟩ <;> rfl

end Geb.InteractionNet.PortNet

end
