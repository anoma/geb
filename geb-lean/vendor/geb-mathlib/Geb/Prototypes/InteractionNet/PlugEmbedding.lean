/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNetPlug
public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Boundary insertion in an ambient matching

Plugging a graph into a context glues their corresponding boundary endpoints. The live
endpoints of the result embed in the disjoint union of both input graphs. This embedding
allows insertion to be compared with other assemblies in a common endpoint space while
retaining their closed-wire counts.

## Main statements

* {lit}`PortNet.plug_spec` — insertion agrees with gluing in the original endpoint space.
* {lit}`PortNet.plug_in` — insertion can be performed inside a larger matching.

## Tags

interaction net, boundary, insertion, graph, embedding, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

variable {α C D Γ I : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- Locate the surviving endpoints of a boundary insertion in its two input graphs. -/
def plugEmbedding (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I : Type) :
    Endpoint arity (Sum.elim label label') Γ ↪ PlugEndpoint arity label label' Γ I :=
  (plugEndpointEquiv arity label label').symm.toEmbedding.trans (.subtype _)

variable [DecidableEq C] [DecidableEq D] [DecidableEq Γ] [DecidableEq I]

/-- Boundary insertion agrees with ambient gluing on both wires and closed components. -/
theorem plug_spec (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order) :
    let g := Wiring.glue (plugPorts arity label label' Γ) order
      (n.wiring.sum m.wiring, n.loops + m.loops)
    Wiring.Respects (plugEmbedding arity label label' Γ I)
      (n.plug m order unique cover).wiring g.1 ∧
        (n.plug m order unique cover).loops = g.2 := by
  refine ⟨?_, rfl⟩
  exact (Wiring.respects_map_symm (plugEndpointEquiv arity label label') _).trans
    (Wiring.respects_glued _ order unique cover _)

/-- Insert a graph inside a larger matching without changing its external loop offset. -/
theorem plug_in {P : Type} [DecidableEq P]
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order)
    (e : PlugEndpoint arity label label' Γ I ↪ P) (ambient : Wiring P × ℕ)
    (he : Wiring.Respects e (n.wiring.sum m.wiring) ambient.1) (extra : ℕ)
    (hl : n.loops + m.loops + extra = ambient.2) :
    let g := Wiring.glue ((plugPorts arity label label' Γ).trans e) order ambient
    Wiring.Respects ((plugEmbedding arity label label' Γ I).trans e)
      (n.plug m order unique cover).wiring g.1 ∧
        (n.plug m order unique cover).loops + extra = g.2 := by
  have hs := n.plug_spec m order unique cover
  have hg := he.glue_offset (plugPorts arity label label' Γ) order
    (n.wiring.sum m.wiring, n.loops + m.loops) ambient extra hl
  exact ⟨hs.1.trans hg.1, (congrArg (· + extra) hs.2).trans hg.2⟩

end Geb.InteractionNet.PortNet

end
