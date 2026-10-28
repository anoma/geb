/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringEmbedding
public import Geb.Prototypes.InteractionNet.PortNet
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

set_option doc.verso true in
/-!
# Joining two open graph boundaries

Two nets may share one boundary block while each retains another block. Joining their
shared positions retains both external blocks, both cell families and every closed wire.
This operation exposes the intermediate graph used when a rule's arguments are attached
before its internal wires and equation roots are closed.

## Main definitions

* {lit}`PortNet.join` — connect the shared block of two open nets.

## Main statements

* {lit}`PortNet.join_spec` — joining agrees with gluing in the disjoint input graphs.
* {lit}`PortNet.join_in` — perform the join inside a common ambient matching.

## Tags

interaction net, graph, boundary, composition, joining, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

variable {α C D Γ I B : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- The two graph endpoint spaces before their shared boundary is removed. -/
abbrev JoinEndpoint (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I B : Type) :=
  Endpoint arity label (Γ ⊕ I) ⊕ Endpoint arity label' (I ⊕ B)

/-- Match the right boundary block of the first net to the left block of the second. -/
def joinPorts (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I B : Type) :
    I × Bool ↪ JoinEndpoint arity label label' Γ I B where
  toFun p := if p.2 then .inr (.inl (.inl p.1)) else .inl (.inl (.inr p.1))
  inj' := by rintro ⟨i, b⟩ ⟨j, c⟩ h; cases b <;> cases c <;> simp_all

/-- Joining retains the left and right external boundaries and both families of cells. -/
def joinEndpointEquiv (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I B : Type) :
    {p : JoinEndpoint arity label label' Γ I B //
      ∀ i b, p ≠ joinPorts arity label label' Γ I B (i, b)} ≃
        Endpoint arity (Sum.elim label label') (Γ ⊕ B) where
  toFun p := match p with
    | ⟨.inl (.inl (.inl i)), _⟩ => .inl (.inl i)
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr ⟨c, p⟩), _⟩ => .inr ⟨.inl c, p⟩
    | ⟨.inr (.inl (.inl i)), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inl (.inr i)), _⟩ => .inl (.inr i)
    | ⟨.inr (.inr ⟨c, p⟩), _⟩ => .inr ⟨.inr c, p⟩
  invFun p := match p with
    | .inl (.inl i) => ⟨.inl (.inl (.inl i)), by intro j b; cases b <;> intro h <;> cases h⟩
    | .inl (.inr i) => ⟨.inr (.inl (.inr i)), by intro j b; cases b <;> intro h <;> cases h⟩
    | .inr ⟨.inl c, p⟩ => ⟨.inl (.inr ⟨c, p⟩), by intro j b; cases b <;> intro h <;> cases h⟩
    | .inr ⟨.inr c, p⟩ => ⟨.inr (.inr ⟨c, p⟩), by intro j b; cases b <;> intro h <;> cases h⟩
  left_inv p := match p with
    | ⟨.inl (.inl (.inl _)), _⟩ => rfl
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr ⟨_, _⟩), _⟩ => rfl
    | ⟨.inr (.inl (.inl i)), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inl (.inr _)), _⟩ => rfl
    | ⟨.inr (.inr ⟨_, _⟩), _⟩ => rfl
  right_inv p := by rcases p with (i | i) | ⟨c | c, p⟩ <;> rfl

/-- Locate the joined graph's retained boundary and cells in the original disjoint graphs. -/
def joinEmbedding (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I B : Type) :
    Endpoint arity (Sum.elim label label') (Γ ⊕ B) ↪ JoinEndpoint arity label label' Γ I B :=
  (joinEndpointEquiv arity label label' Γ I B).symm.toEmbedding.trans (.subtype _)

variable [DecidableEq C] [DecidableEq D] [DecidableEq Γ] [DecidableEq I] [DecidableEq B]

/-- Join the shared boundary once at each position, retaining both other boundary blocks. -/
def join (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' (I ⊕ B))
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order) :
    PortNet arity (Sum.elim label label') (Γ ⊕ B) :=
  let g := Wiring.glued (joinPorts arity label label' Γ I B) order unique cover
    (n.wiring.sum m.wiring, n.loops + m.loops)
  ⟨g.1.map (joinEndpointEquiv arity label label' Γ I B), g.2⟩

/-- Joining agrees with its shared-boundary cuts, including the closed-wire count. -/
theorem join_spec (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' (I ⊕ B))
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order) :
    let g := Wiring.glue (joinPorts arity label label' Γ I B) order
      (n.wiring.sum m.wiring, n.loops + m.loops)
    Wiring.Respects (joinEmbedding arity label label' Γ I B)
      (n.join m order unique cover).wiring g.1 ∧ (n.join m order unique cover).loops = g.2 := by
  exact ⟨(Wiring.respects_map_symm (joinEndpointEquiv arity label label' Γ I B) _).trans
    (Wiring.respects_glued _ _ unique cover _), rfl⟩

/-- Joining respects an ambient endpoint embedding and an independent loop offset. -/
theorem join_in {P : Type} [DecidableEq P]
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' (I ⊕ B))
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order)
    (e : JoinEndpoint arity label label' Γ I B ↪ P) (s : Wiring P × ℕ)
    (he : Wiring.Respects e (n.wiring.sum m.wiring) s.1) (extra : ℕ)
    (hl : n.loops + m.loops + extra = s.2) :
    let g := Wiring.glue ((joinPorts arity label label' Γ I B).trans e) order s
    Wiring.Respects ((joinEmbedding arity label label' Γ I B).trans e)
      (n.join m order unique cover).wiring g.1 ∧
        (n.join m order unique cover).loops + extra = g.2 := by
  have h := n.join_spec m order unique cover
  have hg := he.glue_offset (joinPorts arity label label' Γ I B) order
    (n.wiring.sum m.wiring, n.loops + m.loops) s extra hl
  exact ⟨h.1.trans hg.1, (congrArg (· + extra) h.2).trans hg.2⟩

end Geb.InteractionNet.PortNet

end
