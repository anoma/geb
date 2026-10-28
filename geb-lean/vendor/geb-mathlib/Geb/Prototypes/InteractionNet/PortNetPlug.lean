/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ActivePair
public import Geb.Prototypes.InteractionNet.WiringGlue

set_option doc.verso true in
/-!
# Plugging a net into a boundary

A context has an external boundary and a second boundary for the net to insert. Gluing
the second boundary to the inserted net joins the corresponding wires. All cells survive,
with their origin recorded by a sum of cell types; the connected boundary ports are
removed. Closed wires are counted even when an entire connected component disappears
from the endpoint matching.

## Main definitions

* {lit}`PortNet.plugPorts` — the pairs of endpoints to glue.
* {lit}`PortNet.plugEndpointEquiv` — the surviving endpoints, as ports of the combined net.
* {lit}`PortNet.plug` — executable insertion of a net into a context boundary.

## Main statements

* {lit}`PortNet.plug_order` — insertion is independent of the boundary processing order.

## References

* \[DeFalco2010\], Definition 4.1 and Proposition 4.3.

## Tags

interaction net, boundary, context, gluing, composition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {Γ : Type x} {I : Type y}

/-- Endpoints of the context and the inserted net before gluing. -/
abbrev PlugEndpoint (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ : Type x)
    (I : Type y) := Endpoint arity label (Γ ⊕ I) ⊕ Endpoint arity label' I

/-- The context's hole boundary is paired with the inserted net's external boundary. -/
def plugPorts (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ : Type x) :
    I × Bool ↪ PlugEndpoint arity label label' Γ I where
  toFun p := if p.2 then .inr (.inl p.1) else .inl (.inl (.inr p.1))
  inj' := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    cases b <;> cases c <;> simp_all

/-- The unglued endpoints are exactly the external boundary and the two families of cells. -/
def plugEndpointEquiv (arity : α → ℕ) (label : C → α) (label' : D → α) :
    {p : PlugEndpoint arity label label' Γ I //
      ∀ i b, p ≠ plugPorts arity label label' Γ (i, b)} ≃
        Endpoint arity (Sum.elim label label') Γ where
  toFun p := match p with
    | ⟨.inl (.inl (.inl γ)), _⟩ => .inl γ
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr ⟨c, p⟩), _⟩ => .inr ⟨.inl c, p⟩
    | ⟨.inr (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr ⟨d, p⟩), _⟩ => .inr ⟨.inr d, p⟩
  invFun p := match p with
    | .inl γ => ⟨.inl (.inl (.inl γ)), by
      intro i b
      cases b <;> intro h <;> cases h⟩
    | .inr ⟨.inl c, p⟩ => ⟨.inl (.inr ⟨c, p⟩), by
      intro i b
      cases b <;> intro h <;> cases h⟩
    | .inr ⟨.inr d, p⟩ => ⟨.inr (.inr ⟨d, p⟩), by
      intro i b
      cases b <;> intro h <;> cases h⟩
  left_inv p := match p with
    | ⟨.inl (.inl (.inl _)), _⟩ => rfl
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr ⟨_, _⟩), _⟩ => rfl
    | ⟨.inr (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr ⟨_, _⟩), _⟩ => rfl
  right_inv p := match p with
    | .inl _ => rfl
    | .inr ⟨.inl _, _⟩ => rfl
    | .inr ⟨.inr _, _⟩ => rfl

variable [DecidableEq C] [DecidableEq D] [DecidableEq Γ] [DecidableEq I]

/-- Insert a net by gluing every hole-boundary port once and retaining every closed wire. -/
def plug {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order) :
    PortNet arity (Sum.elim label label') Γ :=
  let g := Wiring.glued (plugPorts arity label label' Γ) order unique cover
    (n.wiring.sum m.wiring, n.loops + m.loops)
  ⟨g.1.map (plugEndpointEquiv arity label label'), g.2⟩

/-- Permuting the hole-boundary enumeration leaves insertion unchanged. -/
theorem plug_order {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    {order order' : List I} (h : order.Perm order')
    (unique : order.Nodup) (unique' : order'.Nodup)
    (cover : ∀ i, i ∈ order) (cover' : ∀ i, i ∈ order') :
    n.plug m order unique cover = n.plug m order' unique' cover' := by
  unfold plug
  rw [Wiring.glued_perm _ h unique unique' cover cover']

/-- Inserting a net preserves active pairs whose cells belong to the context. -/
theorem plug_left_active {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order)
    {c d : C} (hcd : n.Active c d) :
    (n.plug m order unique cover).Active (.inl c) (.inl d) := by
  unfold Active plug
  rw [Wiring.map_partner_eq_iff]
  apply Subtype.ext
  change (Wiring.glue (plugPorts arity label label' Γ) order
    (n.wiring.sum m.wiring, n.loops + m.loops)).1.partner
      (.inl (principal arity label c)) = .inl (principal arity label d)
  refine Wiring.glue_keeps _ _ _ ?_ ?_ (congrArg Sum.inl hcd)
  · intro i b
    cases b <;> intro h <;> cases h
  · intro i b
    cases b <;> intro h <;> cases h

/-- Active pairs internal to an inserted net remain active in the combined net. -/
theorem plug_right_active {arity : α → ℕ} {label : C → α} {label' : D → α}
    (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' I)
    (order : List I) (unique : order.Nodup) (cover : ∀ i, i ∈ order)
    {c d : D} (hcd : m.Active c d) :
    (n.plug m order unique cover).Active (.inr c) (.inr d) := by
  unfold Active plug
  rw [Wiring.map_partner_eq_iff]
  apply Subtype.ext
  change (Wiring.glue (plugPorts arity label label' Γ) order
    (n.wiring.sum m.wiring, n.loops + m.loops)).1.partner
      (.inr (principal arity label' c)) = .inr (principal arity label' d)
  refine Wiring.glue_keeps _ _ _ ?_ ?_ (congrArg Sum.inr hcd)
  · intro i b
    cases b <;> intro h <;> cases h
  · intro i b
    cases b <;> intro h <;> cases h

end Geb.InteractionNet.PortNet

end
