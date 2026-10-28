/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Wiring
public import Geb.Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Data.Fin.SuccPred

set_option doc.verso true in
/-!
# Nets with explicit cells and ports

A cell carries its symbol and ordered ports, with port zero principal. A net pairs the
cell ports and its external boundary by a wire matching and records closed wire components
separately. The finite presentation indexes cells and boundary ports by finite ordinals.
This is a presentation of the wires, pointed cells and loops in \[DeFalco2010\],
Definition 3.1, with the cell's order exposed as a port index.

## Main definitions

* {lit}`CellPort` — a cell and one of its ordered ports.
* {lit}`Endpoint` — an external boundary port or a cell port.
* {lit}`PortNet` — a matching of endpoints with a count of closed wires.
* {lit}`FiniteNet` — a net whose cells and boundary are finite ordinals.
* {lit}`endpointEquiv` — relabeling endpoints along boundary and cell equivalences.

## References

* \[DeFalco2010\], Definitions 3.1 and 3.2.

## Tags

interaction net, finite graph, cell, port, wire, boundary, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

universe u v w x y

variable {α : Type u} {C : Type v} {D : Type w} {Γ : Type x} {Δ : Type y}

/-- A cell with its principal port at zero and its auxiliary ports in order. -/
abbrev CellPort (arity : α → ℕ) (label : C → α) := Σ c, Fin (arity (label c) + 1)

/-- A boundary endpoint or a port of an internal cell. -/
abbrev Endpoint (arity : α → ℕ) (label : C → α) (Γ : Type x) := Γ ⊕ CellPort arity label

/-- A net pairs all endpoints and separately counts closed wires without endpoints. -/
@[ext] structure PortNet (arity : α → ℕ) (label : C → α) (Γ : Type x) : Type (max v x) where
  /-- The wire incident to each endpoint. -/
  wiring : Wiring (Endpoint arity label Γ)
  /-- The number of closed wire components with no endpoint. -/
  loops : ℕ

/-- A finite net with an ordered boundary and explicitly indexed cells. -/
abbrev FiniteNet (arity : α → ℕ) (boundary : ℕ) :=
  Σ cells : ℕ, Σ label : Fin cells → α, PortNet arity label (Fin boundary)

/-- A symbol-preserving cell bijection transports port positions without changing their order. -/
def cellPortEquiv (arity : α → ℕ) {label : C → α} {label' : D → α}
    (e : C ≃ D) (h : ∀ c, label' (e c) = label c) :
    CellPort arity label ≃ CellPort arity label' :=
  (sigmaCongrRight' fun c ↦ finCongr (congrArg (fun a ↦ arity a + 1) (h c).symm)).trans
    (Equiv.sigmaCongrLeft (β := fun c ↦ Fin (arity (label' c) + 1)) e)

/-- Transport endpoints along boundary and symbol-preserving cell bijections. -/
def endpointEquiv (arity : α → ℕ) {label : C → α} {label' : D → α}
    (b : Γ ≃ Δ) (e : C ≃ D) (h : ∀ c, label' (e c) = label c) :
    Endpoint arity label Γ ≃ Endpoint arity label' Δ :=
  Equiv.sumCongr b (cellPortEquiv arity e h)

/-- Boundary renaming acts only on the external endpoint. -/
@[simp] theorem endpointEquiv_boundary (arity : α → ℕ) {label : C → α} {label' : D → α}
    (b : Γ ≃ Δ) (e : C ≃ D) (h : ∀ c, label' (e c) = label c) (p : Γ) :
    endpointEquiv arity b e h (.inl p) = .inl (b p) := rfl

/-- Cell renaming preserves each port's numeric position. -/
@[simp] theorem endpointEquiv_cell (arity : α → ℕ) {label : C → α} {label' : D → α}
    (b : Γ ≃ Δ) (e : C ≃ D) (h : ∀ c, label' (e c) = label c)
    (c : C) (p : Fin (arity (label c) + 1)) :
    endpointEquiv arity b e h (.inr ⟨c, p⟩) =
      .inr ⟨e c, Fin.cast (congrArg (fun a ↦ arity a + 1) (h c).symm) p⟩ := rfl

/-- Identity boundary and cell bijections induce the identity on all endpoints. -/
@[simp] theorem endpointEquiv_refl (arity : α → ℕ) (label : C → α) :
    endpointEquiv (Γ := Γ) arity (Equiv.refl Γ) (Equiv.refl C) (fun _ ↦ rfl) =
      Equiv.refl (Endpoint arity label Γ) := by
  ext p
  cases p with
  | inl p => rfl
  | inr p => rfl

/-- Consecutive boundary and cell renamings induce the composite endpoint renaming. -/
theorem endpointEquiv_trans {E : Type*} {Θ : Type*} (arity : α → ℕ)
    {label : C → α} {label' : D → α} {label'' : E → α}
    (b : Γ ≃ Δ) (b' : Δ ≃ Θ) (e : C ≃ D) (e' : D ≃ E)
    (h : ∀ c, label' (e c) = label c) (h' : ∀ c, label'' (e' c) = label' c) :
    (endpointEquiv arity b e h).trans (endpointEquiv arity b' e' h') =
      endpointEquiv arity (b.trans b') (e.trans e') (fun c ↦ (h' (e c)).trans (h c)) := by
  ext p
  cases p with
  | inl p => rfl
  | inr p => rfl

/-- Inverting the boundary and cell bijections inverts their endpoint renaming. -/
theorem endpointEquiv_symm (arity : α → ℕ) {label : C → α} {label' : D → α}
    (b : Γ ≃ Δ) (e : C ≃ D) (h : ∀ c, label' (e c) = label c) :
    (endpointEquiv arity b e h).symm = endpointEquiv arity b.symm e.symm
      (fun c ↦ (h (e.symm c)).symm.trans (congrArg label' (e.apply_symm_apply c))) := by
  ext p
  apply (endpointEquiv arity b e h).injective
  rw [Equiv.apply_symm_apply]
  cases p with
  | inl p => exact congrArg Sum.inl (b.apply_symm_apply p).symm
  | inr p =>
    apply congrArg Sum.inr
    apply Sigma.ext (e.apply_symm_apply p.1).symm
    apply (Fin.heq_ext_iff (congrArg (fun c ↦ arity (label' c) + 1)
      (e.apply_symm_apply p.1).symm)).mpr
    rfl

namespace PortNet

variable {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- An isomorphism renames internal cells while fixing the ordered external boundary. -/
structure Iso (n : PortNet arity label Γ) (m : PortNet arity label' Γ) where
  /-- The bijection of internal cells. -/
  cells : C ≃ D
  /-- Every cell retains its symbol. -/
  label_eq : ∀ c, label' (cells c) = label c
  /-- Renaming endpoints transports the wire matching. -/
  wiring_eq : n.wiring.map (endpointEquiv arity (Equiv.refl Γ) cells label_eq) = m.wiring
  /-- Closed wire components are preserved. -/
  loops_eq : n.loops = m.loops

namespace Iso

/-- Identity renaming is a boundary-preserving net isomorphism. -/
def refl (n : PortNet arity label Γ) : Iso n n where
  cells := Equiv.refl C
  label_eq _ := rfl
  wiring_eq := by
    change n.wiring.map (endpointEquiv arity (Equiv.refl Γ) (Equiv.refl C)
      (fun _ ↦ rfl)) = n.wiring
    rw [endpointEquiv_refl]
    exact Wiring.map_refl n.wiring
  loops_eq := rfl

/-- A net isomorphism can be reversed. -/
def symm {n : PortNet arity label Γ} {m : PortNet arity label' Γ}
    (i : Iso n m) : Iso m n where
  cells := i.cells.symm
  label_eq c := (i.label_eq (i.cells.symm c)).symm.trans
    (congrArg label' (i.cells.apply_symm_apply c))
  wiring_eq := by
    change m.wiring.map (endpointEquiv arity (Equiv.refl Γ).symm i.cells.symm
      (fun c ↦ (i.label_eq (i.cells.symm c)).symm.trans
        (congrArg label' (i.cells.apply_symm_apply c)))) = n.wiring
    rw [← endpointEquiv_symm arity (Equiv.refl Γ) i.cells i.label_eq,
      ← i.wiring_eq, Wiring.map_symm_map]
  loops_eq := i.loops_eq.symm

/-- Boundary-preserving net isomorphisms compose. -/
def trans {E : Type*} {label'' : E → α}
    {n : PortNet arity label Γ} {m : PortNet arity label' Γ}
    {p : PortNet arity label'' Γ} (i : Iso n m) (j : Iso m p) : Iso n p where
  cells := i.cells.trans j.cells
  label_eq c := (j.label_eq (i.cells c)).trans (i.label_eq c)
  wiring_eq := by
    change n.wiring.map (endpointEquiv arity ((Equiv.refl Γ).trans (Equiv.refl Γ))
      (i.cells.trans j.cells) (fun c ↦ (j.label_eq (i.cells c)).trans (i.label_eq c))) =
        p.wiring
    rw [← endpointEquiv_trans arity (Equiv.refl Γ) (Equiv.refl Γ)
      i.cells j.cells i.label_eq j.label_eq, Wiring.map_trans,
      i.wiring_eq, j.wiring_eq]
  loops_eq := i.loops_eq.trans j.loops_eq

end Iso

end PortNet

end Geb.InteractionNet

end
