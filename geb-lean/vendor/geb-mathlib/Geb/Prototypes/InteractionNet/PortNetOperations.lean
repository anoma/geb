/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Disjoint graph families and elementary nets

Disjoint union combines indexed families of cells and external boundaries. A single-cell
net exposes every ordered cell port at its boundary. A wire-only identity net connects
corresponding positions on two copies of a boundary. These operations provide the pieces
used to interpret the roots and variable occurrences of interaction-calculus terms.

## Main definitions

* {lit}`Wiring.sigma` — disjoint union of an indexed family of matchings.
* {lit}`PortNet.sigma` — disjoint union of finitely many port nets.
* {lit}`PortNet.star` — one cell with all its ports exposed at the boundary.
* {lit}`PortNet.identity` — a wire at each corresponding pair of boundary positions.

## References

* \[DeFalco2010\], Sections 3 and 4.

## Tags

interaction net, disjoint union, cell, boundary, wire, syntax
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

universe u v w x y

namespace Wiring

/-- Disjoint union preserves the matching on every indexed component. -/
def sigma {I : Type u} {P : I → Type v} (w : ∀ i, Wiring (P i)) : Wiring (Σ i, P i) where
  partner p := ⟨p.1, (w p.1).partner p.2⟩
  involutive p := congrArg (Sigma.mk p.1) ((w p.1).partner_partner p.2)
  fixedPointFree p h := (w p.1).fixedPointFree p.2 (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

end Wiring

namespace PortNet

variable {α : Type u} {I : Type v} {C : I → Type w} {Γ : I → Type x}

/-- Reorganize component endpoints into a boundary family and a cell family. -/
def sigmaEndpointEquiv (arity : α → ℕ) (label : ∀ i, C i → α) :
    (Σ i, Endpoint arity (label i) (Γ i)) ≃
      Endpoint arity (fun c : Σ i, C i ↦ label c.1 c.2) (Σ i, Γ i) where
  toFun p := match p with
    | ⟨i, .inl b⟩ => .inl ⟨i, b⟩
    | ⟨i, .inr ⟨c, p⟩⟩ => .inr ⟨⟨i, c⟩, p⟩
  invFun p := match p with
    | .inl ⟨i, b⟩ => ⟨i, .inl b⟩
    | .inr ⟨⟨i, c⟩, p⟩ => ⟨i, .inr ⟨c, p⟩⟩
  left_inv p := by rcases p with ⟨i, b | ⟨c, p⟩⟩ <;> rfl
  right_inv p := by rcases p with ⟨i, b⟩ | ⟨⟨i, c⟩, p⟩ <;> rfl

/-- Form the disjoint union of a finite family, adding its closed-wire counts. -/
def sigma [FinEnum I] {arity : α → ℕ} {label : ∀ i, C i → α}
    (n : ∀ i, PortNet arity (label i) (Γ i)) :
    PortNet arity (fun c : Σ i, C i ↦ label c.1 c.2) (Σ i, Γ i) :=
  ⟨(Wiring.sigma (fun i ↦ (n i).wiring)).map (sigmaEndpointEquiv arity label),
    ((FinEnum.toList I).map (fun i ↦ (n i).loops)).sum⟩

/-- Expose a single cell's principal and auxiliary ports at ordered boundary positions. -/
def star (arity : α → ℕ) (a : α) : PortNet arity (fun _ : Fin 1 ↦ a) (Fin (arity a + 1)) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl p => .inr ⟨0, p⟩
        | .inr ⟨_, p⟩ => .inl p
      involutive p := by
        rcases p with p | ⟨c, p⟩
        · rfl
        · have hc : c = 0 := Fin.eq_zero c
          subst c
          rfl
      fixedPointFree p h := by cases p <;> cases h }
  loops := 0

/-- A wire-only identity net connects corresponding positions on two boundary copies. -/
def identity (arity : α → ℕ) (B : Type y) : PortNet arity (Fin.elim0 : Fin 0 → α) (B ⊕ B) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl (.inl b) => .inl (.inr b)
        | .inl (.inr b) => .inl (.inl b)
        | .inr ⟨c, _⟩ => Fin.elim0 c
      involutive p := by
        rcases p with (b | b) | ⟨c, p⟩ <;> first | rfl | exact Fin.elim0 c
      fixedPointFree p h := by
        rcases p with (b | b) | ⟨c, p⟩ <;> first | cases h | exact Fin.elim0 c }
  loops := 0

end PortNet

end Geb.InteractionNet

end
