/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

set_option doc.verso true in
/-!
# Disjoint union of two port nets

Disjoint union retains the cells and boundary positions of both nets. Its matching is the
disjoint union of their matchings, and its closed-wire count is the sum of their counts.

## Main definitions

* {lit}`PortNet.sum` — binary disjoint union with explicit cell and boundary indices.

## Tags

interaction net, graph, disjoint union, boundary, cell
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

/-- Disjoint union of matchings commutes with endpoint bijections on its two components. -/
theorem Wiring.map_sum {P Q R S : Type} (e : P ≃ R) (f : Q ≃ S)
    (w : Wiring P) (v : Wiring Q) :
    (w.sum v).map (Equiv.sumCongr e f) = (w.map e).sum (v.map f) := by
  ext p
  cases p <;> rfl

namespace PortNet

variable {α C D B Δ : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}

/-- Collect the two nets' boundary positions and cell ports into their disjoint union. -/
def sumEndpointEquiv (arity : α → ℕ) (label : C → α) (label' : D → α) (B Δ : Type) :
    Endpoint arity label B ⊕ Endpoint arity label' Δ ≃
      Endpoint arity (Sum.elim label label') (B ⊕ Δ) where
  toFun p := match p with
    | .inl (.inl b) => .inl (.inl b)
    | .inl (.inr ⟨c, p⟩) => .inr ⟨.inl c, p⟩
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr ⟨c, p⟩) => .inr ⟨.inr c, p⟩
  invFun p := match p with
    | .inl (.inl b) => .inl (.inl b)
    | .inl (.inr b) => .inr (.inl b)
    | .inr ⟨.inl c, p⟩ => .inl (.inr ⟨c, p⟩)
    | .inr ⟨.inr c, p⟩ => .inr (.inr ⟨c, p⟩)
  left_inv p := by rcases p with (b | ⟨c, p⟩) | (b | ⟨c, p⟩) <;> rfl
  right_inv p := by rcases p with (b | b) | ⟨c | c, p⟩ <;> rfl

/-- The disjoint union retains both matchings and adds their closed-wire counts. -/
def sum (n : PortNet arity label B) (m : PortNet arity label' Δ) :
    PortNet arity (Sum.elim label label') (B ⊕ Δ) where
  wiring := (n.wiring.sum m.wiring).map (sumEndpointEquiv arity label label' B Δ)
  loops := n.loops + m.loops

variable {C' D' B' Δ' : Type} {label₁ : C' → α} {label₂ : D' → α}

/-- Component cell correspondences preserve symbols in the disjoint union. -/
theorem sum_label (e : C ≃ C') (f : D ≃ D')
    (he : ∀ c, label₁ (e c) = label c) (hf : ∀ d, label₂ (f d) = label' d)
    (p : C ⊕ D) :
    Sum.elim label₁ label₂ ((Equiv.sumCongr e f) p) = Sum.elim label label' p := by
  cases p with
  | inl c => exact he c
  | inr d => exact hf d

/-- Component boundary and cell correspondences preserve the disjoint union's matching. -/
theorem sum_wiring (n : PortNet arity label B) (m : PortNet arity label' Δ)
    (n' : PortNet arity label₁ B') (m' : PortNet arity label₂ Δ')
    (b : B ≃ B') (d : Δ ≃ Δ') (e : C ≃ C') (f : D ≃ D')
    (he : ∀ c, label₁ (e c) = label c) (hf : ∀ d, label₂ (f d) = label' d)
    (hn : n.wiring.map (endpointEquiv arity b e he) = n'.wiring)
    (hm : m.wiring.map (endpointEquiv arity d f hf) = m'.wiring) :
    (n.sum m).wiring.map (endpointEquiv arity (Equiv.sumCongr b d) (Equiv.sumCongr e f)
      (sum_label e f he hf)) = (n'.sum m').wiring := by
  have hp : (sumEndpointEquiv arity label label' B Δ).trans
      (endpointEquiv arity (Equiv.sumCongr b d) (Equiv.sumCongr e f) (sum_label e f he hf)) =
        (Equiv.sumCongr (endpointEquiv arity b e he) (endpointEquiv arity d f hf)).trans
          (sumEndpointEquiv arity label₁ label₂ B' Δ') := by
    ext p
    rcases p with (p | ⟨c, p⟩) | (p | ⟨c, p⟩) <;> rfl
  dsimp only [sum]
  rw [← Wiring.map_trans, hp, Wiring.map_trans, Wiring.map_sum, hn, hm]

end PortNet

end Geb.InteractionNet

end
