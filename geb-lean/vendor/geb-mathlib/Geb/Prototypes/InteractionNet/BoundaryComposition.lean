/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.FiniteWiring
public import Geb.Prototypes.InteractionNet.WiringEmbedding
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Composing boundary matchings

Two boundary matchings can be connected along their shared interface before either is
attached to a graph. Their remaining endpoints form the composite external matching.
Composition retains any closed wire components created along the shared interface.

## Main definitions

* {lit}`Wiring.composeBoundary` — join two matchings along their common interface.

## Main statements

* {lit}`Wiring.composeBoundary_spec` — the composite embeds in the spliced ambient matching.

## Tags

interaction net, graph, boundary, composition, matching, closed wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

open scoped FinEnum

variable {B Γ Δ : Type}

/-- Pair the shared boundary occurrences, with the outer matching's occurrence first. -/
def composeBoundaryPorts (B Γ Δ : Type) : Γ × Bool ↪ (Γ ⊕ B) ⊕ (Δ ⊕ Γ) where
  toFun p := if p.2 then .inl (.inl p.1) else .inr (.inr p.1)
  inj' := by
    rintro ⟨p, b⟩ ⟨q, c⟩ h
    cases b <;> cases c <;> simp_all

/-- Only the outer external boundary and the inner attachment positions survive composition. -/
def composeBoundaryEquiv (B Γ Δ : Type) :
    {p : (Γ ⊕ B) ⊕ (Δ ⊕ Γ) // ∀ i b, p ≠ composeBoundaryPorts B Γ Δ (i, b)} ≃ Δ ⊕ B where
  toFun p := match p with
    | ⟨.inl (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inl (.inr p), _⟩ => .inr p
    | ⟨.inr (.inl p), _⟩ => .inl p
    | ⟨.inr (.inr i), h⟩ => (h i false rfl).elim
  invFun p := match p with
    | .inl p => ⟨.inr (.inl p), by intro i b; cases b <;> intro h <;> cases h⟩
    | .inr p => ⟨.inl (.inr p), by intro i b; cases b <;> intro h <;> cases h⟩
  left_inv p := match p with
    | ⟨.inl (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inl (.inr _), _⟩ => rfl
    | ⟨.inr (.inl _), _⟩ => rfl
    | ⟨.inr (.inr i), h⟩ => (h i false rfl).elim
  right_inv p := by cases p <;> rfl

/-- Locate the surviving composite endpoints in the original pair of matchings. -/
def composeBoundaryEmbedding (B Γ Δ : Type) : Δ ⊕ B ↪ (Γ ⊕ B) ⊕ (Δ ⊕ Γ) :=
  (composeBoundaryEquiv B Γ Δ).symm.toEmbedding.trans (.subtype _)

/-- Compose finite boundary matchings, retaining the closed wires formed at their interface. -/
def composeBoundary [FinEnum B] [FinEnum Γ] [FinEnum Δ]
    (w : Wiring (Γ ⊕ B)) (v : Wiring (Δ ⊕ Γ)) : Wiring (Δ ⊕ B) × ℕ :=
  let s := gluedFinite (composeBoundaryPorts B Γ Δ) (FinEnum.toList Γ)
    FinEnum.nodup_toList FinEnum.mem_toList (w.sum v, 0)
  (s.1.map (composeBoundaryEquiv B Γ Δ), s.2)

/-- The composite matching and its loop count represent exactly the shared-boundary splices. -/
theorem composeBoundary_spec [FinEnum B] [FinEnum Γ] [FinEnum Δ]
    (w : Wiring (Γ ⊕ B)) (v : Wiring (Δ ⊕ Γ)) :
    let s := glue (composeBoundaryPorts B Γ Δ) (FinEnum.toList Γ) (w.sum v, 0)
    Respects (composeBoundaryEmbedding B Γ Δ) (composeBoundary w v).1 s.1 ∧
      (composeBoundary w v).2 = s.2 := by
  simp only [composeBoundary, gluedFinite_eq]
  exact ⟨(respects_map_symm (composeBoundaryEquiv B Γ Δ) _).trans
    (respects_glued _ _ FinEnum.nodup_toList FinEnum.mem_toList _), rfl⟩

end Geb.InteractionNet.Wiring

end
