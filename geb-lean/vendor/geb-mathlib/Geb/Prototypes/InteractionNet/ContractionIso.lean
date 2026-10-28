/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionEmbedding
public import Geb.Prototypes.InteractionNet.WiringIndex

set_option doc.verso true in
/-!
# Contraction respects cell renaming

A boundary-preserving isomorphism transports active pairs and their contractions.
The auxiliary boundary follows the cell symbols' equal arities; port positions remain
unchanged. Both contractions embed in the same renamed ambient gluing.

## Main definitions

* {lit}`PortNet.reboundary` — transport an external boundary along a bijection.
* {lit}`PortNet.remainingEquiv` — restrict a cell bijection after deleting an active pair.
* {lit}`PortNet.Iso.contract` — transport a contraction along a net isomorphism.

## References

* \[DeFalco2010\], Definitions 3.2 and 5.2.

## Tags

interaction net, contraction, isomorphism, boundary, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

universe u v w x y z

variable {α : Type u} {C : Type v} {D : Type w} {E : Type x}
variable {Γ : Type y} {Δ : Type z} {arity : α → ℕ}
variable {label : C → α} {label' : D → α} {labelR : E → α}

/-- Transport only the external boundary, preserving cells, port order and closed wires. -/
def reboundary (n : PortNet arity label Γ) (b : Γ ≃ Δ) : PortNet arity label Δ :=
  ⟨n.wiring.map (endpointEquiv arity b (Equiv.refl C) (fun _ ↦ rfl)), n.loops⟩

/-- Equal cell symbols identify the auxiliary boundaries without changing port positions. -/
def pairEquiv (arity : α → ℕ) (e : C ≃ D) (h : ∀ c, label' (e c) = label c) (a b : C) :
    PairBoundary arity label a b ≃ PairBoundary arity label' (e a) (e b) :=
  Equiv.sumCongr (finCongr (congrArg arity (h a).symm))
    (finCongr (congrArg arity (h b).symm))

/-- Restrict a cell bijection to the cells surviving deletion of a selected pair. -/
def remainingEquiv (e : C ≃ D) (a b : C) :
    RemainingCell a b ≃ RemainingCell (e a) (e b) where
  toFun c := ⟨e c, fun he ↦ c.property.1 (e.injective he),
    fun he ↦ c.property.2 (e.injective he)⟩
  invFun d := ⟨e.symm d,
    fun he ↦ d.property.1 ((e.apply_symm_apply d).symm.trans (congrArg e he)),
    fun he ↦ d.property.2 ((e.apply_symm_apply d).symm.trans (congrArg e he))⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c)
  right_inv d := Subtype.ext (e.apply_symm_apply d)

/-- The result's surviving and inserted cells retain their symbols under cell renaming. -/
theorem remainingEquiv_label (e : C ≃ D) (h : ∀ c, label' (e c) = label c)
    (a b : C) (c : RemainingCell a b ⊕ E) :
    Sum.elim (fun d : RemainingCell (e a) (e b) ↦ label' d) labelR
      ((Equiv.sumCongr (remainingEquiv e a b) (Equiv.refl E)) c) =
        Sum.elim (fun d : RemainingCell a b ↦ label d) labelR c := by
  cases c with
  | inl c => exact h c
  | inr c => rfl

namespace Iso

/-- An isomorphism preserves wire partners through its endpoint bijection. -/
theorem respects {n : PortNet arity label Γ} {m : PortNet arity label' Γ} (i : Iso n m) :
    Wiring.Respects (endpointEquiv arity (Equiv.refl Γ) i.cells i.label_eq).toEmbedding
      n.wiring m.wiring := by
  rw [← i.wiring_eq]
  exact Wiring.respects_map _ _

/-- An isomorphism transports an active pair to the corresponding pair of cells. -/
theorem active {n : PortNet arity label Γ} {m : PortNet arity label' Γ} (i : Iso n m)
    {a b : C} (h : n.Active a b) : m.Active (i.cells a) (i.cells b) := by
  have he := i.respects (principal arity label a)
  rw [h] at he
  exact he

end Iso

variable [DecidableEq C] [DecidableEq D]

/-- Renaming the ambient graph transports the selected auxiliary splices. -/
theorem contractPorts_equiv (e : C ≃ D) (h : ∀ c, label' (e c) = label c)
    {a b : C} (hab : a ≠ b) :
    (contractPorts (Γ := Γ) arity label labelR hab).trans
        (Equiv.sumCongr (endpointEquiv arity (Equiv.refl Γ) e h)
          (endpointEquiv (label := labelR) (label' := labelR) arity
          (pairEquiv arity e h a b) (Equiv.refl E)
            (fun _ ↦ rfl))).toEmbedding =
      ((pairEquiv arity e h a b).prodCongr (Equiv.refl Bool)).toEmbedding.trans
        (contractPorts arity label' labelR (fun he ↦ hab (e.injective he))) := by
  ext p
  rcases p with ⟨p, side⟩
  cases p <;> cases side <;> rfl

/-- The result's endpoint renaming agrees with its embedding in the renamed ambient graph. -/
theorem contractEmbedding_equiv (e : C ≃ D) (h : ∀ c, label' (e c) = label c)
    {a b : C} (hab : a ≠ b)
    (p : Endpoint arity (Sum.elim (fun c : RemainingCell a b ↦ label c) labelR) Γ) :
    (Equiv.sumCongr (endpointEquiv arity (Equiv.refl Γ) e h)
      (endpointEquiv (label := labelR) (label' := labelR) arity
          (pairEquiv arity e h a b) (Equiv.refl E) (fun _ ↦ rfl)))
        (contractEmbedding arity label labelR hab p) =
      contractEmbedding arity label' labelR (fun he ↦ hab (e.injective he))
        (endpointEquiv arity (Equiv.refl Γ)
          (Equiv.sumCongr (remainingEquiv e a b) (Equiv.refl E))
          (remainingEquiv_label e h a b) p) := by
  cases p with
  | inl p => rfl
  | inr p =>
    rcases p with ⟨c, p⟩
    cases c <;> rfl

variable [DecidableEq E] [DecidableEq Γ]

/-- A renamed contraction embeds in the same ambient gluing as its renamed input. -/
theorem Iso.contract_respects {n : PortNet arity label Γ} {m : PortNet arity label' Γ}
    (i : Iso n m) {a b : C} (hab : n.Active a b)
    (rhs : PortNet arity labelR (PairBoundary arity label a b)) :
    let rhs' := rhs.reboundary (pairEquiv arity i.cells i.label_eq a b)
    let e := Equiv.sumCongr (endpointEquiv arity (Equiv.refl Γ) i.cells i.label_eq)
      (endpointEquiv (label := labelR) (label' := labelR) arity
        (pairEquiv arity i.cells i.label_eq a b) (Equiv.refl E) (fun _ ↦ rfl))
    let g := Wiring.glue (contractPorts arity label' labelR (active_ne (i.active hab)))
      (FinEnum.toList _) (m.wiring.sum rhs'.wiring, m.loops + rhs'.loops)
    Wiring.Respects ((contractEmbedding arity label labelR (active_ne hab)).trans e.toEmbedding)
      (n.contract hab rhs).wiring g.1 ∧ (n.contract hab rhs).loops = g.2 := by
  dsimp only
  let rhs' := rhs.reboundary (pairEquiv arity i.cells i.label_eq a b)
  let e := Equiv.sumCongr (endpointEquiv arity (Equiv.refl Γ) i.cells i.label_eq)
    (endpointEquiv (label := labelR) (label' := labelR) arity
      (pairEquiv arity i.cells i.label_eq a b) (Equiv.refl E) (fun _ ↦ rfl))
  have he := i.respects.sum (Wiring.respects_map
    (endpointEquiv (label := labelR) (label' := labelR) arity
      (pairEquiv arity i.cells i.label_eq a b) (Equiv.refl E) (fun _ ↦ rfl)) rhs.wiring)
  have hs := n.contract_in hab rhs e.toEmbedding
    (m.wiring.sum rhs'.wiring, m.loops + rhs'.loops) he 0
    (by simpa only [Nat.add_zero, rhs', reboundary] using congrArg (· + rhs.loops) i.loops_eq)
  dsimp only [e] at hs
  rw [contractPorts_equiv (arity := arity) (labelR := labelR) i.cells i.label_eq (active_ne hab),
    Wiring.glue_enum_equiv] at hs
  exact ⟨hs.1, (Nat.add_zero _).symm.trans hs.2⟩

/-- Cell renaming commutes with contraction, including the count of closed wires. -/
def Iso.contract {n : PortNet arity label Γ} {m : PortNet arity label' Γ} (i : Iso n m)
    {a b : C} (hab : n.Active a b)
    (rhs : PortNet arity labelR (PairBoundary arity label a b)) :
    Iso (n.contract hab rhs)
      (m.contract (i.active hab) (rhs.reboundary (pairEquiv arity i.cells i.label_eq a b))) where
  cells := Equiv.sumCongr (remainingEquiv i.cells a b) (Equiv.refl E)
  label_eq := remainingEquiv_label i.cells i.label_eq a b
  wiring_eq := by
    have hs := i.contract_respects hab rhs
    have ht := m.contract_spec (i.active hab)
      (rhs.reboundary (pairEquiv arity i.cells i.label_eq a b))
    exact hs.1.map_eq ht.1 _ (contractEmbedding_equiv i.cells i.label_eq (active_ne hab))
  loops_eq := (i.contract_respects hab rhs).2.trans
    (m.contract_spec (i.active hab)
      (rhs.reboundary (pairEquiv arity i.cells i.label_eq a b))).2.symm

end Geb.InteractionNet.PortNet

end
