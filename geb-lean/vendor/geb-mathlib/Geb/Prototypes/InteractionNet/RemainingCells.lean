/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.OpenPair

set_option doc.verso true in
/-!
# Cell indices after two contractions

Two disjoint contractions remove the same original cells and insert the same two families
of replacement cells. Their cell types differ only in the nesting of subtypes and the order
of the two inserted families. These explicit bijections identify the two results while
preserving each surviving cell's original identity.

## Main definitions

* {lit}`PortNet.remainingSumEquiv` — removal in one component preserves the other component.
* {lit}`PortNet.remainingSwap` — removing two disjoint pairs in either order gives the same cells.
* {lit}`PortNet.contractionCellsEquiv` — the cell bijection for commuting two contractions.

## Tags

interaction net, cell, renaming, contraction, disjointness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

universe u v w

variable {C : Type u} {D : Type v} {E : Type w}

/-- Removing two cells from the left summand leaves the right summand intact. -/
def remainingSumEquiv (a b : C) :
    RemainingCell (Sum.inl a : C ⊕ D) (.inl b) ≃ RemainingCell a b ⊕ D where
  toFun p := match p with
    | ⟨.inl c, h⟩ => .inl ⟨c, (fun he ↦ h.1 (congrArg Sum.inl he)),
        (fun he ↦ h.2 (congrArg Sum.inl he))⟩
    | ⟨.inr d, _⟩ => .inr d
  invFun p := match p with
    | .inl c => ⟨.inl c.val, (fun he ↦ c.property.1 (Sum.inl.inj he)),
        (fun he ↦ c.property.2 (Sum.inl.inj he))⟩
    | .inr d => ⟨.inr d, by constructor <;> intro h <;> cases h⟩
  left_inv p := by rcases p with ⟨c | d, h⟩ <;> rfl
  right_inv p := by cases p <;> rfl

/-- Reorder the removal of two disjoint pairs of original cells. -/
def remainingSwap (a b c d : C) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    RemainingCell (⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b) ⟨d, had.symm, hbd.symm⟩ ≃
      RemainingCell (⟨a, hac, had⟩ : RemainingCell c d) ⟨b, hbc, hbd⟩ where
  toFun p := ⟨⟨p.val.val, (fun h ↦ p.property.1 (Subtype.ext h)),
      (fun h ↦ p.property.2 (Subtype.ext h))⟩,
    (fun h ↦ p.val.property.1 (congrArg Subtype.val h)),
    (fun h ↦ p.val.property.2 (congrArg Subtype.val h))⟩
  invFun p := ⟨⟨p.val.val, (fun h ↦ p.property.1 (Subtype.ext h)),
      (fun h ↦ p.property.2 (Subtype.ext h))⟩,
    (fun h ↦ p.val.property.1 (congrArg Subtype.val h)),
    (fun h ↦ p.val.property.2 (congrArg Subtype.val h))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Match the cell types resulting from the two orders of disjoint contractions. -/
def contractionCellsEquiv (a b c d : C)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (RemainingCell (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D)
      (.inl ⟨d, had.symm, hbd.symm⟩) ⊕ E) ≃
    (RemainingCell (.inl ⟨a, hac, had⟩ : RemainingCell c d ⊕ E)
      (.inl ⟨b, hbc, hbd⟩) ⊕ D) :=
  (Equiv.sumCongr (remainingSumEquiv _ _) (Equiv.refl E)).trans
    ((Equiv.sumAssoc _ D E).trans
      ((Equiv.sumCongr (remainingSwap a b c d hac had hbc hbd) (Equiv.sumComm D E)).trans
        ((Equiv.sumAssoc _ E D).symm.trans
          (Equiv.sumCongr (remainingSumEquiv _ _).symm (Equiv.refl D)))))

/-- The cell bijection preserves symbols of original cells and of both replacements. -/
theorem contractionCellsEquiv_label {α : Type*} (label : C → α) (labelD : D → α) (labelE : E → α)
    (a b c d : C) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (p : RemainingCell (.inl ⟨c, hac.symm, hbc.symm⟩ : RemainingCell a b ⊕ D)
      (.inl ⟨d, had.symm, hbd.symm⟩) ⊕ E) :
    Sum.elim (fun p ↦ Sum.elim (fun c ↦ label c.val) labelE p.val) labelD
      (contractionCellsEquiv a b c d hac had hbc hbd p) =
    Sum.elim (fun p ↦ Sum.elim (fun c ↦ label c.val) labelD p.val) labelE p := by
  rcases p with ⟨c | d, h⟩ | e <;> rfl

end Geb.InteractionNet.PortNet

end
