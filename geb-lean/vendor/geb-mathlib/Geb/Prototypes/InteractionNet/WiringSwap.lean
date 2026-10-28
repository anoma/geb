/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Wiring
public import Mathlib.Logic.Equiv.Sum

set_option doc.verso true in
/-!
# Renaming two allocated graph components

Exchanging the allocation order of two replacement graphs exchanges the two corresponding
summands of the endpoint type and preserves the original graph's endpoints.

## Main definitions

* {lit}`sumRightComm` — exchange the last two components of a left-associated sum.

## Main statements

* {lit}`Wiring.map_sumRightComm` — exchanging two graph components transports their matching.

## Tags

interaction net, allocation, sum, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

universe u v w

/-- Exchange the last two components, keeping the original component fixed. -/
def sumRightComm (P : Type u) (Q : Type v) (R : Type w) : (P ⊕ Q) ⊕ R ≃ (P ⊕ R) ⊕ Q :=
  (Equiv.sumAssoc P Q R).trans
    ((Equiv.sumCongr (Equiv.refl P) (Equiv.sumComm Q R)).trans (Equiv.sumAssoc P R Q).symm)

/-- The original component is fixed. -/
@[simp] theorem sumRightComm_original {P : Type u} {Q : Type v} {R : Type w} (p : P) :
    sumRightComm P Q R (.inl (.inl p)) = .inl (.inl p) := rfl

/-- The first allocated component moves to the last position. -/
@[simp] theorem sumRightComm_first {P : Type u} {Q : Type v} {R : Type w} (p : Q) :
    sumRightComm P Q R (.inl (.inr p)) = .inr p := rfl

/-- The last allocated component moves to the first allocation position. -/
@[simp] theorem sumRightComm_second {P : Type u} {Q : Type v} {R : Type w} (p : R) :
    sumRightComm P Q R (.inr p) = .inl (.inr p) := rfl

/-- Reversing the exchange performs the same exchange in the opposite direction. -/
@[simp] theorem sumRightComm_symm (P : Type u) (Q : Type v) (R : Type w) :
    (sumRightComm P Q R).symm = sumRightComm P R Q := by
  ext p
  rcases p with (p | p) | p <;> rfl

namespace Wiring

/-- Exchanging two disjoint components transports their matching without changing any wire. -/
theorem map_sumRightComm {P : Type u} {Q : Type v} {R : Type w}
    (s : Wiring P) (t : Wiring Q) (v : Wiring R) :
    ((s.sum t).sum v).map (sumRightComm P Q R) = (s.sum v).sum t := by
  ext p
  rcases p with (p | p) | p <;> rfl

end Wiring

end Geb.InteractionNet

end
