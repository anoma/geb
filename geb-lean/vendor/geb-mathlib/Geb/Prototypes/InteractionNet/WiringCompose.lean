/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Composition of local gluing operations

Gluing in one component leaves a disjoint component unchanged. Two families of cuts with
disjoint endpoints can be glued in either order, with identical matchings and loop counts.
These statements compare graph contractions after both replacement graphs have been
allocated in a common endpoint space.

## Main statements

* {lit}`Wiring.glue_sum_left` — gluing commutes with adding a disjoint component.
* {lit}`Wiring.glue_glue` — disjoint families of cuts commute.

## References

* \[DeFalco2010\], Proposition 4.3 and the gluing argument in Proposition 5.3.

## Tags

interaction net, gluing, disjoint union, commutation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

universe u v w x

variable {P : Type u} {Q : Type v} {I : Type w} {J : Type x}
variable [DecidableEq P] [DecidableEq Q]

/-- Splicing in the left component leaves the right component unchanged. -/
theorem force_sum_left (s : Wiring P) (t : Wiring Q) {a b : P} (hab : a ≠ b) :
    (s.force a b).sum t = (s.sum t).force (.inl a) (.inl b) := by
  ext p
  cases p with
  | inl p => exact ((respects_inl s t).force hab p).symm
  | inr p =>
    symm
    refine force_keeps (s.sum t) (fun h ↦ hab (Sum.inl.inj h)) ?_ ?_ ?_ ?_ rfl
    all_goals intro h; cases h

/-- One gluing operation commutes with adding a disjoint component and its loop count. -/
theorem glueAt_sum_left (ports : I × Bool ↪ P) (s : Wiring P × ℕ) (t : Wiring Q)
    (k : ℕ) (i : I) :
    glueAt (ports.trans .inl) (s.1.sum t, s.2 + k) i =
      ((glueAt ports s i).1.sum t, (glueAt ports s i).2 + k) := by
  apply Prod.ext
  · exact (force_sum_left s.1 t (pair_ne ports i)).symm
  · change (s.2 + k) + (s.1.sum t).loopDelta (.inl (ports (i, false)))
      (.inl (ports (i, true))) = (s.2 + s.1.loopDelta (ports (i, false)) (ports (i, true))) + k
    have hl : s.1.loopDelta (ports (i, false)) (ports (i, true)) =
        (s.1.sum t).loopDelta (.inl (ports (i, false))) (.inl (ports (i, true))) :=
      (respects_inl s.1 t).loopDelta _ _
    rw [← hl]
    omega

/-- Finite gluing commutes with adding a disjoint component and its loop count. -/
theorem glue_sum_left (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ)
    (t : Wiring Q) (k : ℕ) :
    glue (ports.trans .inl) order (s.1.sum t, s.2 + k) =
      ((glue ports order s).1.sum t, (glue ports order s).2 + k) := by
  revert s
  refine List.rec (fun _ ↦ rfl) ?_ order
  intro i order ih s
  change glue (ports.trans .inl) order (glueAt (ports.trans .inl) (s.1.sum t, s.2 + k) i) =
    ((glue ports order (glueAt ports s i)).1.sum t, (glue ports order (glueAt ports s i)).2 + k)
  rw [glueAt_sum_left, ih]

omit [DecidableEq Q] in
/-- A cut from one family commutes with a cut from a disjoint family. -/
theorem glueAt_comm_other (ports : I × Bool ↪ P) (ports' : J × Bool ↪ P)
    (disjoint : ∀ i a j b, ports (i, a) ≠ ports' (j, b)) (s : Wiring P × ℕ) (i : I) (j : J) :
    glueAt ports' (glueAt ports s i) j = glueAt ports (glueAt ports' s j) i := by
  apply Prod.ext
  · exact force_force s.1 (pair_ne ports i) (pair_ne ports' j)
      (disjoint i false j false) (disjoint i false j true)
      (disjoint i true j false) (disjoint i true j true)
  · dsimp only [glueAt]
    rw [Nat.add_assoc, Nat.add_assoc, loopDelta_force s.1 (pair_ne ports i) (pair_ne ports' j)
      (disjoint i false j false) (disjoint i false j true)
      (disjoint i true j false) (disjoint i true j true)]

omit [DecidableEq Q] in
/-- A cut commutes with gluing an entire disjoint family. -/
theorem glueAt_glue (ports : I × Bool ↪ P) (ports' : J × Bool ↪ P)
    (disjoint : ∀ i a j b, ports (i, a) ≠ ports' (j, b)) (order : List J)
    (s : Wiring P × ℕ) (i : I) :
    glue ports' order (glueAt ports s i) = glueAt ports (glue ports' order s) i := by
  revert s
  refine List.rec (fun _ ↦ rfl) ?_ order
  intro j order ih s
  change glue ports' order (glueAt ports' (glueAt ports s i) j) =
    glueAt ports (glue ports' order (glueAt ports' s j)) i
  rw [glueAt_comm_other ports ports' disjoint, ih]

omit [DecidableEq Q] in
/-- Disjoint families of cuts can be glued in either order. -/
theorem glue_glue (ports : I × Bool ↪ P) (ports' : J × Bool ↪ P)
    (disjoint : ∀ i a j b, ports (i, a) ≠ ports' (j, b))
    (order : List I) (order' : List J) (s : Wiring P × ℕ) :
    glue ports' order' (glue ports order s) = glue ports order (glue ports' order' s) := by
  revert s
  refine List.rec (fun _ ↦ rfl) ?_ order
  intro i order ih s
  change glue ports' order' (glue ports order (glueAt ports s i)) =
    glue ports order (glueAt ports (glue ports' order' s) i)
  rw [ih, glueAt_glue ports ports' disjoint]

end Geb.InteractionNet.Wiring

end
