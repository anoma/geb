/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.WiringSubdivision
public import Mathlib.Data.List.Induction

set_option doc.verso true in
/-!
# Relocating endpoints along separate wires

When one side of every cut meets an endpoint outside all cuts, gluing only relocates the
other endpoints along those wires. The full matching is conjugated by explicit exchanges;
the detached cut pairs remain present until restriction. No closed wire is introduced.

## Main definitions

* {lit}`Wiring.relocation` — the endpoint permutation induced by the wire extensions.

## Main statements

* {lit}`Wiring.glue_relocation` — gluing wire extensions is endpoint relocation.

## Tags

interaction net, wire, subdivision, endpoint, permutation, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

variable {P I : Type*} [DecidableEq P]

/-- Exchange each retained wire end with the endpoint extended along that wire. -/
def relocation (w : Wiring P) (ports : I × Bool ↪ P) (order : List I) (side : Bool) :
    Equiv.Perm P :=
  order.foldl (fun e i ↦ e.trans (exchange (ports (i, !side)) (w.partner (ports (i, side)))))
    (Equiv.refl P)

/-- A final cut applies its exchange after all preceding relocations. -/
theorem relocation_append_singleton (w : Wiring P) (ports : I × Bool ↪ P) (order : List I)
    (i : I) (side : Bool) :
    w.relocation ports (order ++ [i]) side =
      (w.relocation ports order side).trans
        (exchange (ports (i, !side)) (w.partner (ports (i, side)))) := by
  simp only [relocation, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Endpoints outside every exchange are fixed by the complete relocation. -/
theorem relocation_apply_of_outside (w : Wiring P) (ports : I × Bool ↪ P) (order : List I)
    (side : Bool) (p : P)
    (outside : ∀ i ∈ order, p ≠ ports (i, !side) ∧ p ≠ w.partner (ports (i, side))) :
    w.relocation ports order side p = p := by
  revert outside
  refine List.reverseRecOn order (fun _ ↦ rfl) (fun order i ih outside ↦ ?_)
  rw [relocation_append_singleton]
  change exchange (ports (i, !side)) (w.partner (ports (i, side)))
    (w.relocation ports order side p) = p
  rw [ih (fun j hj ↦ outside j (List.mem_append_left _ hj))]
  have h := outside i (List.mem_append_right _ (List.mem_singleton_self i))
  change (if p = ports (i, !side) then _ else if p = w.partner (ports (i, side)) then _
    else p) = p
  simp only [h.1, h.2, ↓reduceIte]

/-- Every processed endpoint is moved to its distinct free wire end. -/
theorem relocation_apply_cut [DecidableEq I] (w : Wiring P) (ports : I × Bool ↪ P)
    (order : List I) (unique : order.Nodup) (side : Bool)
    (free : ∀ i j b, w.partner (ports (i, side)) ≠ ports (j, b)) (i : I) :
    w.relocation ports order side (ports (i, !side)) =
      if i ∈ order then w.partner (ports (i, side)) else ports (i, !side) := by
  revert unique
  refine List.reverseRecOn order (fun _ ↦ rfl) (fun order j ih unique ↦ ?_)
  have hu := List.nodup_append.mp unique
  have hj : j ∉ order := fun h ↦ hu.2.2 j h j (List.mem_singleton_self j) rfl
  rw [relocation_append_singleton]
  change exchange (ports (j, !side)) (w.partner (ports (j, side)))
    (w.relocation ports order side (ports (i, !side))) = _
  rw [ih hu.1]
  by_cases he : i = j
  · subst j
    simp only [hj, ↓reduceIte, List.mem_append, List.mem_singleton_self, or_true]
    change (if ports (i, !side) = ports (i, !side) then _ else _) = _
    exact if_pos rfl
  · have ha : ports (i, !side) ≠ ports (j, !side) := pair_ne_of_ne ports he _ _
    have hb : ports (i, !side) ≠ w.partner (ports (j, side)) := (free j i _).symm
    have hc : w.partner (ports (i, side)) ≠ w.partner (ports (j, side)) := by
      intro h
      exact he (congrArg Prod.fst (ports.injective (w.involutive.injective h)))
    by_cases hm : i ∈ order <;>
      simp [exchange, Equiv.swapCore, hm, he, ha, hb, hc, free]

/-- Gluing separate extensions only conjugates the matching and retains its closed-wire count. -/
theorem glue_relocation (ports : I × Bool ↪ P) (order : List I) (unique : order.Nodup)
    (w : Wiring P) (loops : ℕ) (side : Bool)
    (free : ∀ i ∈ order, ∀ j ∈ order, ∀ b, w.partner (ports (i, side)) ≠ ports (j, b)) :
    glue ports order (w, loops) = (w.map (w.relocation ports order side), loops) := by
  apply Prod.ext
  · revert unique free
    refine List.reverseRecOn order (motive := fun order ↦ order.Nodup →
      (∀ i ∈ order, ∀ j ∈ order, ∀ b, w.partner (ports (i, side)) ≠ ports (j, b)) →
        (glue ports order (w, loops)).1 = w.map (w.relocation ports order side))
      (fun _ _ ↦ (map_refl w).symm) (fun order i ih unique free ↦ ?_)
    have hu := List.nodup_append.mp unique
    have hi : i ∉ order := fun h ↦ hu.2.2 i h i (List.mem_singleton_self i) rfl
    have head : (glue ports order (w, loops)).1.partner (ports (i, side)) =
        w.partner (ports (i, side)) := by
      apply glue_keeps_on
      · intro j hj b
        have hij : i ≠ j := fun he ↦ hi (he.symm ▸ hj)
        exact pair_ne_of_ne ports hij side b
      · intro j hj b
        exact free i (List.mem_append_right _ (List.mem_singleton_self i))
          j (List.mem_append_left _ hj) b
      · rfl
    have h := ih hu.1 (fun i hi j hj b ↦
      free i (List.mem_append_left _ hi) j (List.mem_append_left _ hj) b)
    change (glue ports (order ++ [i]) (w, loops)).1 = _
    simp only [glue, List.foldl_append, List.foldl_cons, List.foldl_nil, glueAt]
    have hs (v : Wiring P) : v.force (ports (i, false)) (ports (i, true)) =
        v.map (exchange (ports (i, !side)) (v.partner (ports (i, side)))) := by
      cases side with
      | false => rfl
      | true => exact force_comm v (pair_ne ports i)
    rw [hs]
    change ((glue ports order (w, loops)).1.map
      (exchange (ports (i, !side)) ((glue ports order (w, loops)).1.partner
        (ports (i, side))))) = _
    rw [head, h, ← map_trans]
    simp only [relocation, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · exact glue_loops_of_free_side ports order unique (w, loops) side free

end Geb.InteractionNet.Wiring

end
