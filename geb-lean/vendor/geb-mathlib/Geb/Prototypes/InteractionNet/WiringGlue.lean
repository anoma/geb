/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.WiringSplice
public import Mathlib.Logic.Embedding.Basic

set_option doc.verso true in
/-!
# Gluing a finite family of wires

A family of disjoint endpoint pairs specifies a gluing. The pairs may be processed in
any order: each operation reconnects incident wires and records a closed component when
it closes a wire. The detached endpoints can then be removed. This gives an executable
form of finite boundary gluing, including the loops in \[DeFalco2010\], Definition 4.1.

## Main definitions

* {lit}`Wiring.glueAt` — splice one pair, retaining the closed-wire count.
* {lit}`Wiring.glue` — process a finite list of pairs.
* {lit}`Wiring.glued` — remove all gluing endpoints from the resulting matching.

## Main statements

* {lit}`Wiring.glue_perm` — permuting the gluing order preserves wires and closed loops.
* {lit}`Wiring.glue_paired` — processed endpoints remain isolated from the surviving net.

## References

* \[DeFalco2010\], Section 2 and Definition 4.1.

## Tags

interaction net, gluing, wire, closed loop, permutation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

universe u v

variable {P : Type u} {I : Type v}

/-- The two endpoints of one gluing pair are distinct. -/
theorem pair_ne (ports : I × Bool ↪ P) (i : I) : ports (i, false) ≠ ports (i, true) := by
  intro h
  have := congrArg Prod.snd (ports.injective h)
  cases this

/-- Different gluing pairs have disjoint endpoints. -/
theorem pair_ne_of_ne (ports : I × Bool ↪ P) {i j : I} (h : i ≠ j) (a b : Bool) :
    ports (i, a) ≠ ports (j, b) := fun he ↦ h (congrArg Prod.fst (ports.injective he))

variable [DecidableEq P]

/-- Splice one pair and add any new closed wire to the running count. -/
def glueAt (ports : I × Bool ↪ P) (s : Wiring P × ℕ) (i : I) : Wiring P × ℕ :=
  (s.1.force (ports (i, false)) (ports (i, true)),
    s.2 + s.1.loopDelta (ports (i, false)) (ports (i, true)))

/-- Operations for distinct gluing pairs commute, and repeated operations commute trivially. -/
theorem glueAt_comm (ports : I × Bool ↪ P) (s : Wiring P × ℕ) (i j : I) :
    glueAt ports (glueAt ports s i) j = glueAt ports (glueAt ports s j) i := by
  by_cases he : ports (i, false) = ports (j, false)
  · have h : i = j := congrArg Prod.fst (ports.injective he)
    subst j
    rfl
  have h : i ≠ j := fun h ↦ he (congrArg (fun i ↦ ports (i, false)) h)
  apply Prod.ext
  · exact force_force s.1 (pair_ne ports i) (pair_ne ports j)
      (pair_ne_of_ne ports h false false) (pair_ne_of_ne ports h false true)
      (pair_ne_of_ne ports h true false) (pair_ne_of_ne ports h true true)
  · dsimp only [glueAt]
    rw [Nat.add_assoc, Nat.add_assoc,
      loopDelta_force s.1 (pair_ne ports i) (pair_ne ports j)
        (pair_ne_of_ne ports h false false) (pair_ne_of_ne ports h false true)
        (pair_ne_of_ne ports h true false) (pair_ne_of_ne ports h true true)]

/-- Process gluing pairs in the specified order. -/
def glue (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ) : Wiring P × ℕ :=
  order.foldl (glueAt ports) s

/-- Reordering a list of gluing pairs preserves both the wiring and the number of loops. -/
theorem glue_perm (ports : I × Bool ↪ P) {order order' : List I}
    (h : order.Perm order') (s : Wiring P × ℕ) : glue ports order s = glue ports order' s :=
  h.foldl_eq' (fun i _ j _ t ↦ glueAt_comm ports t i j) s

/-- Each processed pair becomes a detached wire. -/
theorem glueAt_paired (ports : I × Bool ↪ P) (s : Wiring P × ℕ) (i : I) :
    (glueAt ports s i).1.partner (ports (i, false)) = ports (i, true) :=
  force_left s.1 (pair_ne ports i)

/-- Later splices preserve every pair that has already been detached. -/
theorem glueAt_keeps (ports : I × Bool ↪ P) (s : Wiring P × ℕ) (i j : I)
    (h : s.1.partner (ports (i, false)) = ports (i, true)) :
    (glueAt ports s j).1.partner (ports (i, false)) = ports (i, true) := by
  by_cases he : ports (i, false) = ports (j, false)
  · have hij : i = j := congrArg Prod.fst (ports.injective he)
    subst j
    exact glueAt_paired ports s i
  have hij : i ≠ j := fun h ↦ he (congrArg (fun i ↦ ports (i, false)) h)
  exact force_keeps s.1 (pair_ne ports j)
    (pair_ne_of_ne ports hij false false) (pair_ne_of_ne ports hij false true)
    (pair_ne_of_ne ports hij true false) (pair_ne_of_ne ports hij true true) h

/-- A pair is detached after gluing if it was already detached or occurs in the order. -/
theorem glue_paired (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ) (i : I)
    (h : s.1.partner (ports (i, false)) = ports (i, true) ∨ i ∈ order) :
    (glue ports order s).1.partner (ports (i, false)) = ports (i, true) := by
  revert s
  refine List.rec ?_ ?_ order
  · intro s h
    exact h.elim id (fun hm ↦ (List.not_mem_nil hm).elim)
  · intro j js ih s h
    apply ih
    rcases h with h | h
    · exact Or.inl (glueAt_keeps ports s i j h)
    · rcases List.mem_cons.mp h with h | h
      · subst j
        exact Or.inl (glueAt_paired ports s i)
      · exact Or.inr h

/-- A wire between surviving endpoints is untouched by gluing. -/
theorem glue_keeps (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ)
    {p q : P} (hp : ∀ i b, p ≠ ports (i, b)) (hq : ∀ i b, q ≠ ports (i, b))
    (hw : s.1.partner p = q) : (glue ports order s).1.partner p = q := by
  revert s
  refine List.rec (fun _ h ↦ h) ?_ order
  intro i order ih s hw
  exact ih (glueAt ports s i)
    (force_keeps s.1 (pair_ne ports i) (hp i false) (hp i true) (hq i false) (hq i true) hw)

/-- Endpoints outside a complete family of cuts remain outside it after gluing. -/
theorem glue_closed (ports : I × Bool ↪ P) (order : List I) (cover : ∀ i, i ∈ order)
    (s : Wiring P × ℕ) (p : P) (hp : ∀ i b, p ≠ ports (i, b)) :
    ∀ i b, (glue ports order s).1.partner p ≠ ports (i, b) := by
  intro i b h
  have he := (glue ports order s).1.partner_eq_iff.mp h
  have hi := glue_paired ports order s i (Or.inr (cover i))
  cases b with
  | false => exact hp i true (he.trans hi)
  | true =>
    apply hp i false
    have hr := (glue ports order s).1.partner_partner (ports (i, false))
    rw [hi] at hr
    exact he.trans hr

/-- Glue every pair exactly once, then remove the detached endpoints. -/
@[nolint unusedArguments]
def glued (ports : I × Bool ↪ P) (order : List I) (_unique : order.Nodup)
    (cover : ∀ i, i ∈ order)
    (s : Wiring P × ℕ) : Wiring {p // ∀ i b, p ≠ ports (i, b)} × ℕ :=
  ((glue ports order s).1.restrict _ (glue_closed ports order cover s),
    (glue ports order s).2)

/-- Removing the glued endpoints preserves independence from the processing order. -/
theorem glued_perm (ports : I × Bool ↪ P) {order order' : List I}
    (h : order.Perm order') (unique : order.Nodup) (unique' : order'.Nodup)
    (cover : ∀ i, i ∈ order) (cover' : ∀ i, i ∈ order') (s : Wiring P × ℕ) :
    glued ports order unique cover s = glued ports order' unique' cover' s := by
  apply Prod.ext
  · apply Wiring.ext
    funext p
    apply Subtype.ext
    change (glue ports order s).1.partner p = (glue ports order' s).1.partner p
    rw [glue_perm ports h s]
  · change (glue ports order s).2 = (glue ports order' s).2
    exact congrArg Prod.snd (glue_perm ports h s)

/-- Endpoint renaming commutes with one gluing operation, including its closed-wire count. -/
theorem glueAt_map {Q : Type*} [DecidableEq Q] (e : P ≃ Q) (ports : I × Bool ↪ P)
    (s : Wiring P × ℕ) (i : I) :
    glueAt (ports.trans e.toEmbedding) (s.1.map e, s.2) i =
      ((glueAt ports s i).1.map e, (glueAt ports s i).2) := by
  apply Prod.ext
  · exact (force_map e s.1 (pair_ne ports i)).symm
  · exact congrArg (s.2 + ·) (loopDelta_map e s.1 _ _)

/-- Renaming the endpoints before or after a finite gluing gives the same result. -/
theorem glue_map {Q : Type*} [DecidableEq Q] (e : P ≃ Q) (ports : I × Bool ↪ P)
    (order : List I) (s : Wiring P × ℕ) :
    glue (ports.trans e.toEmbedding) order (s.1.map e, s.2) =
      ((glue ports order s).1.map e, (glue ports order s).2) := by
  revert s
  refine List.rec (fun _ ↦ rfl) ?_ order
  intro i order ih s
  change glue (ports.trans e.toEmbedding) order
    (glueAt (ports.trans e.toEmbedding) (s.1.map e, s.2) i) =
      ((glue ports order (glueAt ports s i)).1.map e,
        (glue ports order (glueAt ports s i)).2)
  rw [glueAt_map e ports s i, ih]

end Geb.InteractionNet.Wiring

end
