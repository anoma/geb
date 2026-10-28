/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionIso
public import Geb.Prototypes.InteractionNet.WiringIndex
public import Geb.Prototypes.RoseTree.Basic
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Reading constructor trees from port graphs

Read-back follows a boundary wire to a cell's principal port, checks its constructor tag,
and then visits the auxiliary ports in order. A depth bound makes traversal total on
arbitrary graphs, including cyclic graphs. The traversal also records every visited cell.
The whole-net reader accepts only when no closed wires remain and the traversal visits
every cell exactly once, checked by a duplicate-free visit list of the required length.

## Main definitions

* {lit}`PortNet.readTree` — bounded constructor-tree traversal with its visited cells.
* {lit}`FiniteNet.readTree` — read the whole graph at its sole external boundary.

## Main statements

* {lit}`PortNet.Iso.readTree` — cell renaming preserves bounded tree traversal.
* {lit}`FiniteNet.readTree_iso` — whole-net read-back is invariant under cell renaming.

## Tags

interaction net, graph, read-back, tree, constructor, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α C D Γ : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}

namespace PortNet

/-- Build one observed node after all of its ordered children have been read. -/
def readNode (tag : α → Option ℕ) (a : α) (c : C)
    (children : Fin (arity a) → Option (RoseTree ℕ × List C)) :
    Option (RoseTree ℕ × List C) := do
  let l ← tag a
  let cs ← (List.ofFn children).mapM id
  pure (RoseTree.node l (cs.map Prod.fst), c :: cs.flatMap Prod.snd)

/-- Follow principal wires and ordered auxiliary fields, retaining the visited cell identities. -/
def readTree (tag : α → Option ℕ) (n : PortNet arity label Γ) (fuel : ℕ) :
    Endpoint arity label Γ → Option (RoseTree ℕ × List C) :=
  Nat.rec (fun _ ↦ none) (fun _ ih p ↦
    match n.wiring.partner p with
    | .inl _ => none
    | .inr ⟨c, q⟩ =>
      if q.val = 0 then readNode tag (label c) c (fun i ↦ ih (.inr ⟨c, i.succ⟩))
      else none) fuel

private theorem sequence_map {X Y : Type} (f : X → Y) (xs : List (Option X)) :
    (xs.map (Option.map f)).mapM id = (xs.mapM id).map (List.map f) := by
  apply List.rec (motive := fun xs : List (Option X) ↦
    (xs.map (Option.map f)).mapM id = (xs.mapM id).map (List.map f)) rfl
    (fun x xs ih ↦ ?_) xs
  simp only [List.map_cons, List.mapM_cons, ih]
  cases x <;> cases xs.mapM id <;> rfl

/-- Relabeling visited cells commutes with assembling one observed node. -/
theorem readNode_map (tag : α → Option ℕ) (a : α) (c : C) (e : C → D)
    (children : Fin (arity a) → Option (RoseTree ℕ × List C)) :
    readNode tag a (e c) (fun i ↦ (children i).map (fun r ↦ (r.1, r.2.map e))) =
      (readNode tag a c children).map (fun r ↦ (r.1, r.2.map e)) := by
  unfold readNode
  have hs := sequence_map (fun r : RoseTree ℕ × List C ↦ (r.1, r.2.map e))
    (List.ofFn children)
  rw [List.map_ofFn] at hs
  dsimp only [Function.comp_def] at hs
  rw [hs]
  cases tag a with
  | none => rfl
  | some l =>
    cases (List.ofFn children).mapM id with
    | none => rfl
    | some cs =>
      simp only [bind, Option.bind_some, Option.map_some, pure, List.map_map, List.map_cons,
        List.flatMap_map, List.map_flatMap, Function.comp_def]

/-- Renaming graph cells preserves traversal and renames exactly its recorded cells. -/
theorem Iso.readTree {n : PortNet arity label Γ} {m : PortNet arity label' Γ} (e : n.Iso m)
    (tag : α → Option ℕ) (fuel : ℕ) (p : Endpoint arity label Γ) :
    m.readTree tag fuel (endpointEquiv arity (Equiv.refl Γ) e.cells e.label_eq p) =
      (n.readTree tag fuel p).map (fun r ↦ (r.1, r.2.map e.cells)) := by
  refine Nat.rec (motive := fun fuel ↦ ∀ p : Endpoint arity label Γ,
    m.readTree tag fuel (endpointEquiv arity (Equiv.refl Γ) e.cells e.label_eq p) =
      (n.readTree tag fuel p).map (fun r ↦ (r.1, r.2.map e.cells))) (fun _ ↦ rfl)
      (fun fuel ih p ↦ ?_) fuel p
  change (match m.wiring.partner (endpointEquiv arity (Equiv.refl Γ) e.cells e.label_eq p) with
    | .inl _ => none
    | .inr ⟨c, q⟩ => if q.val = 0 then
        readNode tag (label' c) c (fun i ↦ m.readTree tag fuel (.inr ⟨c, i.succ⟩))
      else none) = _
  have he : m.wiring.partner (endpointEquiv arity (Equiv.refl Γ) e.cells e.label_eq p) =
      endpointEquiv arity (Equiv.refl Γ) e.cells e.label_eq (n.wiring.partner p) := e.respects p
  rw [he]
  cases hp : n.wiring.partner p with
  | inl b =>
    simp only [PortNet.readTree, hp, endpointEquiv_boundary, Option.map_none]
  | inr cp =>
    rcases cp with ⟨c, q⟩
    simp only [endpointEquiv_cell, Fin.val_cast]
    change (if q.val = 0 then
      readNode tag (label' (e.cells c)) (e.cells c)
        (fun i ↦ m.readTree tag fuel (.inr ⟨e.cells c, i.succ⟩)) else none) = _
    have hr : n.readTree tag (fuel + 1) p =
        if q.val = 0 then readNode tag (label c) c
          (fun i ↦ n.readTree tag fuel (.inr ⟨c, i.succ⟩)) else none := by
      simp only [PortNet.readTree, hp]
    rw [hr]
    by_cases hq : q.val = 0
    · simp only [hq, ↓reduceIte]
      have hn (a b : α) (h : a = b)
          (cs : Fin (arity a) → Option (RoseTree ℕ × List D))
          (ds : Fin (arity b) → Option (RoseTree ℕ × List C))
          (hc : ∀ i, cs (Fin.cast (congrArg arity h.symm) i) =
            (ds i).map (fun r ↦ (r.1, r.2.map e.cells))) :
          readNode tag a (e.cells c) cs =
            (readNode tag b c ds).map (fun r ↦ (r.1, r.2.map e.cells)) := by
        subst b
        simpa only [Fin.cast_refl, ← hc, id_eq] using readNode_map tag a c e.cells ds
      apply hn _ _ (e.label_eq c)
      intro i
      exact ih (.inr ⟨c, i.succ⟩)
    · simp only [hq, ↓reduceIte, Option.map_none]

end PortNet

namespace FiniteNet

/-- Isomorphic finite ordinal cell types have the same number of cells, constructively. -/
theorem cells_eq_of_iso {n m : ℕ} (e : Fin n ≃ Fin m) : n = m := by
  let en : FinEnum (Fin n) := { card := n, equiv := Equiv.refl _, decEq := inferInstance }
  let em : FinEnum (Fin m) := { card := m, equiv := Equiv.refl _, decEq := inferInstance }
  have h := (@Wiring.enum_perm (Fin n) (Fin m) en em e).length_eq
  have hn : @FinEnum.card (Fin n) en = n := rfl
  have hm : @FinEnum.card (Fin m) em = m := rfl
  have hc : @FinEnum.card (Fin n) en = @FinEnum.card (Fin m) em := by
    simpa only [FinEnum.toList, List.length_map, List.length_finRange] using h
  exact hn.symm.trans (hc.trans hm)

/-- Read a complete tree at the sole boundary, rejecting closed wires and unvisited cells. -/
def readTree (tag : α → Option ℕ) (n : FiniteNet arity 1) : Option (RoseTree ℕ) := do
  if n.2.2.loops ≠ 0 then none else
    let result ← n.2.2.readTree tag (n.1 + 1) (.inl 0)
    if result.2.length = n.1 ∧ result.2.Nodup then some result.1 else none

/-- Whole-net tree read-back is invariant under a boundary-preserving cell renaming. -/
theorem readTree_iso (tag : α → Option ℕ) {n m : FiniteNet arity 1}
    (e : n.2.2.Iso m.2.2) : readTree tag n = readTree tag m := by
  rcases n with ⟨k, label, n⟩
  rcases m with ⟨k', label', m⟩
  have hc := cells_eq_of_iso e.cells
  change k = k' at hc
  subst k'
  have hr := e.readTree tag (k + 1) (.inl 0)
  rw [endpointEquiv_boundary, Equiv.refl_apply] at hr
  unfold readTree
  rw [← e.loops_eq, hr]
  split
  · rfl
  · cases n.readTree tag (k + 1) (.inl 0) with
    | none => rfl
    | some result =>
      simp only [bind, Option.map_some, Option.bind_some, List.length_map,
        List.nodup_map_iff e.cells.injective]

end FiniteNet

end Geb.InteractionNet

end
