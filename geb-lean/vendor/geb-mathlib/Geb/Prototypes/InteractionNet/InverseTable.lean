/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Tactic.TypeStar

set_option doc.verso true in
/-!
# Inverse tables of finite embeddings

An embedding into {lit}`Fin size` is inverted on a listed part of its domain by an array of
{lit}`size` optional entries, holding at the position of each listed element that element. The
table is built by one write for each listed element, so an inverse lookup costs one array read.

## Main definitions

* {lit}`inverseEntries` — write each listed element at its position in a table.
* {lit}`inverseTable` — the table of the listed elements, every other entry empty.

## Main statements

* {lit}`inverseEntries_get` — the writes record each listed element at its position.
* {lit}`inverseTable_get` — the table holds each listed element at its position.

## Tags

embedding, inverse, array, table
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {β : Type*} {size : ℕ}

/-- Write each listed element at its position under the embedding. -/
def inverseEntries (e : β ↪ Fin size) (ps : List β) (table : Vector (Option β) size) :
    Vector (Option β) size :=
  ps.foldl (fun table p ↦ table.set (e p) (some p)) table

/-- Later writes keep an element's entry: a write at its position is a write of itself. -/
theorem inverseEntries_keep (e : β ↪ Fin size) (ps : List β) {table : Vector (Option β) size}
    {p : β} (h : table[e p] = some p) : (inverseEntries e ps table)[e p] = some p := by
  refine List.rec (motive := fun ps ↦ ∀ table : Vector (Option β) size,
      table[e p] = some p → (inverseEntries e ps table)[e p] = some p) (fun _ h ↦ h)
    (fun q qs ih table h ↦ ?_) ps table h
  change (inverseEntries e qs (table.set (e q) (some q)))[e p] = _
  apply ih
  rw [Fin.getElem_fin, Vector.getElem_set]
  split
  · rename_i hq
    rw [e.injective (Fin.ext hq)]
  · exact h

/-- Filling inverse entries records every listed element at its position. -/
theorem inverseEntries_get (e : β ↪ Fin size) {ps : List β} (table : Vector (Option β) size)
    {p : β} (hp : p ∈ ps) : (inverseEntries e ps table)[e p] = some p := by
  refine List.rec (motive := fun ps ↦ p ∈ ps → ∀ table : Vector (Option β) size,
      (inverseEntries e ps table)[e p] = some p) (fun h ↦ (List.not_mem_nil h).elim)
    (fun q qs ih hp table ↦ ?_) ps hp table
  change (inverseEntries e qs (table.set (e q) (some q)))[e p] = _
  rcases List.mem_cons.mp hp with hpq | hp
  · subst q
    apply inverseEntries_keep
    rw [Fin.getElem_fin, Vector.getElem_set_self]
  · exact ih hp _

/-- The inverse table of an embedding on the listed elements, every other entry empty. -/
def inverseTable (e : β ↪ Fin size) (ps : List β) : Vector (Option β) size :=
  inverseEntries e ps (Vector.replicate size none)

/-- The inverse table holds each listed element at its position under the embedding. -/
theorem inverseTable_get (e : β ↪ Fin size) {ps : List β} {p : β} (hp : p ∈ ps) :
    (inverseTable e ps)[e p] = some p :=
  inverseEntries_get e _ hp

end Geb.InteractionNet

end
