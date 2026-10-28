/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Finite enumeration of surviving cells

Selecting a decidable subset of an explicitly enumerated cell type gives an explicit
enumeration of the surviving cells. This supplies finite ordinal indices after deleting
an active pair. Reindexing a net by such an enumeration preserves its external boundary,
cell symbols and wire matching.

## Main definitions

* {lit}`PortNet.subtypeCells` — the ordered list of cells satisfying a predicate.
* {lit}`PortNet.subtypeEnum` — the corresponding finite enumeration.
* {lit}`PortNet.indexed` — give a net finite ordinal cell indices.

## Tags

interaction net, cell, finite enumeration, allocation, reindexing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

universe u v w

variable {C : Type u}

/-- Retain a cell together with evidence that it satisfies the selection predicate. -/
def selectCell (p : C → Prop) [DecidablePred p] (c : C) : Option {c // p c} :=
  if h : p c then some ⟨c, h⟩ else none

/-- A selected cell retains its original identity. -/
theorem selectCell_val (p : C → Prop) [DecidablePred p] {c : C} {d : {c // p c}}
    (h : d ∈ selectCell p c) : d.val = c := by
  unfold selectCell at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · cases h

/-- The ordered list of cells that satisfy a decidable predicate. -/
def subtypeCells [FinEnum C] (p : C → Prop) [DecidablePred p] : List {c // p c} :=
  (FinEnum.toList C).filterMap (selectCell p)

/-- Every selected cell occurs in the filtered enumeration. -/
theorem mem_subtypeCells [FinEnum C] (p : C → Prop) [DecidablePred p] (c : {c // p c}) :
    c ∈ subtypeCells p := by
  apply List.mem_filterMap.mpr
  refine ⟨c.val, FinEnum.mem_toList _, ?_⟩
  simp only [selectCell, dif_pos c.property]

/-- Filtering a cell enumeration introduces no duplicates. -/
theorem nodup_subtypeCells [FinEnum C] (p : C → Prop) [DecidablePred p] :
    (subtypeCells p).Nodup :=
  List.Nodup.filterMap (fun _ _ _ h h' ↦ (selectCell_val p h).symm.trans (selectCell_val p h'))
    FinEnum.nodup_toList

/-- An explicitly enumerable type has an explicit enumeration for every decidable subtype. -/
@[instance_reducible] def subtypeEnum [FinEnum C] (p : C → Prop) [DecidablePred p] :
    FinEnum {c // p c} where
  card := (subtypeCells p).length
  equiv :=
    { toFun := fun c ↦ ⟨(subtypeCells p).idxOf c,
        List.idxOf_lt_length_of_mem (mem_subtypeCells p c)⟩
      invFun := (subtypeCells p).get
      left_inv := fun c ↦ List.getElem_idxOf (List.idxOf_lt_length_of_mem (mem_subtypeCells p c))
      right_inv := fun i ↦ Fin.ext ((nodup_subtypeCells p).idxOf_getElem i.val i.isLt) }
  decEq := inferInstance

variable {α : Type v} {Γ : Type w} {arity : α → ℕ} {label : C → α}

/-- Reindex a finite net by its cell enumeration, keeping the external boundary fixed. -/
def indexed [FinEnum C] (n : PortNet arity label Γ) :
    PortNet arity (fun i : Fin (FinEnum.card C) ↦ label (FinEnum.equiv.symm i)) Γ :=
  ⟨n.wiring.map (endpointEquiv arity (Equiv.refl Γ) FinEnum.equiv
    (fun c ↦ congrArg label (Equiv.symm_apply_apply _ c))), n.loops⟩

/-- Finite ordinal indexing is a boundary-preserving net isomorphism. -/
def indexedIso [FinEnum C] (n : PortNet arity label Γ) : Iso n n.indexed where
  cells := FinEnum.equiv
  label_eq c := congrArg label (Equiv.symm_apply_apply _ c)
  wiring_eq := rfl
  loops_eq := rfl

end Geb.InteractionNet.PortNet

end
