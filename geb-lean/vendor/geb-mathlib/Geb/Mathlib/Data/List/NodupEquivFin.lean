/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual

/-!
# Choice-free inversion of a duplicate-free list

`List.Nodup.getEquiv` depends on `Classical.choice` through a single
ingredient, `List.idxOf_lt_length_iff`. Substituting
`List.idxOf_lt_length_of_mem`, which depends on `propext` alone,
rebuilds it choice-free. `Fin.compressEquiv` renumbers the indices
satisfying a `Bool`-valued predicate, which is what an equalizer or a
coequalizer carrier needs.

## Main definitions

* `List.Nodup.getEquivC` — the choice-free rebuild of
  `List.Nodup.getEquiv`.
* `Fin.compressEquiv` — the indices satisfying a predicate,
  renumbered.

## Tags

list, nodup, equiv, choice-free
-/

@[expose] public section

universe u

namespace List.Nodup

/-- Indices of a duplicate-free list correspond to its members.
Choice-free rebuild of `List.Nodup.getEquiv`. -/
def getEquivC {α : Type u} [DecidableEq α] (l : List α) (H : l.Nodup) :
    Fin l.length ≃ {x // x ∈ l} where
  toFun i := ⟨l.get i, List.get_mem _ _⟩
  invFun x := ⟨l.idxOf ↑x, List.idxOf_lt_length_of_mem x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by
    simp only [List.get_eq_getElem, List.getElem_idxOf, Subtype.coe_eta]

end List.Nodup

namespace Fin

/-- The indices of `Fin n` satisfying `p`, renumbered onto an initial
segment. -/
def compressEquiv {n : ℕ} (p : Fin n → Bool) :
    Fin ((List.finRange n).filter p).length ≃ {i : Fin n // p i} :=
  (List.Nodup.getEquivC _ ((List.nodup_finRange n).filter p)).trans
    (Equiv.subtypeEquivRight (fun x ↦ by
      simp only [List.mem_filter, List.mem_finRange, true_and]))

end Fin
