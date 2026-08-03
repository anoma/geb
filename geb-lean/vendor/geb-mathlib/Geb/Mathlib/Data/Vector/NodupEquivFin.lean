/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.List.NodupEquivFin
public import Geb.Mathlib.Data.Vector.OfFn
public import Mathlib.Data.Fin.SuccPred

/-!
# Choice-free inversion of an injective vector

The operation inverts an injective `ι : Vector (Fin n) k` — the
vector, not a function `Fin k → Fin n`, since morphisms of
`FinSetSkel` are vectors. The hypothesis is stated over `ι.get`, the
application-normal form, rather than over `ι.toList.Nodup`;
`List.nodup_iff_injective_get` relates the two.

This module targets mathlib rather than Lean core or Batteries: its
statement is an `Equiv`, which exists in neither.

## Main definitions

* `Vector.invOfInjective` — the inverse of an injective vector.

## Main statements

* `Vector.invOfInjective_apply` — the inverse's forward direction is
  the vector's lookup.

## Tags

vector, injective, equiv, choice-free
-/

@[expose] public section

namespace Vector

/-- An injective vector corresponds to the set of its entries. -/
def invOfInjective {n k : ℕ} (ι : Vector (Fin n) k)
    (h : Function.Injective ι.get) :
    Fin k ≃ {j : Fin n // j ∈ ι.toList} :=
  have hlen : ι.toList.length = k := by simp only [Vector.length_toList]
  have hnd : ι.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b hab
    have ha : (a : ℕ) < k := lt_of_lt_of_eq a.isLt hlen
    have hb : (b : ℕ) < k := lt_of_lt_of_eq b.isLt hlen
    have key : ι.get ⟨a, ha⟩ = ι.get ⟨b, hb⟩ := by
      simpa [Vector.get_eq_getElem, Vector.getElem_toList,
        List.get_eq_getElem] using hab
    exact Fin.ext (congrArg (Fin.val (n := k)) (h key))
  (finCongr hlen.symm).trans (List.Nodup.getEquivC _ hnd)

/-- The inversion of an injective vector recovers the vector's
lookup. -/
theorem invOfInjective_apply {n k : ℕ} (ι : Vector (Fin n) k)
    (h : Function.Injective ι.get) (i : Fin k) :
    ((invOfInjective ι h) i).val = ι.get i := rfl

end Vector
