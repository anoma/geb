/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

/-!
# A choice-free `ofFn` for root `Vector`

Core builds `Vector.ofFn` on `Array.ofFn`, whose indexing lemmas
depend on `Classical.choice` through the private
`Array.getElem_ofFn_go`; the dependence reaches `Vector.getElem_ofFn`,
`Vector.ofFn_getElem`, `Vector.getElem_range` and
`Vector.getElem_finRange`. Routing the construction through
`List.ofFn` instead avoids it: every ingredient below is choice-free,
and the result is still array-backed, so indexing stays
constant-time.

Those four lemmas are therefore not to be used in a choice-free module,
and neither is the `Array` bridge beneath them. All four carry `@[simp]`,
and all but `Vector.ofFn_getElem` also `@[grind =]`, so a bare `simp` or
`grind` meeting such a term introduces `Classical.choice` without an
error. The constructions `Vector.range` and `Vector.finRange` are equally
unusable, each having only choice-dependent indexing lemmas, so the
restriction covers the constructions and not only their lemmas; the
constructions themselves depend on `propext` alone.

`ofFnC` is not related to `Vector.ofFn` by any choice-free equation —
the bridge would be `List.toArray_ofFn`, itself choice-dependent — so
the two coexist unrelated, and choice-free modules use this one.

`get_eq_getElem` restates Batteries'
`Batteries.Data.Vector.Lemmas.get_eq_getElem`, which is unreachable:
no `Mathlib.*` module imports that file, and the bare umbrella
`import Mathlib` that would reach it is forbidden in
upstream-eligible files. Importing Batteries directly is permitted but
declined, because it would bring the choice-tainted `@[simp]`
`Vector.get_ofFn` and `Vector.get_range` into scope.

## Main definitions

* `Vector.ofFnC` — the choice-free `ofFn`.

## Main statements

* `Vector.getElem_ofFnC`, `Vector.get_ofFnC`, `Vector.ofFnC_get` — the
  indexing lemma and the two round trips.
* `Vector.get_eq_getElem` — the bridge to the `getElem` API,
  deliberately not `simp`.

## Tags

vector, ofFn, choice-free
-/

@[expose] public section

universe u

namespace Vector

/-- A vector from an index function, built through `List.ofFn` so that
no `Classical.choice`-dependent lemma is needed to reason about it. -/
def ofFnC {α : Type u} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by rw [List.size_toArray, List.length_ofFn]⟩

/-- Indexing `ofFnC` at a `Nat` recovers the function. -/
theorem getElem_ofFnC {α : Type u} {n : Nat} (f : Fin n → α)
    (i : Nat) (h : i < n) : (ofFnC f)[i] = f ⟨i, h⟩ := by
  rw [ofFnC, getElem_mk, List.getElem_toArray, List.getElem_ofFn]

/-- The `Fin`-indexed accessor is the `Nat`-indexed one. Not `simp`:
the `get` form is the normal form, and marking this in either
orientation would rewrite it away. -/
theorem get_eq_getElem {α : Type u} {n : Nat} (v : Vector α n)
    (i : Fin n) : v.get i = v[(i : Nat)] := rfl

/-- Indexing `ofFnC` at a `Fin` recovers the function. -/
@[simp] theorem get_ofFnC {α : Type u} {n : Nat} (f : Fin n → α)
    (i : Fin n) : (ofFnC f).get i = f i := getElem_ofFnC f i.1 i.2

/-- `ofFnC` inverts indexing. -/
@[simp] theorem ofFnC_get {α : Type u} {n : Nat} (v : Vector α n) :
    ofFnC v.get = v :=
  Vector.ext fun i hi ↦ getElem_ofFnC _ i hi

end Vector
