/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Vector.OfFn

/-!
# Writing a list of index-value pairs into a vector

`Vector.scatter` writes a list of index-value pairs into a vector in
one left-to-right pass, each pair overwriting the entry at its index.
Repeated indices are allowed, the last pair carrying an index being
the one whose value survives, so the entry at an index is determined
by the pairs whenever they all carry the same value there.

## Main definitions

* `Vector.scatter` — the pass.

## Main statements

* `Vector.get_scatter_of_not_mem` — an index no pair carries keeps
  its entry.
* `Vector.get_scatter_of_mem` — an index carried with one value takes
  that value.

## Implementation notes

The determinacy condition covers a list of constant value and a list
of distinct indices alike, neither paying for the other's hypothesis.
Both lemmas quantify over the starting vector, so they apply part-way
through a pass as well as at its start.

## Tags

vector, scatter, fold, choice-free
-/

@[expose] public section

universe u

namespace Vector

/-- One pass writing each pair's value into the vector at the pair's
index. -/
def scatter {α : Type u} {n : Nat} (P : List (Fin n × α)) (v : Vector α n) :
    Vector α n :=
  P.foldl (fun w p ↦ w.set p.1.val p.2 p.1.isLt) v

/-- The pass leaves untouched every index no pair carries. -/
theorem get_scatter_of_not_mem {α : Type u} {n : Nat} (P : List (Fin n × α))
    (v : Vector α n) (j : Fin n) (hj : j ∉ P.map Prod.fst) :
    (scatter P v).get j = v.get j :=
  P.rec (motive := fun P ↦ ∀ (v : Vector α n), j ∉ P.map Prod.fst →
      (scatter P v).get j = v.get j)
    (fun _ _ ↦ rfl)
    (fun p P ih v hj ↦ by
      rw [List.map_cons, List.mem_cons, not_or] at hj
      refine (ih (v.set p.1.val p.2 p.1.isLt) hj.2).trans ?_
      simp only [get_eq_getElem]
      exact getElem_set_ne p.1.isLt j.isLt fun he ↦ hj.1 (Fin.ext he).symm)
    v hj

/-- The pass writes the value of a pair whose index no other pair
carries with a different value. -/
theorem get_scatter_of_mem {α : Type u} {n : Nat} (P : List (Fin n × α))
    (v : Vector α n) (j : Fin n) (a : α) (hm : (j, a) ∈ P)
    (hu : ∀ b, (j, b) ∈ P → b = a) : (scatter P v).get j = a :=
  P.rec (motive := fun P ↦ ∀ (v : Vector α n), (j, a) ∈ P →
      (∀ b, (j, b) ∈ P → b = a) → (scatter P v).get j = a)
    (fun _ hm _ ↦ absurd hm List.not_mem_nil)
    (fun p P ih v hm hu ↦ by
      by_cases hjP : j ∈ P.map Prod.fst
      · obtain ⟨q, hq, hqj⟩ := List.mem_map.mp hjP
        have hq' : (j, q.2) ∈ P := by rw [← hqj]; exact hq
        exact ih (v.set p.1.val p.2 p.1.isLt)
          (hu q.2 (List.mem_cons_of_mem p hq') ▸ hq')
          fun b hb ↦ hu b (List.mem_cons_of_mem p hb)
      · rcases List.mem_cons.mp hm with he | hmP
        · subst he
          refine (get_scatter_of_not_mem P (v.set j.val a j.isLt) j hjP).trans ?_
          simp only [get_eq_getElem]
          exact getElem_set_self j.isLt
        · exact absurd (List.mem_map_of_mem (f := Prod.fst) hmP) hjP)
    v hm hu

end Vector
