/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Batteries.Data.UnionFind

/-!
# A size-indexed union-find and the fold over a list of edges

`Batteries.UnionFind` ties its size to its representation, so an index
into it has type `Fin self.size` and every operation that changes the
structure changes the index type. `Sized n` fixes the size as a
subtype, so the indices are `Fin n` throughout and no cast is needed
to pass one operation's index to the next. `Sized.ofEdges` folds
`Sized.union` over a list of pairs, and the two theorems about it are
the two directions of correctness: every listed pair is merged, and
nothing beyond the listed pairs is.

## Main definitions

* `Batteries.UnionFind.Sized` — a union-find of a fixed size.
* `Batteries.UnionFind.Sized.discrete`,
  `Batteries.UnionFind.Sized.union`,
  `Batteries.UnionFind.Sized.root` — the operations, at `Fin n`.
* `Batteries.UnionFind.Sized.ofEdges` — the fold over a list of
  pairs.

## Main statements

* `Batteries.UnionFind.Sized.root_ofEdges_eq_of_mem` — every listed
  pair is merged.
* `Batteries.UnionFind.Sized.apply_root_ofEdges` — nothing beyond the
  listed pairs is merged, in eliminator form.

## Implementation notes

The second is stated as an eliminator — any `h : Fin n → α` agreeing
on the listed pairs agrees on roots — rather than as a
characterisation of the merged relation as the equivalence closure of
the edges. The eliminator is what a coequalizer's factorisation law
instantiates directly.

This module does not extract to mathlib4, `Sized` being a wrapper over
a Batteries type, and it imports nothing outside core and Batteries.
Where such content belongs is `TODO.md` § Upstream destination of core-
and Batteries-targeted content.

## Tags

union-find, disjoint set, quotient, choice-free
-/

@[expose] public section

universe u

namespace Batteries.UnionFind

variable {n : Nat}

/-- `union` preserves the size. -/
theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size := by
  unfold union; simp [UnionFind.size]

/-- `push` adds one to the size. -/
theorem size_push (self : UnionFind) : self.push.size = self.size + 1 := by
  unfold push; simp [UnionFind.size]

/-- A union-find whose size is fixed, so that its indices are
`Fin n` and no operation changes their type. -/
def Sized (n : Nat) : Type := {u : UnionFind // u.size = n}

/-- The discrete partition on `n` elements: `n` `push`es onto the
empty structure. -/
def Sized.discrete (n : Nat) : Sized n :=
  Nat.rec (motive := fun m ↦ Sized m) ⟨.empty, rfl⟩
    (fun _ v ↦ ⟨v.1.push, by rw [size_push, v.2]⟩) n

/-- Merge the classes of two indices. -/
def Sized.union (v : Sized n) (x y : Fin n) : Sized n :=
  ⟨v.1.unionN x y v.2.symm, by obtain ⟨u, rfl⟩ := v; exact size_union u x y⟩

/-- The representative of an index's class, as an index. -/
def Sized.root (v : Sized n) (x : Fin n) : Fin n :=
  ⟨v.1.rootD x, by obtain ⟨u, rfl⟩ := v; exact UnionFind.rootD_lt.mpr x.isLt⟩

/-- The union-find obtained by merging every listed pair. -/
def Sized.ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n :=
  l.foldl (fun v p ↦ v.union p.1 p.2) (discrete n)

/-- Two indices have the same root exactly when they are equivalent. -/
theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b := Fin.ext_iff

/-- `Batteries.UnionFind.equiv_union` restated at `Sized.union`. The
`Nat` arguments match Batteries' `Equiv`; the `Fin n` arguments the
other lemmas pass are coerced. -/
theorem Sized.equiv_union {v : Sized n} {x y : Fin n} {a b : Nat} :
    (v.union x y).1.Equiv a b ↔
      v.1.Equiv a b ∨ v.1.Equiv a x ∧ v.1.Equiv y b
                    ∨ v.1.Equiv a y ∧ v.1.Equiv x b := by
  obtain ⟨u, rfl⟩ := v
  exact UnionFind.equiv_union

/-- Every index is its own root in the discrete partition. -/
theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x :=
  Nat.rec (motive := fun k ↦ (discrete k).1.rootD x = x)
    UnionFind.rootD_empty (fun _ ih ↦ (UnionFind.root_push).trans ih) m

/-- `Sized.rootD_discrete` at `Fin n`. -/
theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x :=
  Fin.ext (rootD_discrete n x)

/-- A root is its own root. -/
theorem Sized.root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x := Fin.ext UnionFind.rootD_rootD

/-- Equivalence in an accumulator survives the fold. -/
theorem Sized.equiv_foldl_of_equiv (l : List (Fin n × Fin n))
    (a b : Fin n) (v : Sized n) (hv : v.1.Equiv a b) :
    (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv
      a b :=
  List.rec (motive := fun (l : List (Fin n × Fin n)) ↦ ∀ (v : Sized n), v.1.Equiv a b →
      (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv a b)
    (fun _ hv ↦ hv)
    (fun p _ ih v hv ↦ ih (v.union p.1 p.2) (Sized.equiv_union.mpr (Or.inl hv)))
    l v hv

/-- A listed pair is equivalent after the fold, from any accumulator. -/
theorem Sized.equiv_foldl_of_mem (l : List (Fin n × Fin n))
    (a b : Fin n) (hab : (a, b) ∈ l) (v : Sized n) :
    (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv
      a b :=
  List.rec (motive := fun (l : List (Fin n × Fin n)) ↦ (a, b) ∈ l → ∀ (v : Sized n),
      (l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).1.Equiv a b)
    (fun hab ↦ absurd hab List.not_mem_nil)
    (fun p _ ih hab v ↦ by
      cases List.mem_cons.mp hab with
      | inl hp =>
        subst hp
        exact equiv_foldl_of_equiv _ a b (v.union a b)
          (Sized.equiv_union.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      | inr ht => exact ih ht (v.union p.1 p.2))
    l hab v

/-- A function agreeing on every listed pair, and on the accumulator's
roots, agrees on the roots after the fold. -/
theorem Sized.apply_root_foldl {α : Type u} {h : Fin n → α}
    (l : List (Fin n × Fin n)) (hl : ∀ p ∈ l, h p.1 = h p.2)
    (v : Sized n) (hv : ∀ x, h (v.root x) = h x) (x : Fin n) :
    h ((l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).root
      x) = h x :=
  List.rec (motive := fun (l : List (Fin n × Fin n)) ↦ (∀ p ∈ l, h p.1 = h p.2) →
      ∀ (v : Sized n), (∀ z, h (v.root z) = h z) →
      h ((l.foldl (fun (v : Sized n) (p : Fin n × Fin n) ↦ v.union p.1 p.2) v).root x) = h x)
    (fun _ _ hv ↦ hv x)
    (fun p _ ih hl v hv ↦ ih (fun q hq ↦ hl q (List.mem_cons_of_mem p hq))
      (v.union p.1 p.2) (fun z ↦ by
        have key : ∀ c d : Fin n, v.1.Equiv c d → h c = h d := fun c d hcd ↦
          ((hv c).symm.trans (congrArg h (root_eq_iff.mpr hcd))).trans (hv d)
        have hz : (v.union p.1 p.2).1.Equiv z ((v.union p.1 p.2).root z) :=
          UnionFind.rootD_rootD.symm
        cases Sized.equiv_union.mp hz with
        | inl hsame => exact (key _ _ hsame).symm
        | inr hcross =>
          cases hcross with
          | inl hfwd => exact ((key _ _ hfwd.1).trans
              ((hl p List.mem_cons_self).trans (key _ _ hfwd.2))).symm
          | inr hbwd => exact ((key _ _ hbwd.1).trans
              ((hl p List.mem_cons_self).symm.trans (key _ _ hbwd.2))).symm))
    l hl v hv

/-- Every listed pair is merged. -/
theorem Sized.root_ofEdges_eq_of_mem {l : List (Fin n × Fin n)}
    {a b : Fin n} (hab : (a, b) ∈ l) :
    (ofEdges n l).root a = (ofEdges n l).root b :=
  root_eq_iff.mpr (equiv_foldl_of_mem l a b hab (discrete n))

/-- Nothing beyond the listed pairs is merged: a function agreeing on
every listed pair agrees on roots. -/
theorem Sized.apply_root_ofEdges {α : Type u} {l : List (Fin n × Fin n)}
    {h : Fin n → α} (hl : ∀ p ∈ l, h p.1 = h p.2) (x : Fin n) :
    h ((ofEdges n l).root x) = h x :=
  apply_root_foldl l hl (discrete n) (fun z ↦ congrArg h (root_discrete z)) x

end Batteries.UnionFind
