/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.OpenPair
public import Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Ranks of the cells remaining after a contraction

The cells of {lit}`Fin n` other than two cells {lit}`a` and {lit}`b`, in increasing order, are
enumerated by their ranks: a remaining cell's rank is its index less the number of the removed
cells below it, and the cell of a rank is that rank plus the number of removed cells at or below
it. Both are computed from the two removed cells alone, so that each costs a constant number of
comparisons, where an enumeration filtering the cells finds a rank by searching them.

## Main definitions

* {lit}`PortNet.remainingCard` — the number of cells other than the two removed.
* {lit}`PortNet.remainingRank` — the rank of a cell among those remaining.
* {lit}`PortNet.remainingUnrank` — the cell of a rank among those remaining.
* {lit}`PortNet.remainingEnum` — the enumeration of the remaining cells by their ranks.

## Main statements

* {lit}`PortNet.remainingUnrank_rank` and {lit}`PortNet.remainingRank_unrank` — the rank and
  the cell of a rank are inverse.

## Tags

interaction net, contraction, enumeration, rank
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

/-- The number of cells of {lit}`Fin n` other than {lit}`x` and {lit}`y`. -/
def remainingCard (n x y : ℕ) : ℕ := n - 1 - if x = y then 0 else 1

/-- The rank of a cell among the cells other than {lit}`x` and {lit}`y`: its index less the
number of those below it. -/
def remainingRank (x y c : ℕ) : ℕ :=
  c - (if x < c then 1 else 0) - (if x = y then 0 else if y < c then 1 else 0)

/-- The cell of a rank among the cells other than {lit}`x` and {lit}`y`: the rank plus the
number of those at or below the cell. -/
def remainingUnrank (x y i : ℕ) : ℕ :=
  if x = y then (if i < x then i else i + 1)
  else if i < (if x < y then x else y) then i
  else if i + 1 < (if x < y then y else x) then i + 1 else i + 2

/-- A remaining cell's rank is below the number of remaining cells. -/
theorem remainingRank_lt {n x y c : ℕ} (hc : c < n) (hx : x < n) (hy : y < n) (hcx : c ≠ x)
    (hcy : c ≠ y) : remainingRank x y c < remainingCard n x y := by
  unfold remainingRank remainingCard
  split_ifs <;> omega

/-- The cell of a rank below the number of remaining cells is a cell. -/
theorem remainingUnrank_lt {n x y i : ℕ} (hx : x < n) (hy : y < n)
    (hi : i < remainingCard n x y) : remainingUnrank x y i < n := by
  unfold remainingUnrank remainingCard at *
  split_ifs at * <;> omega

/-- The cell of a rank is not the first removed cell. -/
theorem remainingUnrank_ne_left (x y i : ℕ) : remainingUnrank x y i ≠ x := by
  unfold remainingUnrank
  split_ifs <;> omega

/-- The cell of a rank is not the second removed cell. -/
theorem remainingUnrank_ne_right (x y i : ℕ) : remainingUnrank x y i ≠ y := by
  unfold remainingUnrank
  split_ifs <;> omega

/-- The cell of a remaining cell's rank is that cell. -/
theorem remainingUnrank_rank {x y c : ℕ} (hcx : c ≠ x) (hcy : c ≠ y) :
    remainingUnrank x y (remainingRank x y c) = c := by
  unfold remainingUnrank remainingRank
  split_ifs <;> omega

/-- The rank of the cell of a rank is that rank. -/
theorem remainingRank_unrank (x y i : ℕ) : remainingRank x y (remainingUnrank x y i) = i := by
  unfold remainingUnrank remainingRank
  split_ifs <;> omega

variable {n : ℕ}

/-- The cells of {lit}`Fin n` other than {lit}`a` and {lit}`b`, enumerated in increasing order
by their ranks. -/
@[instance_reducible] def remainingEnum (a b : Fin n) : FinEnum (RemainingCell a b) where
  card := remainingCard n a b
  equiv :=
    { toFun c := ⟨remainingRank a b c.val, remainingRank_lt c.val.isLt a.isLt b.isLt
        (fun h ↦ c.property.1 (Fin.ext h)) (fun h ↦ c.property.2 (Fin.ext h))⟩
      invFun i := ⟨⟨remainingUnrank a b i, remainingUnrank_lt a.isLt b.isLt i.isLt⟩,
        fun h ↦ remainingUnrank_ne_left a b i (congrArg Fin.val h),
        fun h ↦ remainingUnrank_ne_right a b i (congrArg Fin.val h)⟩
      left_inv c := Subtype.ext (Fin.ext (remainingUnrank_rank
        (fun h ↦ c.property.1 (Fin.ext h)) (fun h ↦ c.property.2 (Fin.ext h))))
      right_inv i := Fin.ext (remainingRank_unrank a b i) }
  decEq := inferInstance

end Geb.InteractionNet.PortNet

end
