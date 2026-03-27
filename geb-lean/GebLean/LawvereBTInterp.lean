import GebLean.LawvereBTQuot

/-!
# Interpretation of the Lawvere Theory into Type

Defines a functor from `LawvereBTQuotCat` (the
Lawvere theory of parameterized binary tree objects)
into `Type u` for an arbitrary universe `u`.

The interpretation `BTMor1.interpU` and its
computation lemmas for proj, leaf, and branch are
in `LawvereBT.lean`.  The fold computation lemma
(`interpU_fold`) is deferred pending resolution
of a transport issue in `polyFixChildAt`.

This file will contain:
- Soundness (btMorRel implies equal interpU)
- The functor LawvereBTQuotCat ⥤ Type u
- Faithfulness of the functor

These all depend on `interpU_fold`.
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## BT.fold computation lemmas -/

/-- `BT.fold` on `BT.leaf` returns the base
value. -/
theorem BT.fold_leaf {α : Type u}
    (b : α) (s : α → α → α) :
    BT.fold b s BT.leaf = b := by
  unfold BT.fold BT.leaf
    polyProdFreeMFoldAt
    polyFreeMapAt
  simp only [polyFreeM_pure_bind]
  unfold polyFreeMPure polyFreeCounitFoldAt
  rfl

/-- `BT.fold` on `BT.node` applies the step
function to the recursive results. -/
theorem BT.fold_node {α : Type u}
    (b : α) (s : α → α → α)
    (l r : BT.{u}) :
    BT.fold b s (BT.node l r) =
      s (BT.fold b s l)
        (BT.fold b s r) := by
  rfl

end GebLean
