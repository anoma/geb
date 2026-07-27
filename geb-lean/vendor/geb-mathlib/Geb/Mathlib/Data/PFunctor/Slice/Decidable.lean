/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Geb.Mathlib.Data.FinEnum

/-!
# Decidability of the slice functor's fiber and compatibility predicates

`SliceDomPFunctor.DirectionOver` / `SlicePFunctor.ShapeOver` are equalities
against a base or output index, decidable given decidable equality on that
index. A quantifier over the directions of a shape lying over an index is
decidable given `PFunctor.Finitary`, via `FinEnum.decidableForallSubtype`.
`SliceDomPFunctor.Compatible` is, by definition, an equality of functions out
of the (finitary) direction type, decidable via `FinEnum.decidablePiFinEnum`.
`SlicePFunctor.WValid` is decidable via a `WType.elim` fold computing
admissibility alongside the root index in a single pass.

## Main definitions

* `SliceDomPFunctor.decidableDirectionOver` — decidability of
  `DirectionOver`.
* `SlicePFunctor.decidableShapeOver` — decidability of `ShapeOver`.
* `SliceDomPFunctor.decidableForallDirection` — decidability of a
  quantifier over the directions of a shape lying over an index.
* `SliceDomPFunctor.decidableCompatible` — decidability of `Compatible`.
* `SlicePFunctor.wValidData` — the `WType.elim` fold computing a tree's
  root index and admissibility together.
* `SlicePFunctor.decidableWValid` — decidability of `WValid`.

## Tags

polynomial functor, slice category, decidability, FinEnum
-/

public section

universe uA uB uD uC uI uX

namespace SliceDomPFunctor

/-- Whether a direction lies over a given base index is decidable when
the base has decidable equality. No finiteness is needed. -/
instance decidableDirectionOver {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [DecidableEq dom] (a : F.A) (i : dom) : DecidablePred (F.DirectionOver a i) :=
  fun b ↦ decidable_of_iff (F.rCurried a b = i) Iff.rfl

/-- A quantifier over the directions of shape `a` lying over `i` is
decidable. Stated at `Direction` rather than left to
`FinEnum.decidableForallSubtype`: `Direction` is a `def`, and instance
resolution does not unfold it to a `Subtype`. -/
instance decidableForallDirection {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] (a : F.A) (i : dom)
    {q : F.Direction a i → Prop} [DecidablePred q] : Decidable (∀ b, q b) :=
  inferInstanceAs (Decidable (∀ b : Subtype (F.DirectionOver a i), q b))

/-- Compatibility of a direction assignment with a projection is
decidable: `Compatible p a v` is by definition the function equality
`p ∘ v = F.r ∘ Sigma.mk a` out of the finite direction type, decided by
`FinEnum.decidablePiFinEnum`. -/
instance decidableCompatible {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] {X : Type uX} (p : X → dom)
    (a : F.A) (v : F.B a → X) : Decidable (F.Compatible p a v) :=
  decidable_of_iff (p ∘ v = F.r ∘ Sigma.mk a) Iff.rfl

end SliceDomPFunctor

namespace SlicePFunctor

/-- Whether a shape lies over a given output index is decidable when the
codomain has decidable equality. -/
instance decidableShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) [DecidableEq cod] (j : cod) :
    DecidablePred (F.ShapeOver j) :=
  fun a ↦ decidable_of_iff (F.q a = j) Iff.rfl

/-- The algebra of the `WValid` fold: a node's index is its shape's
output index, and it is admitted when every child is admitted and the
children's index family equals the direction-input map. The `Bool`
analogue of `wIndexStep`. -/
@[expose] def wValidStep {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] :
    F.toPFunctor.Obj (I × Bool) → I × Bool :=
  fun x ↦ (F.q x.1,
    decide (∀ b, (x.2 b).2 = true) && decide (∀ b, (x.2 b).1 = F.rCurried x.1 b))

/-- The `WValid` fold: index and admissibility computed together, by a
single `WType.elim` at the carrier `I × Bool`. The index must be carried
even though it is non-recursive, because the step sees the children's
results and never the children. -/
@[expose] def wValidData {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] : F.toPFunctor.W → I × Bool :=
  WType.elim (I × Bool) (F.wValidStep)

/-- The admissibility component of the fold. -/
@[expose] def wValidBool {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] : F.toPFunctor.W → Bool :=
  fun w ↦ (F.wValidData w).2

/-- The index component of the fold is the root index. -/
@[simp] theorem wValidData_fst {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    (F.wValidData w).1 = F.wIndexRoot w := by
  cases w with
  | mk a f => rfl

/-- `wValidBool` decides admissibility. -/
theorem wValidBool_eq_true_iff {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    F.wValidBool w = true ↔ F.WValid w :=
  WType.rec (motive := fun w ↦ F.wValidBool w = true ↔ F.WValid w)
    (fun a f ih ↦ by
      beta_reduce
      rw [F.wValid_mk a f]
      change ((decide (∀ b, F.wValidBool (f b) = true)) &&
        decide (∀ b, (F.wValidData (f b)).1 = F.rCurried a b)) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      refine and_congr (forall_congr' ih) ?_
      exact ⟨fun h ↦ funext fun b ↦ (F.wValidData_fst (f b)).symm.trans (h b),
        fun h b ↦ (F.wValidData_fst (f b)).trans (congrFun h b)⟩)
    w

/-- Admissibility of a slice W-tree is decidable. -/
instance decidableWValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    Decidable (F.WValid w) :=
  decidable_of_iff _ (F.wValidBool_eq_true_iff w)

end SlicePFunctor
