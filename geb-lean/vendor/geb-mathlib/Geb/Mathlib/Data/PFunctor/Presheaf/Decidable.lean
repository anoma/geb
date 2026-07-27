/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
public import Geb.Mathlib.Data.W.Basic

/-!
# Decidability of naturality and hereditary naturality

`PresheafDomPFunctorData.IsNatural` is a quantifier over the objects, the
hom-sets, and the directions of the index category, of an equality in a fiber
of the input presheaf. It is decidable when the functor is finitary, the index
category has finitely many objects and finite hom-sets, and the input
presheaf's values have decidable equality.

`PresheafPFunctor.IsHereditarilyNatural` extends the naturality condition to
every node of a slice W-tree. It is decided by a classless `Bool`-valued core
that carries every finiteness and decidability datum explicitly, enumerating
each node's raw directions with `FinEnum.toList` rather than synthesising a
`Decidable` instance through the `PresheafPFunctor` diamond.

## Main definitions

* `PresheafDomPFunctorData.decidableIsNatural` — decidability of `IsNatural`.
* `PresheafPFunctor.isHereditarilyNaturalBoolCore` — the classless `Bool`-valued
  hereditary-naturality checker.
* `PresheafPFunctor.decidableIsHereditarilyNatural` — decidability of
  `IsHereditarilyNatural`.

## Main statements

* `PresheafPFunctor.isHereditarilyNaturalBoolCore_eq_true_iff` — the core returns
  `true` exactly on hereditarily natural slice W-trees.

## Tags

polynomial functor, presheaf, naturality, decidability, FinEnum
-/

public section

open CategoryTheory

universe uI uA uB vI uZ

namespace PresheafDomPFunctorData

/-- Naturality of a direction assignment is decidable when the functor is
finitary, the index category has finitely many objects and finite
hom-sets, and the input presheaf's values have decidable equality. Its
subject is a slice object over `elemProj Z`, not a `PresheafDomPFunctorData.obj Z`:
the latter is the `IsNatural` subtype itself, on which the predicate
holds by projection. -/
instance decidableIsNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) {Z : Iᵒᵖ ⥤ Type uZ}
    [F.Finitary] [FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]
    [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toSliceDomPFunctor.Obj (elemProj Z)) : Decidable (F.IsNatural x) :=
  inferInstanceAs (Decidable (∀ ⦃i i' : I⦄ (f : i' ⟶ i)
    (b : F.toSliceDomPFunctor.Direction x.1.1 i),
      F.value x (F.directionRestr x.1.1 f b) = Z.map f.op (F.value x b)))

end PresheafDomPFunctorData

namespace PresheafPFunctor

/-- The root-only restriction of a raw W-tree along a morphism: restrict
the root shape and reindex the direction assignment. The underlying-tree
form of `wRestrTree`, stated on the admissibility subtype; the head-index
witness `hq` is retained because `objRestrElt` consumes it. -/
@[expose] def wRestrTreeRaw {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (w : F.toPFunctor.W) (hq : F.q (PFunctor.W.head w) = j) : WType F.toPFunctor.B :=
  match w, hq with
  | WType.mk a f, hq =>
      WType.mk (F.shapeRestr g ⟨a, hq⟩).1
        fun b' ↦ f (F.reindex g ⟨a, hq⟩ (i := F.rCurried _ b') ⟨b', rfl⟩).1

/-- The underlying tree of `wRestrTree` is `wRestrTreeRaw`. -/
theorem wRestrTree_val {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    (F.wRestrTree g z hq).1 = F.wRestrTreeRaw g z.1 hq := by
  obtain ⟨w, hw⟩ := z
  cases w with
  | mk a f => rfl

/-- Hereditary naturality as a `Bool`, classless. All finiteness and
decidability supplied explicitly; the raw directions of each node are
enumerated and filtered by an explicit equality test, so no typeclass
inference traverses the `PresheafPFunctor` diamond. -/
@[expose] def isHereditarilyNaturalBoolCore {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i' : I, FinEnum (i' ⟶ i))
    (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B)) :
    F.toPFunctor.W → Bool :=
  WType.para Bool fun x ↦
    ((feI.toList).all fun i ↦ (feI.toList).all fun i' ↦
      ((feHom i i').toList).all fun g ↦
        ((feB x.1).toList).all fun b' ↦
          match decI (F.rCurried x.1 b') i with
          | isFalse _ => true
          | isTrue hb =>
            match decI (F.q (PFunctor.W.head (x.2 b').1)) i with
            | isFalse _ => true
            | isTrue hq =>
              (decEqW (x.2 (F.directionRestr x.1 g ⟨b', hb⟩).1).1
                (F.wRestrTreeRaw g (x.2 b').1 hq)).decide)
    && ((feB x.1).toList).all fun b' ↦ (x.2 b').2

/-- `isHereditarilyNaturalBoolCore` decides hereditary naturality. -/
theorem isHereditarilyNaturalBoolCore_eq_true_iff {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i' : I, FinEnum (i' ⟶ i))
    (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B))
    (z : F.toSlicePFunctor.W) :
    F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1 = true ↔
      F.IsHereditarilyNatural z := by
  refine SlicePFunctor.W.induction
    (motive := fun z ↦ F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1 = true ↔
      F.IsHereditarilyNatural z)
    (fun x ih ↦ ?_) z
  beta_reduce
  rw [F.isHereditarilyNatural_mk x]
  simp only [SlicePFunctor.W.mk, isHereditarilyNaturalBoolCore, WType.para_mk]
  rw [Bool.and_eq_true]
  refine and_congr ?_ ?_
  · simp only [List.all_eq_true, FinEnum.mem_toList, forall_const]
    constructor
    · intro H i i' g b
      have hb : F.rCurried x.1.1 b.1 = i := b.2
      have hqval : F.q (PFunctor.W.head (x.1.2 b.1).1) = i :=
        (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.wIndex x.1.1 x.1.2).mp
          x.2 b.1).trans hb)
      have hthis := H i i' g b.1
      split at hthis
      · exact absurd hb (by assumption)
      · split at hthis
        · exact absurd hqval (by assumption)
        · simp only [decide_eq_true_iff] at hthis
          exact Subtype.ext (hthis.trans (F.wRestrTree_val g (x.1.2 b.1) hqval).symm)
    · intro H i i' g b'
      split
      · rfl
      · split
        · rfl
        · simp only [decide_eq_true_iff]
          exact (congrArg Subtype.val (H g ⟨b', by assumption⟩)).trans
            (F.wRestrTree_val g (x.1.2 b') _)
  · rw [List.all_eq_true]
    constructor
    · intro H b
      exact (ih b).mp (H b (FinEnum.mem_toList b))
    · intro H b' _
      exact (ih b').mpr (H b')

/-- Hereditary naturality of a slice W-tree is decidable. -/
instance decidableIsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    [F.Finitary] [FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]
    [DecidableEq F.A] (z : F.toSlicePFunctor.W) :
    Decidable (F.IsHereditarilyNatural z) :=
  decidable_of_iff _ (F.isHereditarilyNaturalBoolCore_eq_true_iff inferInstance inferInstance
    inferInstance inferInstance inferInstance z)

end PresheafPFunctor
