/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Skeletal

/-!
# `FinSetSkel` compared with mathlib's skeleton

`FinSetSkel` and `FintypeCat.Skeleton` are the same category
presented differently: the comparison functors are mutually inverse on
the nose, giving an isomorphism in `Cat` rather than merely an
equivalence.

This module is allowlisted for `Classical.choice`, which
`CategoryTheory.Cat.category` depends on: an isomorphism in `Cat` is
an `Iso` with respect to that instance, so its type carries the
dependence however it is constructed. The comparison functors
themselves are choice-free; the taint enters the composite identities
through `CategoryTheory.Functor.comp` in their statements. Everything
pointwise is in `FinSetSkel.Basic`, so this module packages rather
than argues.

The isomorphism is closed by `CategoryTheory.Functor.hext`, which
takes object equality together with `HEq` of the morphism components.
`Functor.ext` does not close it: its `h_map` obligation retains
`eqToHom` applied to `(F ⋙ G).obj X = (𝟭 _).obj X`, on which
`eqToHom_refl` cannot fire. Write `Functor.ext` qualified — under
`open CategoryTheory` a bare `Functor.ext` resolves to the
`LawfulFunctor` lemma and errors with a message mentioning `f <$> x`.
`Functor.hext` is unambiguous, there being no `_root_.Functor.hext`,
and is written qualified only for symmetry.

## Main definitions

* `FinSetSkel.toSkeleton`, `FinSetSkel.ofSkeleton` — the comparison
  functors.
* `FinSetSkel.catIso` — the isomorphism in `Cat`.
* `FinSetSkel.skeletonEquivalence` — the equivalence, defined as
  `Cat.equivOfIso` of the isomorphism so that a reader arriving at the
  weaker statement is led to the stronger one.
* `FinSetSkel.incl` — the inclusion into `FintypeCat`.

## Main statements

* `FinSetSkel.skeletal` — isomorphic objects are equal.
* `FinSetSkel.isSkeleton` — `FinSetSkel` is a skeleton of
  `FintypeCat`.

## Implementation notes

`FinSetSkel` is not an instantiation of `FintypeCat.Skeleton` because it
cannot be. mathlib's `SmallCategory Skeleton` instance fixes
`Hom X Y := ULift (Fin X.len) → ULift (Fin Y.len)`, and instance search
selects one `Category` structure per type, so a category with the same
objects and vector morphisms is a distinct type rather than a
re-instantiation. The representation is what makes the constructions
decidable: mathlib's finite limits and colimits on `FintypeCat` are
layered over `noncomputable` constructions, so nothing transported along
the equivalence computes. Measured at v4.33.0-rc1.

## Tags

category, skeleton, equivalence
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

/-- The comparison functor to mathlib's skeleton. -/
def toSkeleton : FinSetSkel.{u} ⥤ FintypeCat.Skeleton.{u} where
  obj X := FintypeCat.Skeleton.mk X.len
  map f := toIdxFun f
  map_id X := funext fun i ↦ congrArg ULift.up (id_get X i.down)
  map_comp f g := funext fun i ↦ congrArg ULift.up (comp_get f g i.down)

/-- The comparison functor from mathlib's skeleton. -/
def ofSkeleton : FintypeCat.Skeleton.{u} ⥤ FinSetSkel.{u} where
  obj X := ⟨X.len⟩
  map {X Y} g := ofIdxFun (X := ⟨X.len⟩) (Y := ⟨Y.len⟩) g
  map_id X := hom_ext fun i ↦ by rw [ofIdxFun_get, id_get]; rfl
  map_comp f g := hom_ext fun i ↦ by
    rw [ofIdxFun_get, comp_get, ofIdxFun_get, ofIdxFun_get]; rfl

/-- The comparison functors compose to the identity on `FinSetSkel`. -/
theorem toSkeleton_comp_ofSkeleton :
    toSkeleton.{u} ⋙ ofSkeleton.{u} = Functor.id _ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦
    heq_of_eq (ofIdxFun_toIdxFun f)

/-- The comparison functors compose to the identity on mathlib's
skeleton. -/
theorem ofSkeleton_comp_toSkeleton :
    ofSkeleton.{u} ⋙ toSkeleton.{u} = Functor.id _ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun X Y f ↦
    heq_of_eq (toIdxFun_ofIdxFun (X := ⟨X.len⟩) (Y := ⟨Y.len⟩) f)

/-- `FinSetSkel` and mathlib's skeleton are isomorphic in `Cat`. -/
def catIso : Cat.of FinSetSkel.{u} ≅ Cat.of FintypeCat.Skeleton.{u} where
  hom := toSkeleton.toCatHom
  inv := ofSkeleton.toCatHom
  hom_inv_id := Cat.ext (by
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    exact toSkeleton_comp_ofSkeleton)
  inv_hom_id := Cat.ext (by
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    exact ofSkeleton_comp_toSkeleton)

/-- The equivalence, derived from the isomorphism. -/
def skeletonEquivalence : FinSetSkel.{u} ≌ FintypeCat.Skeleton.{u} :=
  Cat.equivOfIso catIso

/-- The comparison functor is an equivalence, being half of an
isomorphism in `Cat`. -/
instance toSkeleton_isEquivalence : toSkeleton.{u}.IsEquivalence :=
  skeletonEquivalence.isEquivalence_functor

/-- The inclusion of `FinSetSkel` into `FintypeCat`. -/
def incl : FinSetSkel.{u} ⥤ FintypeCat.{u} :=
  toSkeleton ⋙ FintypeCat.Skeleton.incl

/-- The inclusion is an equivalence, `IsSkeletonOf`'s `eqv` field
requiring it. -/
instance incl_isEquivalence : incl.{u}.IsEquivalence := by
  unfold incl; infer_instance

/-- Isomorphic objects of `FinSetSkel` are equal. -/
theorem skeletal : Skeletal FinSetSkel.{u} := fun _ _ ⟨e⟩ ↦
  FinSetSkel.ext (congrArg FintypeCat.Skeleton.len
    (FintypeCat.Skeleton.is_skeletal ⟨toSkeleton.mapIso e⟩))

/-- `FinSetSkel` is a skeleton of `FintypeCat`. -/
theorem isSkeleton : IsSkeletonOf FintypeCat.{u} FinSetSkel.{u} incl where
  skel := skeletal

end FinSetSkel
