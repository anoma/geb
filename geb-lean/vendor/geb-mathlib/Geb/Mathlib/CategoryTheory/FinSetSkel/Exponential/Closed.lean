/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Core
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# `FinSetSkel` is monoidal closed

The monoidal packaging of `FinSetSkel.expEquivIdx` and
`FinSetSkel.expEquivHom` as a `MonoidalClosed` structure.

## Main definitions

* `FinSetSkel.expHomEquiv` — the exponential's hom-level
  equivalence, in the form the adjunction consumes.
* `FinSetSkel.monoidalClosed` — the monoidal closed structure.

## Main statements

* `FinSetSkel.whiskerLeft_get` — the action of left whiskering on
  indices.
* `FinSetSkel.expHomEquiv_naturality` — naturality of that
  equivalence in the parameter.

## Implementation notes

`Closed X` has exactly the two fields `rightAdj` and `adj`, and
`MonoidalClosed C` exactly the one field `closed`, so
`Adjunction.rightAdjointOfEquiv` and
`Adjunction.adjunctionOfEquivRight` supply the functor, the unit, the
counit and the triangle identities, and none is constructed by hand.

`X ⊗ Z` is the object of length `X.len * Z.len` on the nose, the
monoidal structure having come from
`CartesianMonoidalCategory.ofChosenFiniteProducts` fed with the
chosen binary product cones, so restating the equivalence at
`X ⊗ Z ⟶ Y` transports along a definitional equality rather than a
comparison isomorphism.

The whiskering bridge is what connects the carrier-level naturality
of `FinSetSkel.expEquivIdx_naturality` to `F.map f`: left whiskering
acts on indices by pairing the first component with the whiskered
morphism's action on the second. It is stated here rather than
alongside the carrier-level equivalence because `◁` elaborates
through the `CartesianMonoidalCategory` instance, which depends on
`Classical.choice`.

## References

* [Freyd1972], for the axiomatisation whose cartesian-closure axiom
  `FinSetSkel.monoidalClosed` discharges.

## Tags

finite sets, skeleton, exponential, monoidal closed
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace FinSetSkel

/-- Left whiskering acts on indices by pairing the first component
with the whiskered morphism's action on the second. -/
theorem whiskerLeft_get (X : FinSetSkel.{u}) {Y Z : FinSetSkel.{u}}
    (f : Y ⟶ Z) (i : Fin (X ⊗ Y).len) :
    (X ◁ f).toVec.get i =
      Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i)) := by
  have h : (X ◁ f) = prodLift (prodFst X Y) (prodSnd X Y ≫ f) :=
    prodLift_uniq _ _ _
      (CartesianMonoidalCategory.whiskerLeft_fst X f)
      (CartesianMonoidalCategory.whiskerLeft_snd X f)
  have h' : ∀ j : Fin (prodObj X Y).len,
      (prodLift (prodFst X Y) (prodSnd X Y ≫ f)).toVec.get j =
        Fin.pairC (Fin.divNatC j) (f.toVec.get (Fin.modNatC j)) := fun j ↦ by
    rw [prodLift_get, comp_get, prodFst_get, prodSnd_get]
  rw [h]
  exact h' i

/-- The exponential's hom-level equivalence, in the form
`adjunctionOfEquivRight` consumes. -/
def expHomEquiv (X : FinSetSkel.{u}) (Z Y : FinSetSkel.{u}) :
    ((tensorLeft X).obj Z ⟶ Y) ≃ (Z ⟶ mk (Y.len ^ X.len)) :=
  expEquivHom X.len Z.len Y.len

/-- Naturality of the exponential's equivalence, in the form
`Adjunction.adjunctionOfEquivRight` consumes. -/
theorem expHomEquiv_naturality (X : FinSetSkel.{u})
    (Z' Z Y : FinSetSkel.{u}) (f : Z' ⟶ Z) (g : (tensorLeft X).obj Z ⟶ Y) :
    expHomEquiv X Z' Y ((tensorLeft X).map f ≫ g) =
      f ≫ expHomEquiv X Z Y g := by
  -- The statement over the length-indexed objects, where the rewrites
  -- of `expEquivHom` match syntactically.
  have key : ∀ (g' : (mk (X.len * Z.len) : FinSetSkel.{u}) ⟶ mk Y.len)
      (h : (mk (X.len * Z'.len) : FinSetSkel.{u}) ⟶ mk Y.len),
      (∀ i, h.toVec.get i =
          g'.toVec.get (Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i)))) →
      expEquivHom X.len Z'.len Y.len h = f ≫ expEquivHom X.len Z.len Y.len g' := by
    intro g' h hh
    have harg : homEquivIdxFun (mk (X.len * Z'.len)) (mk Y.len) h =
        fun i ↦ (homEquivIdxFun (mk (X.len * Z.len)) (mk Y.len) g')
          (Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i))) := funext hh
    refine hom_ext fun t ↦ ?_
    simp only [expEquivHom, Equiv.trans_apply, harg]
    rw [homEquivIdxFun_symm_get, comp_get, homEquivIdxFun_symm_get]
    exact congrFun (expEquivIdx_naturality X.len Z'.len Z.len Y.len f.toVec.get
      (homEquivIdxFun (mk (X.len * Z.len)) (mk Y.len) g')) t
  -- The whiskered composite, at the tensor spelling `whiskerLeft_get` matches.
  have hten : ∀ i : Fin (X ⊗ Z').len,
      (X ◁ f ≫ g).toVec.get i =
        g.toVec.get (Fin.pairC (Fin.divNatC i) (f.toVec.get (Fin.modNatC i))) :=
    fun i ↦ by rw [comp_get, whiskerLeft_get]; rfl
  exact key g (X ◁ f ≫ g) fun i ↦ hten i

/-- `FinSetSkel` is monoidal closed: the exponential of the object of
length `X.len` into the object of length `Y.len` is the object of
length `Y.len ^ X.len`. -/
instance monoidalClosed : MonoidalClosed FinSetSkel.{u} where
  closed X :=
    { rightAdj :=
        Adjunction.rightAdjointOfEquiv (expHomEquiv X) (expHomEquiv_naturality X)
      adj :=
        Adjunction.adjunctionOfEquivRight (expHomEquiv X)
          (expHomEquiv_naturality X) }

end FinSetSkel
