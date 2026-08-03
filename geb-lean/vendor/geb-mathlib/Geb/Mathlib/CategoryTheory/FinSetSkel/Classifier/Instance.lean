/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Core
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Mono
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances
public import Mathlib.CategoryTheory.Topos.Classifier

/-!
# The subobject classifier of `FinSetSkel`

The mathlib packaging of `FinSetSkel.Classifier.chi` and its
universal property. The classifying object is the object of length 2,
`Ω₀` is the one-element terminal object, and `truth` picks the index
`1`; the characteristic morphism sends the members of a
monomorphism's image to `1`. This module and the module defining
`FinSetSkel.Classifier.chi` fix that orientation jointly, each
stating it.

## Main definitions

* `FinSetSkel.truth` — the truth morphism.
* `FinSetSkel.classifier` — the subobject classifier.

## Main statements

* `FinSetSkel.chi_iff_of_isPullback` — the fibre of a classifying
  morphism over `1` is the image of the monomorphism it classifies.

## Implementation notes

The derivation of the vector-level hypothesis of
`FinSetSkel.Classifier.chi_uniq` from `IsPullback` lives here rather
than in the choice-free layer, and it is content rather than
packaging: it uses the pullback's universal property and cannot be
stated choice-free.

`Ω₀` is the object `mk 1`, which the cartesian structure also takes
as its unit, so the classifier's `Ω₀` and the cartesian unit are the
same object and their comparison is an isomorphism between an object
and itself.

## References

* [Freyd1972], for the axiomatisation whose subobject classifier
  `FinSetSkel.classifier` supplies.

## Tags

finite sets, skeleton, subobject classifier, topos
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- The truth morphism: the point of the classifying object at
index `1`. -/
def truth : (mk 1 : FinSetSkel.{u}) ⟶ mk 2 := point 1

/-- The fibre of a classifying morphism over `1` is the image of the
monomorphism it classifies. -/
theorem chi_iff_of_isPullback {U X : FinSetSkel.{u}} (m : U ⟶ X)
    (χ' : X ⟶ mk 2)
    (hp : IsPullback m (isTerminalOne.from U) χ' truth) (j : Fin X.len) :
    χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList := by
  -- (←) the square commutes, and both of its legs are the constant `1`
  have hmpr : j ∈ m.toVec.toList → χ'.toVec.get j = 1 := by
    intro hj
    obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hj
    have hi : n < U.len := by simpa using hn
    have hj' : m.toVec.get ⟨n, hi⟩ = j := by
      rw [Vector.get_eq_getElem]
      simpa using hget
    have hw : (m ≫ χ').toVec.get ⟨n, hi⟩
        = (isTerminalOne.from U ≫ truth).toVec.get ⟨n, hi⟩ :=
      congrArg (fun k : U ⟶ mk 2 ↦ k.toVec.get ⟨n, hi⟩) hp.w
    rw [comp_get, comp_get, truth, point_get] at hw
    rw [← hj']
    exact hw
  -- (→) the point at `j` factors through the pullback
  have hmp : χ'.toVec.get j = 1 → j ∈ m.toVec.toList := by
    intro h
    have hw : point j ≫ χ' = isTerminalOne.from (mk 1) ≫ truth := by
      refine hom_ext fun _ ↦ ?_
      rw [comp_get, comp_get, point_get, truth, point_get]
      exact h
    obtain ⟨l, hl⟩ : ∃ l : (mk 1 : FinSetSkel.{u}) ⟶ U, l ≫ m = point j :=
      ⟨hp.lift (point j) (isTerminalOne.from (mk 1)) hw,
        hp.lift_fst (point j) (isTerminalOne.from (mk 1)) hw⟩
    have hg : m.toVec.get (l.toVec.get 0) = j := by
      rw [← comp_get, hl, point_get]
    rw [← hg]
    simp [Vector.get_eq_getElem]
  exact ⟨hmp, hmpr⟩

/-- The subobject classifier of `FinSetSkel`. -/
def classifier : CategoryTheory.Classifier FinSetSkel.{u} :=
  CategoryTheory.Classifier.mkOfTerminalΩ₀ (mk 1) isTerminalOne (mk 2) truth
    (fun m ↦ Classifier.chi m)
    (fun m _ ↦ by
      have hinj : Function.Injective m.toVec.get := mono_iff_injective.mp ‹Mono m›
      -- the square: both legs are the constant `1` on the image of `m`
      have hsq : CommSq m (isTerminalOne.from _) (Classifier.chi m) truth :=
        ⟨hom_ext fun i ↦ by
          rw [comp_get, comp_get, truth, point_get]
          exact Classifier.chi_get_image_eq_one m i⟩
      -- membership of a competing cone's left leg, from its own commutation
      have hmem : ∀ (s : PullbackCone (Classifier.chi m) truth) (t : Fin s.pt.len),
          s.fst.toVec.get t ∈ m.toVec.toList := fun s t ↦
        (Classifier.chiVec_get_eq_one_iff m _).mp (by
          have hc : (s.fst ≫ Classifier.chi m).toVec.get t
              = (s.snd ≫ truth).toVec.get t :=
            congrArg (fun k : s.pt ⟶ mk 2 ↦ k.toVec.get t) s.condition
          rw [comp_get, comp_get, Classifier.chi_get] at hc
          exact hc.trans (point_get 1 _))
      exact IsPullback.of_isLimit' hsq
        (PullbackCone.isLimitAux _
          (fun s ↦ Classifier.pullbackLift m hinj s.fst (hmem s))
          (fun s ↦ Classifier.pullbackLift_comp m hinj s.fst (hmem s))
          (fun _ ↦ (toOne_uniq _).trans (toOne_uniq _).symm)
          (fun s n hn ↦
            Classifier.pullbackLift_uniq m hinj s.fst (hmem s) n
              (hn WalkingCospan.left))))
    (fun m _ χ' hp ↦ Classifier.chi_uniq m χ' (chi_iff_of_isPullback m χ' hp))

end FinSetSkel
