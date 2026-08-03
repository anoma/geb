/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Data.Vector.NodupEquivFin
public import Geb.Mathlib.Data.Vector.OfFn
public import Geb.Mathlib.Data.Vector.Scatter

/-!
# The subobject classifier of `FinSetSkel`, over vectors

The classifying object is the object of length 2 and the
characteristic morphism of a monomorphism sends the members of its
image to `1` and everything else to `0`. `FinSetSkel.truth` picks the
index `1`, and this module and the module defining it fix that
orientation jointly, each stating it.

## Main definitions

* `FinSetSkel.Classifier.chi` — the characteristic morphism.
* `FinSetSkel.Classifier.pullbackLift` — the factorisation through a
  monomorphism of a morphism whose image it contains.

## Main statements

* `FinSetSkel.Classifier.chiVec_get_eq_one_iff` — the characteristic
  vector is the indicator of the image.
* `FinSetSkel.Classifier.chi_get_image_eq_one` — the characteristic
  morphism sends the image to `1`.
* `FinSetSkel.Classifier.chi_uniq` — a morphism with the same
  indicator is the characteristic morphism.

## Implementation notes

The orientation follows mathlib's own: `finTwoEquiv` is
`fun i ↦ i == 1`, and `Presheaf.truth` and `Sheaf.truth`, the truth
morphisms of the two subobject classifiers mathlib builds,
`Presheaf.classifier` and `Sheaf.classifier`, both pick the maximal
sieve. With `truth = 1` the characteristic morphism is the indicator
of membership and every bridge to `Bool`, `decide` or `Prop` is
`finTwoEquiv` composed with nothing; with `truth = 0` each such
bridge carries a negation and the normal forms on the two sides stop
matching.

The characteristic vector is scattered in one pass over a
`Vector.replicate`, not written index-by-index over a membership
test, which would rebuild and rescan the image per index.

## Tags

finite sets, skeleton, subobject classifier, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel.Classifier

variable {U X : FinSetSkel.{u}}

/-- The characteristic vector of `m`: `1` on its image, `0`
elsewhere. `m` is not assumed monic; monicity is what makes the
vector classify a subobject. -/
def chiVec (m : U ⟶ X) : Vector (Fin 2) X.len :=
  Vector.scatter (m.toVec.toList.map (fun j ↦ (j, 1))) (Vector.replicate X.len (0 : Fin 2))

/-- The characteristic morphism of `m`, whose vector is
`FinSetSkel.Classifier.chiVec m`. It classifies the image of `m` as a
subobject when `m` is monic. -/
def chi (m : U ⟶ X) : X ⟶ mk 2 := Hom.ofVec (chiVec m)

/-- The characteristic morphism looks up the characteristic
vector. -/
@[simp] theorem chi_get (m : U ⟶ X) (j : Fin X.len) :
    (chi m).toVec.get j = (chiVec m).get j := by
  rw [chi, Hom.toVec_ofVec]

/-- The characteristic vector is the indicator of the image. -/
theorem chiVec_get_eq_one_iff (m : U ⟶ X) (j : Fin X.len) :
    (chiVec m).get j = 1 ↔ j ∈ m.toVec.toList := by
  constructor
  · intro h
    by_cases hj : j ∈ m.toVec.toList
    · exact hj
    · rw [chiVec, Vector.get_scatter_of_not_mem _ _ _ (by simpa using hj),
        Vector.get_eq_getElem, Vector.getElem_replicate] at h
      exact absurd h (by decide)
  · exact fun hj ↦ Vector.get_scatter_of_mem _ _ _ _ (List.mem_map_of_mem hj)
      fun b hb ↦ by obtain ⟨_, _, hx⟩ := List.mem_map.mp hb; exact (congrArg Prod.snd hx).symm

/-- The factorisation through a monomorphism of a morphism whose
image it contains. -/
def pullbackLift (m : U ⟶ X) (hm : Function.Injective m.toVec.get)
    {Z : FinSetSkel.{u}} (z : Z ⟶ X)
    (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) : Z ⟶ U :=
  let e := Vector.invOfInjective m.toVec hm
  Hom.ofVec (Vector.ofFnC fun t ↦ e.symm ⟨z.toVec.get t, hz t⟩)

/-- The factorisation composes back to the original morphism. -/
theorem pullbackLift_comp (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) :
    pullbackLift m hm z hz ≫ m = z :=
  hom_ext fun t ↦ by
    simp only [comp_get, pullbackLift, Hom.toVec_ofVec, Vector.get_ofFnC]
    rw [← Vector.invOfInjective_apply m.toVec hm, Equiv.apply_symm_apply]

/-- The factorisation through a monomorphism is unique. -/
theorem pullbackLift_uniq (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList)
    (n : Z ⟶ U) (hn : n ≫ m = z) : n = pullbackLift m hm z hz :=
  hom_ext fun t ↦ hm (by
    have h : (n ≫ m).toVec.get t = (pullbackLift m hm z hz ≫ m).toVec.get t := by
      rw [hn, pullbackLift_comp]
    simpa only [comp_get] using h)

/-- The characteristic morphism is `1` on the image. -/
theorem chi_get_image_eq_one (m : U ⟶ X) (i : Fin U.len) :
    (chi m).toVec.get (m.toVec.get i) = 1 := by
  rw [chi_get]
  exact (chiVec_get_eq_one_iff m _).mpr (by simp [Vector.get_eq_getElem])

/-- A morphism whose fibre over `1` is the image is the
characteristic morphism. -/
theorem chi_uniq (m : U ⟶ X) (χ' : X ⟶ mk 2)
    (h : ∀ j, χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList) :
    χ' = chi m :=
  hom_ext fun j ↦ by
    rw [chi_get]
    by_cases hj : χ'.toVec.get j = 1
    · rw [hj]
      exact ((chiVec_get_eq_one_iff m j).mpr ((h j).mp hj)).symm
    · have h1 : (chiVec m).get j ≠ 1 :=
        fun hc ↦ hj ((h j).mpr ((chiVec_get_eq_one_iff m j).mp hc))
      -- neither is `1`, so in `Fin 2` both are `0`
      have h2 : (χ'.toVec.get j).val ≠ 1 := fun hc ↦ hj (Fin.val_injective hc)
      have h3 : ((chiVec m).get j).val ≠ 1 := fun hc ↦ h1 (Fin.val_injective hc)
      have h4 : (χ'.toVec.get j).val < 2 := (χ'.toVec.get j).isLt
      have h5 : ((chiVec m).get j).val < 2 := ((chiVec m).get j).isLt
      exact Fin.val_injective (by omega)

end FinSetSkel.Classifier
