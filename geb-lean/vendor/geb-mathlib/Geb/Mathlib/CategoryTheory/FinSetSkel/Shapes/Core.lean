/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Data.Fin.Basic
public import Geb.Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The initial and terminal objects, coproducts and products of `FinSetSkel`

The constructions of the initial and terminal objects, the binary
coproducts and the binary products over `Fin` and vectors, together
with the content of their universal properties, stated in the
application-normal form `f.toVec.get i`. The mathlib cones and `Prop`
instances built from them are in
`FinSetSkel.cartesianMonoidalCategory` and its neighbours; this
module is choice-free.

## Main definitions

* `FinSetSkel.homEquivIdxFun` — morphisms as index functions.
* `FinSetSkel.point` — the morphism out of the one-element object
  picking a given index.
* `FinSetSkel.fromZero`, `FinSetSkel.toOne` — the canonical
  morphisms out of the empty and into the one-element object.
* `FinSetSkel.coprodObj`, `FinSetSkel.coprodInl`,
  `FinSetSkel.coprodInr`, `FinSetSkel.coprodDesc` — binary
  coproducts.
* `FinSetSkel.prodObj`, `FinSetSkel.prodFst`, `FinSetSkel.prodSnd`,
  `FinSetSkel.prodLift` — binary products.

## Main statements

* `FinSetSkel.fromZero_uniq`, `FinSetSkel.toOne_uniq` — initiality
  and terminality.
* `FinSetSkel.coprodInl_desc`, `FinSetSkel.coprodInr_desc`,
  `FinSetSkel.coprodDesc_uniq` — the coproduct's universal property.
* `FinSetSkel.prodLift_fst`, `FinSetSkel.prodLift_snd`,
  `FinSetSkel.prodLift_uniq` — the product's universal property.

## Implementation notes

`FinSetSkel.ofIdxFun` and `FinSetSkel.toIdxFun` state the
correspondence between morphisms and index functions over
`ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)`, not as an `Equiv`
and not over bare index functions. `FinSetSkel.homEquivIdxFun`
packages the two round trips and removes both `ULift`s, so that a
universal property stated over index functions can be transported to
one over morphisms. Its domain transport is `Equiv.arrowCongrLeftC`;
mathlib's `Equiv.arrowCongr` and the `Equiv.piCongrLeft` family all
depend on `Classical.choice`.

## Tags

finite sets, skeleton, coproduct, product, terminal, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

variable {X Y : FinSetSkel.{u}}

/-- Morphisms as lifted index functions: `FinSetSkel.ofIdxFun` and
`FinSetSkel.toIdxFun` as an equivalence. -/
def homEquivIdxFunU (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) where
  toFun := toIdxFun
  invFun := ofIdxFun
  left_inv := ofIdxFun_toIdxFun
  right_inv := toIdxFun_ofIdxFun

/-- Morphisms as index functions. -/
def homEquivIdxFun (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (Fin X.len → Fin Y.len) :=
  (homEquivIdxFunU X Y).trans
    ((Equiv.arrowCongrLeftC Equiv.ulift).trans
      (Equiv.piCongrRight fun _ ↦ Equiv.ulift))

/-- The index function of a morphism is its normal-form lookup. -/
@[simp] theorem homEquivIdxFun_apply (f : X ⟶ Y) (i : Fin X.len) :
    homEquivIdxFun X Y f i = f.toVec.get i := rfl

/-- The morphism of an index function looks up by that function. -/
@[simp] theorem homEquivIdxFun_symm_get
    (g : Fin X.len → Fin Y.len) (i : Fin X.len) :
    ((homEquivIdxFun X Y).symm g).toVec.get i = g i := by
  simp [homEquivIdxFun, homEquivIdxFunU, ofIdxFun_get, Equiv.arrowCongrLeftC]

/-- The unique morphism out of the empty object. -/
def fromZero (Y : FinSetSkel.{u}) : mk 0 ⟶ Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ i.elim0)

/-- Any morphism out of the empty object is the canonical one. -/
theorem fromZero_uniq {Y : FinSetSkel.{u}} (f : mk 0 ⟶ Y) :
    f = fromZero Y :=
  hom_ext fun i ↦ i.elim0

/-- The unique morphism into the one-element object. -/
def toOne (X : FinSetSkel.{u}) : X ⟶ mk 1 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- Any morphism into the one-element object is the canonical one. -/
theorem toOne_uniq {X : FinSetSkel.{u}} (f : X ⟶ mk 1) :
    f = toOne X :=
  hom_ext fun _ ↦ Subsingleton.elim _ _

/-- The morphism out of the one-element object picking an index. -/
def point {X : FinSetSkel.{u}} (i : Fin X.len) : mk 1 ⟶ X :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ i)

/-- A point looks up the index it picks. -/
@[simp] theorem point_get {X : FinSetSkel.{u}} (i : Fin X.len)
    (t : Fin (mk 1 : FinSetSkel.{u}).len) : (point i).toVec.get t = i := by
  simp [point]

/-- The binary coproduct object: lengths add. Reducible, so that
`Fin (coprodObj X Y).len` and `Fin (X.len + Y.len)` are interchangeable
at reducible transparency: `finSumFinEquiv`'s index types are stated in
the second form and the objects of this category in the first, and a
term mixing them is type-correct only up to delta, which `rw`'s motive
check rejects. -/
abbrev coprodObj (X Y : FinSetSkel.{u}) : FinSetSkel.{u} :=
  mk (X.len + Y.len)

/-- The left injection into the binary coproduct. -/
def coprodInl (X Y : FinSetSkel.{u}) : X ⟶ coprodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ finSumFinEquiv (Sum.inl i))

/-- The right injection into the binary coproduct. -/
def coprodInr (X Y : FinSetSkel.{u}) : Y ⟶ coprodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ finSumFinEquiv (Sum.inr i))

/-- The left injection acts by the left summand embedding. -/
@[simp] theorem coprodInl_get (X Y : FinSetSkel.{u}) (i : Fin X.len) :
    (coprodInl X Y).toVec.get i = finSumFinEquiv (Sum.inl i) := by
  rw [coprodInl, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- The right injection acts by the right summand embedding. -/
@[simp] theorem coprodInr_get (X Y : FinSetSkel.{u}) (i : Fin Y.len) :
    (coprodInr X Y).toVec.get i = finSumFinEquiv (Sum.inr i) := by
  rw [coprodInr, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- The morphism out of a binary coproduct determined by its two
components. -/
def coprodDesc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    coprodObj X Y ⟶ Z :=
  Hom.ofVec (Vector.ofFnC fun i ↦
    Sum.elim (fun a ↦ f.toVec.get a) (fun b ↦ g.toVec.get b)
      (finSumFinEquiv.symm i))

/-- The descent morphism acts by case analysis on the summand. -/
@[simp] theorem coprodDesc_get {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (i : Fin (coprodObj X Y).len) :
    (coprodDesc f g).toVec.get i =
      Sum.elim (fun a ↦ f.toVec.get a) (fun b ↦ g.toVec.get b)
        (finSumFinEquiv.symm i) := by
  rw [coprodDesc, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- Descent restricted along the left injection is its left
component. -/
@[simp] theorem coprodInl_desc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) : coprodInl X Y ≫ coprodDesc f g = f :=
  hom_ext fun i ↦ by
    rw [comp_get, coprodInl_get, coprodDesc_get, Equiv.symm_apply_apply,
      Sum.elim_inl]

/-- Descent restricted along the right injection is its right
component. -/
@[simp] theorem coprodInr_desc {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) : coprodInr X Y ≫ coprodDesc f g = g :=
  hom_ext fun i ↦ by
    rw [comp_get, coprodInr_get, coprodDesc_get, Equiv.symm_apply_apply,
      Sum.elim_inr]

/-- A morphism agreeing with both components on the injections is
the descent morphism. -/
theorem coprodDesc_uniq {X Y Z : FinSetSkel.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (m : coprodObj X Y ⟶ Z)
    (hl : coprodInl X Y ≫ m = f) (hr : coprodInr X Y ≫ m = g) :
    m = coprodDesc f g :=
  hom_ext fun i ↦ by
    rcases hs : finSumFinEquiv.symm i with a | b
    · have : i = finSumFinEquiv (Sum.inl a) := by
        rw [← hs, Equiv.apply_symm_apply]
      subst this
      rw [coprodDesc_get, Equiv.symm_apply_apply, Sum.elim_inl, ← hl, comp_get,
        coprodInl_get]
    · have : i = finSumFinEquiv (Sum.inr b) := by
        rw [← hs, Equiv.apply_symm_apply]
      subst this
      rw [coprodDesc_get, Equiv.symm_apply_apply, Sum.elim_inr, ← hr, comp_get,
        coprodInr_get]

/-- The binary product object: lengths multiply. Reducible for the
reason recorded at `coprodObj`. -/
abbrev prodObj (X Y : FinSetSkel.{u}) : FinSetSkel.{u} :=
  mk (X.len * Y.len)

/-- The first projection of the binary product. -/
def prodFst (X Y : FinSetSkel.{u}) : prodObj X Y ⟶ X :=
  Hom.ofVec (Vector.ofFnC Fin.divNatC)

/-- The second projection of the binary product. -/
def prodSnd (X Y : FinSetSkel.{u}) : prodObj X Y ⟶ Y :=
  Hom.ofVec (Vector.ofFnC Fin.modNatC)

/-- The morphism into a binary product determined by its two
components. -/
def prodLift {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ prodObj X Y :=
  Hom.ofVec (Vector.ofFnC fun t ↦ Fin.pairC (f.toVec.get t) (g.toVec.get t))

/-- The first projection acts by the quotient. -/
@[simp] theorem prodFst_get (X Y : FinSetSkel.{u})
    (i : Fin (prodObj X Y).len) :
    (prodFst X Y).toVec.get i = Fin.divNatC i := by
  rw [prodFst, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- The second projection acts by the remainder. -/
@[simp] theorem prodSnd_get (X Y : FinSetSkel.{u})
    (i : Fin (prodObj X Y).len) :
    (prodSnd X Y).toVec.get i = Fin.modNatC i := by
  rw [prodSnd, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- The lift acts by pairing its components' lookups. -/
@[simp] theorem prodLift_get {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) (t : Fin Z.len) :
    (prodLift f g).toVec.get t =
      Fin.pairC (f.toVec.get t) (g.toVec.get t) := by
  rw [prodLift, Hom.toVec_ofVec]
  exact Vector.get_ofFnC _ _

/-- The lift followed by the first projection is its first
component. -/
@[simp] theorem prodLift_fst {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) : prodLift f g ≫ prodFst X Y = f :=
  hom_ext fun t ↦ by
    rw [comp_get, prodLift_get, prodFst_get, Fin.divNatC_pairC]

/-- The lift followed by the second projection is its second
component. -/
@[simp] theorem prodLift_snd {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) : prodLift f g ≫ prodSnd X Y = g :=
  hom_ext fun t ↦ by
    rw [comp_get, prodLift_get, prodSnd_get, Fin.modNatC_pairC]

/-- A morphism agreeing with both components on the projections is
the lift. -/
theorem prodLift_uniq {X Y Z : FinSetSkel.{u}} (f : Z ⟶ X)
    (g : Z ⟶ Y) (m : Z ⟶ prodObj X Y)
    (hf : m ≫ prodFst X Y = f) (hg : m ≫ prodSnd X Y = g) :
    m = prodLift f g :=
  hom_ext fun t ↦ by
    rw [prodLift_get, ← hf, ← hg, comp_get, comp_get, prodFst_get,
      prodSnd_get, Fin.pairC_divNatC_modNatC]

end FinSetSkel
