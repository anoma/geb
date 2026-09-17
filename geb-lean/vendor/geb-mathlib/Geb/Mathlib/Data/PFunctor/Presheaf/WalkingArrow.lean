/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic


set_option doc.verso true in
/-!
# Families over ordinary W-types from walking-arrow presheaves

A presheaf on the walking arrow {lit}`0 ⟶ 1`, represented by {lit}`Fin 2`, is a
map from its total space at {lit}`1` to its base at {lit}`0`. Suppose every direction
of a base-level shape of a {name}`PresheafPFunctor` lies at {lit}`0`. Then its base
component is an ordinary {name}`PFunctor`: it does not inspect the total space.
This is a specialization of the presheaf PRA formula in \[nLabParametricRightAdjoint\].
The total-level shapes and their arity reindexing retain the generality of the PRA data.

## Main definitions

* {lit}`BaseIndependent`: base shapes have only base directions.
* {lit}`basePFunctor`: the ordinary polynomial on base shapes and their directions.
* {lit}`baseObjEquiv`: identifies the base component of the functor with that polynomial.
* {lit}`baseWEquiv`: identifies the base of the presheaf W-type with mathlib's W-type.
* {lit}`DependentW`: the fibres of restriction, indexed by that ordinary W-type.

## Main statements

* {lit}`map_baseNode`: the base-component identification commutes with input morphisms.
* {lit}`baseWEquiv_mk`: the W-type identification preserves constructors.
* {lit}`index_mk`: computes the index of a dependent constructor as an ordinary W node.

## References

* \[nLabParametricRightAdjoint\]

## Tags

walking arrow, presheaf, parametric right adjoint, W-type, dependent type
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory

namespace PresheafPFunctor.WalkingArrow

universe uA uB uZ

variable (F : PresheafPFunctor.{0, 0, uA, uB, 0, 0} (Fin 2) (Fin 2))

/-- Base-level constructors recurse only on the base type. -/
def BaseIndependent : Prop :=
  ∀ (a : F.Shape 0) (b : F.B a.1), F.rCurried a.1 b = 0

/-- The polynomial whose shapes are the base shapes and whose directions are their fields. -/
def basePFunctor : PFunctor.{uA, uB} :=
  ⟨F.Shape 0, fun a ↦ F.B a.1⟩

variable {F} (hF : BaseIndependent F)

/-- A node of the ordinary base polynomial as a node of the presheaf functor. -/
def baseNode (Z : (Fin 2)ᵒᵖ ⥤ Type uZ) (x : (basePFunctor F).Obj (Z.obj ⟨0⟩)) :
    (F.objPresheaf Z).obj ⟨0⟩ :=
  ⟨⟨⟨⟨x.1.1, fun b ↦ ⟨0, x.2 b⟩⟩,
      (F.compatible_iff _ _ _).mpr (fun b ↦ (hF x.1 b).symm)⟩, by
    intro i i' g b
    have hi : i = 0 := b.2.symm.trans (hF x.1 b.1)
    subst i
    have hi' : i' = 0 := by have hg := g.down.down; apply Fin.ext; change i'.val = 0; omega
    subst i'
    have hg : g = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
    subst g
    rw [congrFun (F.isFunctorial.directionRestr_id x.1.1 0) b]
    exact (FunctorToTypes.map_id_apply Z _).symm⟩, x.1.2⟩

/-- The base component depends only on the base of the input presheaf. -/
def baseObjEquiv (Z : (Fin 2)ᵒᵖ ⥤ Type uZ) :
    (F.objPresheaf Z).obj ⟨0⟩ ≃ (basePFunctor F).Obj (Z.obj ⟨0⟩) where
  toFun x := ⟨⟨x.1.shape, x.2⟩, fun b ↦ F.value x.1.1 ⟨b, hF ⟨x.1.shape, x.2⟩ b⟩⟩
  invFun := baseNode hF Z
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    refine Sigma.ext rfl (heq_of_eq (funext fun b ↦ ?_))
    exact Sigma.ext
      (((F.compatible_iff _ _ _).mp x.1.1.2 b).trans (hF ⟨x.1.shape, x.2⟩ b)).symm
      (cast_heq _ _)
  right_inv x := rfl

/-- The base-component equivalence commutes with maps of input presheaves. -/
theorem map_baseNode {Z Z' : (Fin 2)ᵒᵖ ⥤ Type uZ} (α : NatTrans Z Z')
    (x : (basePFunctor F).Obj (Z.obj ⟨0⟩)) :
    (F.mapPresheaf α).app ⟨0⟩ (baseNode hF Z x) =
      baseNode hF Z' ((basePFunctor F).map (α.app ⟨0⟩) x) := rfl

/-- Embed an ordinary base tree into the presheaf W-type, using its constructor. -/
def ofBaseW : (basePFunctor F).W → F.W.obj ⟨0⟩ :=
  WType.elim _ (fun x ↦ W.mk (baseNode hF F.W x))

/-- The embedding preserves constructors. -/
theorem ofBaseW_mk (a : F.Shape 0) (f : F.B a.1 → (basePFunctor F).W) :
    ofBaseW hF (WType.mk a f) =
      W.mk (baseNode hF F.W ⟨a, fun b ↦ ofBaseW hF (f b)⟩) := rfl

/-- A fold carrier retaining a base tree precisely when its index is zero. -/
abbrev BaseValue := Σ i : Fin 2, i = 0 → (basePFunctor F).W

/-- The slice algebra for reading the base tree; independence supplies every child index. -/
def readBaseStep (x : F.toSliceDomPFunctor.Obj
    (Sigma.fst : BaseValue (F := F) → Fin 2)) : BaseValue (F := F) :=
  ⟨F.q x.1.1, fun ha ↦ WType.mk ⟨x.1.1, ha⟩ (fun b ↦
    (x.1.2 b).2 (((F.compatible_iff _ _ _).mp x.2 b).trans (hF ⟨x.1.1, ha⟩ b)))⟩

/-- The index-preserving slice fold underlying the base-tree reader. -/
def readBase : F.toSlicePFunctor.W → BaseValue (F := F) :=
  SlicePFunctor.W.elim F.toSlicePFunctor _ Sigma.fst (readBaseStep hF) rfl

/-- The base reader preserves the slice index. -/
theorem readBase_index (w : F.toSlicePFunctor.W) :
    (readBase hF w).1 = F.toSlicePFunctor.wIndex w :=
  congrFun (SlicePFunctor.W.comp_elim F.toSlicePFunctor _ Sigma.fst (readBaseStep hF) rfl) w

/-- Read an ordinary base tree from a slice tree whose root is at the base. -/
def toBaseW (w : F.toSlicePFunctor.W) (hw : F.toSlicePFunctor.wIndex w = 0) :
    (basePFunctor F).W :=
  (readBase hF w).2 ((readBase_index hF w).trans hw)

/-- The reader's constructor equation on a base-indexed slice node. -/
theorem toBaseW_mk (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.wIndex)
    (hx : F.q x.1.1 = 0) :
    toBaseW hF (SlicePFunctor.W.mk x) hx = WType.mk (β := (basePFunctor F).B) ⟨x.1.1, hx⟩
      (fun b ↦ toBaseW hF (x.1.2 b)
        (((F.compatible_iff _ _ _).mp x.2 b).trans (hF ⟨x.1.1, hx⟩ b))) := rfl

/-- Reading an embedded base tree recovers the original ordinary W-tree. -/
theorem toBaseW_ofBaseW (w : (basePFunctor F).W) :
    toBaseW hF (ofBaseW hF w).down.1 (ofBaseW hF w).down.2.1 = w := by
  apply WType.rec (motive := fun w ↦
    toBaseW hF (ofBaseW hF w).down.1 (ofBaseW hF w).down.2.1 = w) _ w
  intro a f ih
  change WType.mk a (fun b ↦
    toBaseW hF (ofBaseW hF (f b)).down.1 (ofBaseW hF (f b)).down.2.1) = WType.mk a f
  rw [funext ih]

/-- Embedding the read base tree recovers the underlying slice tree. -/
theorem ofBaseW_toBaseW_val (w : F.toSlicePFunctor.W)
    (hw : F.toSlicePFunctor.wIndex w = 0) :
    (ofBaseW hF (toBaseW hF w hw)).down.1.1 = w.1 := by
  apply SlicePFunctor.W.induction (motive := fun w ↦
    ∀ hw : F.toSlicePFunctor.wIndex w = 0,
      (ofBaseW hF (toBaseW hF w hw)).down.1.1 = w.1) _ w hw
  intro x ih hx
  change WType.mk x.1.1 (fun b ↦
    (ofBaseW hF (toBaseW hF (x.1.2 b)
      (((F.compatible_iff _ _ _).mp x.2 b).trans (hF ⟨x.1.1, hx⟩ b)))).down.1.1) =
    WType.mk x.1.1 (fun b ↦ (x.1.2 b).1)
  congr 1
  funext b
  exact ih b _

/-- The base of the presheaf W-type is equivalent to mathlib's ordinary W-type. -/
def baseWEquiv : F.W.obj ⟨0⟩ ≃ (basePFunctor F).W where
  toFun w := toBaseW hF w.down.1 w.down.2.1
  invFun := ofBaseW hF
  left_inv w := by
    apply ULift.ext
    apply Subtype.ext
    apply Subtype.ext
    exact ofBaseW_toBaseW_val hF w.down.1 w.down.2.1
  right_inv := toBaseW_ofBaseW hF

/-- The base equivalence preserves the polynomial constructor. -/
theorem baseWEquiv_mk (x : (F.objPresheaf F.W).obj ⟨0⟩) :
    baseWEquiv hF (W.mk x) =
      PFunctor.W.mk ((basePFunctor F).map (baseWEquiv hF) (baseObjEquiv hF F.W x)) := by
  obtain ⟨x, rfl⟩ := (baseObjEquiv hF F.W).symm.surjective x
  rfl

/-- Restriction of a constructor is the constructor on the restricted node. -/
theorem map_mk {i j : Fin 2} (g : i ⟶ j) (x : (F.objPresheaf F.W).obj ⟨j⟩) :
    F.W.map g.op (W.mk x) = W.mk ((F.objPresheaf F.W).map g.op x) := by
  apply ULift.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The index of a total-space tree, obtained by restriction to the ordinary base W-type. -/
def index (w : F.W.obj ⟨1⟩) : (basePFunctor F).W :=
  baseWEquiv hF (F.W.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)).op w)

/-- The dependent constructor's index is computed by the ordinary polynomial constructor. -/
theorem index_mk (x : (F.objPresheaf F.W).obj ⟨1⟩) :
    index hF (W.mk x) = PFunctor.W.mk ((basePFunctor F).map (baseWEquiv hF)
      (baseObjEquiv hF F.W
        ((F.objPresheaf F.W).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)).op x))) := by
  rw [index, map_mk, baseWEquiv_mk]

/-- The dependent W-family over the ordinary base W-type. -/
def DependentW (w : (basePFunctor F).W) : Type (max uA uB) :=
  { t : F.W.obj ⟨1⟩ // index hF t = w }

/-- Every total-space tree gives an element of the family at its computed index. -/
def dependentMk (x : (F.objPresheaf F.W).obj ⟨1⟩) :
    DependentW hF (PFunctor.W.mk ((basePFunctor F).map (baseWEquiv hF)
      (baseObjEquiv hF F.W
        ((F.objPresheaf F.W).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)).op x)))) :=
  ⟨W.mk x, index_mk hF x⟩

/-- The total space of the dependent family recovers the presheaf W-type's total space. -/
def totalEquiv : (Σ w, DependentW hF w) ≃ F.W.obj ⟨1⟩ where
  toFun x := x.2.1
  invFun t := ⟨index hF t, t, rfl⟩
  left_inv := fun ⟨w, t, ht⟩ ↦ by cases ht; rfl
  right_inv _ := rfl

end PresheafPFunctor.WalkingArrow
