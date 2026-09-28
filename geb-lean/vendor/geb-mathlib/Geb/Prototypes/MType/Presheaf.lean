/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.MType.Slice
public import Geb.Mathlib.Data.PFunctor.Presheaf.Carrier

set_option doc.verso true in
/-!
# M-types of presheaf polynomial functors

For a presheaf polynomial endofunctor {lit}`F : PresheafPFunctor I I`, the
M-type is obtained from the M-type of the underlying slice endofunctor
({name}`Geb.MType.SliceM`), as its W-type ({name}`PresheafPFunctor.W`) is
obtained from the underlying slice W-type: both are the carrier presheaf
({name}`PresheafPFunctor.carrier`) of a fixed point of the slice endofunctor
with its hereditarily natural trees. The carrier presheaf's fibre over
{lit}`j` is the hereditarily natural trees indexed at {lit}`j`, its restriction
maps restrict the root of a tree along a morphism, and its constructor and
destructor are natural and mutually inverse, all stated once over the fixed
point.

What is particular to M-types is hereditary naturality, and the corecursor. A
tree is hereditarily natural when every node reached through children is
natural ({name}`PresheafPFunctor.NodeNatural`): for W-types an inductive fold,
here {lit}`PresheafM.IsHereditarilyNatural` is its coinductive form
({name}`Geb.MType.Hereditary`). The corecursor from a presheaf coalgebra
{lit}`(Y, α)` is the corecursor of the slice coalgebra {lit}`α` induces on the
total space of {lit}`Y`. Its image is hereditarily natural by coinduction, and
it is natural by a one-level argument ({lit}`PresheafM.sliceCorec_map`): the
corecursion from a restricted element and the restriction of the corecursion
are built from the same node, by the naturality of {lit}`α`. It is a morphism
of coalgebras and the only one, by the uniqueness of the slice corecursor, so
the carrier is the terminal coalgebra. The coalgebras are those of the
endofunctor {name}`PresheafPFunctor.objPresheaf` of presheaves valued in
{lit}`Type (max uI uA uB)`, the universe of the carrier: a structure map
{lit}`Y ⟶ objPresheaf Y` needs {lit}`Y` and {lit}`objPresheaf Y` in one
category, as the eliminator of {name}`PresheafPFunctor.W` needs its algebras
in that universe.

## Main definitions

* {lit}`PresheafM.IsHereditarilyNatural` — hereditary naturality of the trees
  of the slice M-type, coinductively.
* {lit}`PresheafM.hereditaryNaturality` — its unfolding equation.
* {lit}`PresheafM` — the carrier presheaf.
* {lit}`PresheafM.corec` — the corecursor from a presheaf coalgebra.

## Main statements

* {lit}`PresheafM.sliceCorec_map` — the underlying corecursion commutes with
  restriction.
* {lit}`PresheafM.dest_corec` — the corecursor is a morphism of coalgebras.
* {lit}`PresheafM.corec_unique` — it is the only one.

## References

* \[Weber2007\]
* \[GambinoKock2013\]
* \[VanDenBergDeMarchi2007\], Section 2.

## Tags

M-type, terminal coalgebra, polynomial functor, presheaf, parametric right
adjoint, naturality, coinduction
-/
set_option doc.verso true

@[expose] public section

open CategoryTheory PresheafPFunctor

universe uI uA uB vI

namespace Geb.MType

variable {I : Type uI} [Category.{vI} I] (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)

namespace PresheafM

/-- Hereditary naturality of the trees of the slice M-type: every node reached
through children is natural. The coinductive form, by
{name}`Geb.MType.Hereditary`, of {name}`PresheafPFunctor.NodeNatural`. -/
def IsHereditarilyNatural : SliceM F.toSlicePFunctor → Prop :=
  Hereditary (Q := F.toPFunctor) (fun z ↦ z.dest.1)
    (F.NodeNatural (SliceM.fixedPoint F.toSlicePFunctor) ∘ SliceM.dest)

/-- Hereditary naturality unfolded one level. -/
theorem isHereditarilyNatural_iff (z : SliceM F.toSlicePFunctor) :
    IsHereditarilyNatural F z ↔
      F.NodeNatural (SliceM.fixedPoint F.toSlicePFunctor) z.dest ∧
        ∀ b, IsHereditarilyNatural F (z.dest.1.2 b) := by
  unfold IsHereditarilyNatural
  exact hereditary_iff _ _ z

/-- Hereditary naturality of the trees of the slice M-type satisfies the
unfolding equation of {name}`PresheafPFunctor.HereditaryNaturality`.
Reducible, so that the carrier presheaf's fibres show
{name}`IsHereditarilyNatural`. -/
@[reducible] def hereditaryNaturality :
    F.HereditaryNaturality (SliceM.fixedPoint F.toSlicePFunctor) where
  holds := IsHereditarilyNatural F
  holds_iff := isHereditarilyNatural_iff F

end PresheafM

/-- The carrier presheaf of the M-type of {lit}`F`: the carrier presheaf
({name}`PresheafPFunctor.carrier`) of the slice M-type with its hereditarily
natural trees. -/
def PresheafM : Iᵒᵖ ⥤ Type (max uI uA uB) :=
  F.carrier (PresheafM.hereditaryNaturality F)

namespace PresheafM

section Corec

variable (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans Y (F.objPresheaf Y))

/-- The slice coalgebra underlying the presheaf coalgebra {lit}`α`, on the
total space of {lit}`Y`: an element over {lit}`i` goes to the node
{lit}`α` gives it. -/
def sliceStep (e : Σ i : I, Y.obj ⟨i⟩) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Y) :=
  (α.app ⟨e.1⟩ e.2).1.1

/-- The underlying slice coalgebra lies over {lit}`I`. -/
theorem obj_sliceStep :
    F.toSlicePFunctor.obj (PresheafDomPFunctorData.elemProj Y) ∘ sliceStep F Y α =
      PresheafDomPFunctorData.elemProj Y :=
  funext fun e ↦ (α.app ⟨e.1⟩ e.2).2

/-- The corecursion of the underlying slice coalgebra. -/
def sliceCorec : (Σ i : I, Y.obj ⟨i⟩) → SliceM F.toSlicePFunctor :=
  SliceM.corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)

/-- The underlying corecursion from an element over {lit}`i` is indexed at
{lit}`i`. -/
theorem index_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    SliceM.index F.toSlicePFunctor (sliceCorec F Y α e) = e.1 :=
  congrFun (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)) e

/-- The destructor of the underlying corecursion. -/
theorem dest_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    (sliceCorec F Y α e).dest = F.toSliceDomPFunctor.map (sliceCorec F Y α)
      (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α))
      (sliceStep F Y α e) :=
  SliceM.dest_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α) e

/-- The node {lit}`α` gives a restricted element is the restriction of the
node it gives the element: the naturality of {lit}`α`. -/
theorem sliceStep_map ⦃i i' : I⦄ (f : i' ⟶ i) (y : Y.obj ⟨i⟩) :
    sliceStep F Y α ⟨i', Y.map f.op y⟩ =
      F.objRestrElt f (sliceStep F Y α ⟨i, y⟩) (α.app ⟨i⟩ y).2 := by
  have h : α.app ⟨i'⟩ (Y.map f.op y) = (F.objPresheaf Y).map f.op (α.app ⟨i⟩ y) :=
    FunctorToTypes.naturality _ _ α f.op y
  exact congrArg (fun w : (F.objPresheaf Y).obj ⟨i'⟩ ↦ w.1.1) h

/-- The underlying corecursion from a restricted element is the root
restriction of the corecursion from the element. A one-level argument: both
are constructed from the same node, by the naturality of {lit}`α` and because
mapping children commutes with reindexing them. -/
theorem sliceCorec_map ⦃i i' : I⦄ (f : i' ⟶ i) (y : Y.obj ⟨i⟩) :
    sliceCorec F Y α ⟨i', Y.map f.op y⟩ =
      F.restrTree (SliceM.fixedPoint F.toSlicePFunctor) f (sliceCorec F Y α ⟨i, y⟩)
        (index_sliceCorec F Y α ⟨i, y⟩) := by
  refine (SliceM.mk_dest _).symm.trans (congrArg SliceM.mk ?_)
  refine (dest_sliceCorec F Y α _).trans ?_
  rw [sliceStep_map]
  exact F.objRestrElt_congr f (dest_sliceCorec F Y α ⟨i, y⟩).symm _ _

/-- Mapping the children of a natural node by the underlying corecursion gives
a natural node of trees. -/
theorem nodeNatural_map_sliceCorec (x : F.toPresheafDomPFunctorData.obj Y) :
    F.NodeNatural (SliceM.fixedPoint F.toSlicePFunctor) (F.toSliceDomPFunctor.map
      (sliceCorec F Y α)
      (SliceM.comp_corec F.toSlicePFunctor _ (sliceStep F Y α) (obj_sliceStep F Y α)) x.1) := by
  intro i i' g b
  change sliceCorec F Y α (x.1.1.2 (F.directionRestr x.1.1.1 g b).1) =
    F.restrTree (SliceM.fixedPoint F.toSlicePFunctor) g (sliceCorec F Y α (x.1.1.2 b.1)) _
  rw [F.snd_eq_value x.1 (F.directionRestr x.1.1.1 g b), x.2 g b, sliceCorec_map]
  exact F.restrTree_congr _ g (congrArg (sliceCorec F Y α) (F.snd_eq_value x.1 b).symm) _ _

/-- The underlying corecursion is hereditarily natural: its nodes are natural,
by {name}`nodeNatural_map_sliceCorec`, so it is hereditarily natural by
{name}`Geb.MType.hereditary_of_hom`. -/
theorem isHereditarilyNatural_sliceCorec (e : Σ i : I, Y.obj ⟨i⟩) :
    IsHereditarilyNatural F (sliceCorec F Y α e) := by
  unfold IsHereditarilyNatural
  refine hereditary_of_hom (Q := F.toPFunctor) _ _ (fun e ↦ (sliceStep F Y α e).1)
    (sliceCorec F Y α) (fun e ↦ congrArg Subtype.val (dest_sliceCorec F Y α e)) (fun e ↦ ?_) e
  change F.NodeNatural (SliceM.fixedPoint F.toSlicePFunctor) (sliceCorec F Y α e).dest
  rw [dest_sliceCorec]
  exact nodeNatural_map_sliceCorec F Y α (α.app ⟨e.1⟩ e.2).1

/-- The corecursor from a presheaf coalgebra {lit}`(Y, α)`: a natural
transformation into the carrier presheaf, whose component at {lit}`j` is the
underlying corecursion; naturality is {name}`sliceCorec_map`. -/
def corec : NatTrans Y (PresheafM F) where
  app j := ↾ fun y ↦ ULift.up ⟨sliceCorec F Y α ⟨j.unop, y⟩, index_sliceCorec F Y α _,
    isHereditarilyNatural_sliceCorec F Y α _⟩
  naturality _ _ g := by
    ext y
    apply carrier.obj_ext
    exact sliceCorec_map F Y α g.unop y

/-- The computation rule for the corecursor: it is a morphism of presheaf
coalgebras. -/
theorem dest_corec {j : I} (y : Y.obj ⟨j⟩) :
    carrier.dest ((corec F Y α).app ⟨j⟩ y) =
      (F.mapPresheaf (corec F Y α)).app ⟨j⟩ (α.app ⟨j⟩ y) := by
  apply Subtype.ext
  apply Subtype.ext
  refine (carrier.rememberNode_congr (dest_sliceCorec F Y α ⟨j, y⟩)
    ((isHereditarilyNatural_iff F _).mp (isHereditarilyNatural_sliceCorec F Y α ⟨j, y⟩)).2
    fun b ↦ isHereditarilyNatural_sliceCorec F Y α _).trans ?_
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦
    carrier.sigma_eta ((corec F Y α).app ⟨_⟩ ((sliceStep F Y α ⟨j, y⟩).1.2 b).2)))

/-- The corecursor is the only morphism of presheaf coalgebras into the
carrier presheaf: its underlying slice-level function is a morphism of slice
coalgebras, so it is the underlying corecursion. -/
theorem corec_unique (f : NatTrans Y (PresheafM F))
    (hf : ∀ (j : I) (y : Y.obj ⟨j⟩),
      carrier.dest (f.app ⟨j⟩ y) = (F.mapPresheaf f).app ⟨j⟩ (α.app ⟨j⟩ y)) :
    f = corec F Y α := by
  have h : (fun e : Σ i : I, Y.obj ⟨i⟩ ↦ (f.app ⟨e.1⟩ e.2).down.1) = sliceCorec F Y α :=
    SliceM.corec_unique F.toSlicePFunctor _ _ _ _ (funext fun e ↦ (f.app ⟨e.1⟩ e.2).down.2.1)
      fun e ↦ congrArg (fun w : (F.objPresheaf (PresheafM F)).obj ⟨e.1⟩ ↦ carrier.forgetNode w.1.1)
        (hf e.1 e.2)
  ext j y
  exact carrier.obj_ext (congrFun h ⟨j.unop, y⟩)

end Corec

end PresheafM

end Geb.MType
