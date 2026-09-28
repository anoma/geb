/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Carrier

/-!
# W-types of presheaf polynomial functors: hereditary naturality (constructive core)

For a presheaf polynomial endofunctor `F : PresheafPFunctor I I`, the W-type of
the underlying slice endofunctor `F.toSlicePFunctor : SlicePFunctor I I` carries
a tree-level naturality predicate. A slice W-tree assembles a shape with a
compatible family of child subtrees; the presheaf structure additionally acts on
directions contravariantly (`directionRestr`) and on the assignment of shapes to
output indices. A tree is hereditarily natural when, at every node, restricting a
child subtree along a morphism agrees with selecting the child at the reindexed
direction, hereditarily through the whole tree.

The carrier presheaf and its fixed-point structure are the generic ones of
`Presheaf/Carrier.lean`, at the slice W-type as a fixed point of the slice
endofunctor (`SlicePFunctor.wFixedPoint`). `wRestrTree` is its root-only
restriction of a slice W-tree along a morphism, `PresheafPFunctor.restrTree`.
`IsHereditarilyNatural` folds the local naturality equation, `NodeNatural`,
over the whole tree through the slice W-type's `Prop`-valued paramorphism
`SlicePFunctor.W.RecProp`; `isHereditarilyNatural_mk` is its one-level
computation rule, which makes it a `HereditaryNaturality`
(`wHereditaryNaturality`). What is particular to W-types is that fold and the
eliminator.

## Main definitions

* `PresheafPFunctor.wRestrTree` — the root-only restriction of a slice W-tree
  along a morphism, `restrTree` at `SlicePFunctor.wFixedPoint`.
* `PresheafPFunctor.IsHereditarilyNatural` — the tree-level naturality predicate
  on slice W-trees, defined by `SlicePFunctor.W.RecProp`.
* `PresheafPFunctor.wHereditaryNaturality` — `IsHereditarilyNatural` with its
  unfolding equation, a `HereditaryNaturality`.
* `PresheafPFunctor.wRestr` — restriction on the `ULift`ed carrier fiber,
  reindexing the underlying tree along a morphism while preserving the index and
  hereditary naturality.
* `PresheafPFunctor.W` — the carrier presheaf `Iᵒᵖ ⥤ Type (max uI uA uB)`, the
  generic `carrier` at `wHereditaryNaturality`, whose fiber over `j` is the
  `ULift` of the hereditarily-natural slice W-trees indexed at `j` and whose
  restriction maps are `wRestr`.
* `PresheafPFunctor.W.mk` / `PresheafPFunctor.W.dest` — the fixed-point
  constructor and destructor, `carrier.mk` / `carrier.dest`: mutually inverse
  fiberwise maps between the `objPresheaf`-value at `F.W` and `F.W`, exhibiting
  `F.W` as a fixed point of the `objPresheaf`-action at `F.W`.
* `PresheafPFunctor.W.PElimData` / `pElimStep` / `pElimData` — the eliminator's
  fold carrier, algebra, and fold (a `WType.elim` fold whose value is guarded by
  hereditary naturality, since the presheaf algebra acts only on natural nodes):
  the presheaf analogue of the slice `ElimData` machinery.
* `PresheafPFunctor.W.elimVal` — the eliminator's value on a carrier element,
  extracted from the fold given the tree's hereditary naturality.
* `PresheafPFunctor.W.elim` — the eliminator into any presheaf algebra `(Y, α)`,
  a natural transformation `F.W ⟶ Y`.
* `PresheafPFunctor.MemW` — membership of a raw W-tree in the carrier presheaf's
  fiber over an index, stated on `F.toPFunctor.W` so that it can be decided by a
  fold.

## Main statements

* `PresheafPFunctor.isHereditarilyNatural_mk` — the one-level unfolding of
  `IsHereditarilyNatural` on a constructor `SlicePFunctor.W.mk x`: local
  naturality at the root, together with hereditary naturality of every child.
* `PresheafPFunctor.wIndex_wRestrTree` — the index of a root-restricted tree is
  the restriction morphism's source.
* `PresheafPFunctor.isHereditarilyNatural_wRestrTree` — hereditary naturality is
  preserved by the root-only restriction, a one-level argument.
* `PresheafPFunctor.wRestrTree_id` / `PresheafPFunctor.wRestrTree_comp` — the
  functoriality of `wRestrTree`, from which `W`'s functor laws transport.
* `PresheafPFunctor.W.dest_mk` / `PresheafPFunctor.W.mk_dest` — `mk` and `dest`
  are mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
  `F.W`.
* `PresheafPFunctor.W.comp_elim` — `elim` is a morphism of presheaves (its
  `NatTrans` naturality), from `elimVal_wRestr`.
* `PresheafPFunctor.W.elim_mk` — the computation rule: `elim` commutes with `mk`,
  i.e. it is a morphism of presheaf algebras.
* `PresheafPFunctor.memW_iff_exists_obj` — `MemW` holds exactly of the trees
  underlying the carrier presheaf's fiber.

## Implementation notes

This is the presheaf endofunctor case, `I = J`, so the slice endofunctor
`F.toSlicePFunctor : SlicePFunctor I I` has a W-type. `wRestrTree` and
`IsHereditarilyNatural` act on the un-lifted trees `F.toSlicePFunctor.W` of type
`Type (max uA uB)`; the carrier presheaf `W` `ULift`s the indexed subtype into
`Type (max uI uA uB)` so its fibers land in a single universe with the index
category `I`.

The recursion in `IsHereditarilyNatural` is confined to the slice W-type's
`Prop`-valued paramorphism `SlicePFunctor.W.RecProp`: no explicit self-recursion
and no `induction` tactic appear. `wHereditaryNaturality` and
`SlicePFunctor.wFixedPoint` are reducible, so instance resolution sees
`IsHereditarilyNatural` and the slice W-type through the carrier presheaf's
fibers, where the decision procedures of `Presheaf/Decidable.lean` apply.

The eliminator `elim` folds the underlying slice tree into a target value with a
bespoke `WType.elim` fold (`pElimData`, carrier `PElimData`, algebra
`pElimStep`), the presheaf analogue of the slice `elim`'s `ElimData` fold. The
presheaf algebra `α` acts only on natural nodes, so — unlike the slice `elim`,
whose algebra is total — the fold's value is a function of the subtree's
hereditary naturality, and the fold carries a naturality proxy (via the guard
`P ∧ ∀ hp : P, Q hp`, the standard `And` with `Q` proof-irrelevant in `hp`) letting
`α` apply at each node. The value fold is
a non-dependent `WType.elim` (code-generatable); the recursion in the
accompanying proofs (`pElimData_valid`, `elimVal_wRestr`) stays inside
`WType.rec` / `SlicePFunctor.W.induction`. Only the existence half of the
initial-algebra universal property is established — the carrier, its fixed-point
structure, and `elim` with its computation rule `elim_mk` and naturality law
`comp_elim`; uniqueness of `elim` is not formalized.

## References

* [Weber2007]
* [GambinoHyland2004]
* [GambinoKock2013]
* [AltenkirchGhaniHancockMcBrideMorris2015]

## Tags

W-type, initial algebra, polynomial functor, presheaf, parametric right adjoint,
naturality, restriction map, PFunctor
-/

public section

open CategoryTheory

universe uI uA uB vI

namespace PresheafPFunctor

/-- The root-only restriction of a slice W-tree `z` along a morphism `g : j' ⟶ j`
(where `j` is the index of `z`): the root restriction `restrTree` of the W-type
as a fixed point of the slice endofunctor, `SlicePFunctor.wFixedPoint`. The
head-index witness is the hypothesis `hq`, the root's `q`-output index being
read from `PFunctor.W.head`. -/
@[expose] def wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.W :=
  F.restrTree F.toSlicePFunctor.wFixedPoint g z hq

/-- Hereditary naturality of a slice W-tree: at every node, restricting a child
subtree along a morphism `g` agrees with selecting the child at the reindexed
direction, hereditarily. The local conjunct is `NodeNatural`, the tree analogue
of `PresheafDomPFunctorData.IsNatural`; the fold over the tree is carried by the
slice W-type's `Prop`-valued paramorphism `SlicePFunctor.W.RecProp`. -/
@[expose] def IsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : F.toSlicePFunctor.W → Prop :=
  SlicePFunctor.W.RecProp fun x ih ↦ F.NodeNatural F.toSlicePFunctor.wFixedPoint x ∧ ∀ b, ih b

/-- One-level unfolding of `IsHereditarilyNatural` on a constructor
`SlicePFunctor.W.mk x`: local naturality at the root together with hereditary
naturality of every child subtree. From `SlicePFunctor.W.recProp_mk`. -/
theorem isHereditarilyNatural_mk {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.wIndex) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
          x.1.2 (F.directionRestr x.1.1 g b).1
            = F.wRestrTree g (x.1.2 b.1)
                (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.wIndex x.1.1 x.1.2).mp
                  x.2 b.1).trans b.2)) ∧
        ∀ b, F.IsHereditarilyNatural (x.1.2 b) := by
  unfold IsHereditarilyNatural
  rw [SlicePFunctor.W.recProp_mk]
  exact Iff.rfl

/-- Hereditary naturality of slice W-trees satisfies the unfolding equation of
`HereditaryNaturality`, from `isHereditarilyNatural_mk`. Reducible, so that
instance resolution sees `IsHereditarilyNatural` through the carrier
presheaf's fibres. -/
@[expose, reducible] def wHereditaryNaturality {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) :
    F.HereditaryNaturality F.toSlicePFunctor.wFixedPoint where
  holds := F.IsHereditarilyNatural
  holds_iff t :=
    (iff_of_eq (congrArg F.IsHereditarilyNatural (SlicePFunctor.W.mk_dest t).symm)).trans
      (F.isHereditarilyNatural_mk (SlicePFunctor.W.dest t))

/-- The index of a root-restricted tree is `j'`. -/
theorem wIndex_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.wIndex (F.wRestrTree g z hq) = j' :=
  F.index_restrTree F.toSlicePFunctor.wFixedPoint g z hq

/-- Hereditary naturality is preserved by the root-only restriction. -/
theorem isHereditarilyNatural_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hz : F.IsHereditarilyNatural z) :
    F.IsHereditarilyNatural (F.wRestrTree g z hq) :=
  F.wHereditaryNaturality.holds_restrTree g z hq hz

/-- Restriction on the `ULift`ed carrier fiber: `carrierRestr` at
`wHereditaryNaturality`. -/
@[expose] def wRestr {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j) :
    ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.wIndex w = j ∧ F.IsHereditarilyNatural w } →
      ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.wIndex w = j' ∧ F.IsHereditarilyNatural w } :=
  F.carrierRestr F.wHereditaryNaturality g

/-- Restriction along an identity fixes the tree. -/
theorem wRestrTree_id {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j : I⦄
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.wRestrTree (𝟙 j) z hq = z :=
  F.restrTree_id F.toSlicePFunctor.wFixedPoint z hq

/-- Restriction along a composite factors. -/
theorem wRestrTree_comp {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' j'' : I⦄ (g : j' ⟶ j)
    (h : j'' ⟶ j') (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hq2 : F.q (PFunctor.W.head (F.wRestrTree g z hq).1) = j') :
    F.wRestrTree (h ≫ g) z hq = F.wRestrTree h (F.wRestrTree g z hq) hq2 :=
  F.restrTree_comp F.toSlicePFunctor.wFixedPoint g h z hq hq2

/-- The carrier presheaf `W : Iᵒᵖ ⥤ Type` of the presheaf polynomial endofunctor
`F`: the carrier presheaf `carrier` of the hereditarily natural slice W-trees,
whose fiber over `j` is the `ULift` of the hereditarily-natural slice W-trees
indexed at `j` and whose restriction maps are `wRestr`. -/
@[expose] def W {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : Iᵒᵖ ⥤ Type (max uI uA uB) :=
  F.carrier F.wHereditaryNaturality

namespace W

/-- The fixed-point constructor of the presheaf W-type: the `objPresheaf`-value
at the carrier presheaf `F.W` maps into `F.W`, fiberwise over `I`; the carrier
constructor `carrier.mk`. -/
@[expose] def mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : (F.W).obj ⟨j⟩ :=
  carrier.mk (N := F.wHereditaryNaturality) x

/-- The fixed-point destructor of the presheaf W-type, inverse to `mk`; the
carrier destructor `carrier.dest`. -/
@[expose] def dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : (F.objPresheaf F.W).obj ⟨j⟩ :=
  carrier.dest (N := F.wHereditaryNaturality) z

/-- `dest` is a left inverse of `mk`. -/
@[simp]
theorem dest_mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : dest (mk x) = x :=
  carrier.dest_mk (N := F.wHereditaryNaturality) x

/-- `mk` is a left inverse of `dest`; with `dest_mk`, `mk` and `dest` are
mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
`F.W`. -/
@[simp]
theorem mk_dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : mk (dest z) = z :=
  carrier.mk_dest (N := F.wHereditaryNaturality) z

/-- The carrier of the presheaf-`W` value fold: the slice `WIndex` (root index
and admissibility) together with a hereditary-naturality proxy `H`, a value
function producing a total-space element of `Y` once the subtree is admissible
and hereditarily natural, and a proof `over` that the value lies over the
index. -/
@[ext]
structure PElimData {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) extends SlicePFunctor.WIndex I where
  /-- Hereditary naturality of the subtree, a fold-level proxy. -/
  H : valid → Prop
  /-- The subtree's contributed value, in the total space of `Y`, available once
  the subtree is admissible and hereditarily natural. -/
  value : (hv : valid) → H hv → Σ i : I, Y.obj ⟨i⟩
  /-- The value lies over the index. -/
  over : ∀ (hv : valid) (hn : H hv), (value hv hn).1 = index

/-- The slice node over `elemProj Y` assembled from a shape `a` and the children
carriers' values: the direction assignment sends `b` to the child value
`(c b).value`, compatible with `elemProj Y` by the children's `over` and the
node's `OverInput`. -/
@[expose] def pNodeSlice {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I}
    {Y : Iᵒᵖ ⥤ Type (max uI uA uB)} {a : F.toPFunctor.A}
    (c : F.toPFunctor.B a → PElimData F Y)
    (hv : F.toSlicePFunctor.NodeValid a (fun b ↦ (c b).toWIndex))
    (hc : ∀ b, (c b).H (hv.1 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Y) :=
  ⟨⟨a, fun b ↦ (c b).value (hv.1 b) (hc b)⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj Y) a _).mpr
      fun b ↦ ((c b).over (hv.1 b) (hc b)).trans (congrFun hv.2 b)⟩

/-- The value-fold algebra step: index and admissibility as for `wIndexStep`; a
hereditary-naturality proxy `H` combining the children's proxies with the
naturality of the assembled node (`pNodeSlice`); and a value that applies the
presheaf algebra `α` to that node, packaged over the shape's `q`-output index. -/
@[expose] def pElimStep {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) :
    F.toPFunctor.Obj (PElimData F Y) → PElimData F Y :=
  fun x ↦
    { index := F.q x.1
      valid := F.toSlicePFunctor.NodeValid x.1 (fun b ↦ (x.2 b).toWIndex)
      H := fun hv ↦ (∀ b, (x.2 b).H (hv.1 b)) ∧
        (∀ hc : (∀ b, (x.2 b).H (hv.1 b)), F.IsNatural (pNodeSlice x.2 hv hc))
      value := fun hv hn ↦
        ⟨F.q x.1, α.app ⟨F.q x.1⟩ ⟨⟨pNodeSlice x.2 hv hn.1, hn.2 hn.1⟩, rfl⟩⟩
      over := fun _ _ ↦ rfl }

/-- The value fold: the `F.toPFunctor`-algebra morphism into
`(PElimData F Y, pElimStep)` given by `WType.elim`, a single non-dependent fold
with no explicit recursion. -/
@[expose] def pElimData {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) :
    F.toPFunctor.W → PElimData F Y :=
  WType.elim (PElimData F Y) (pElimStep F Y α)

/-- The index-and-admissibility projection of `pElimData` agrees with the slice
fold `wIndexValid`: the value fold refines the slice fold, so admissibility and
the root index transport from the slice results. Proved by the dependent
recursor `WType.rec`. -/
theorem pElimData_toWIndex {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pElimData F Y α w).toWIndex = F.wIndexValid w :=
  WType.rec (motive := fun w ↦ (pElimData F Y α w).toWIndex = F.wIndexValid w)
    (fun a f ih ↦ by
      change F.wIndexStep ⟨a, fun b ↦ (pElimData F Y α (f b)).toWIndex⟩ =
        F.wIndexStep ⟨a, fun b ↦ F.wIndexValid (f b)⟩
      rw [funext ih])
    w

/-- The admissibility component of `pElimData` is `WValid`. -/
theorem pElimData_valid {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pElimData F Y α w).valid = F.WValid w :=
  congrArg SlicePFunctor.WIndex.valid (pElimData_toWIndex F Y α w)

/-- The index component of `pElimData` is the root index. -/
theorem pElimData_index {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pElimData F Y α w).index = F.wIndexRoot w :=
  (congrArg SlicePFunctor.WIndex.index (pElimData_toWIndex F Y α w)).trans
    (F.wIndexValid_index_eq_wIndexRoot w)

/-- A natural transformation's components respect heterogeneous equality of
fiber elements over equal indices. -/
private theorem app_heq.{w} {I : Type uI} [Category.{vI} I]
    {Z Z' : Iᵒᵖ ⥤ Type w} (β : NatTrans Z Z') {k k' : I} (hk : k = k')
    {x : Z.obj ⟨k⟩} {x' : Z.obj ⟨k'⟩} (hx : x ≍ x') :
    β.app ⟨k⟩ x ≍ β.app ⟨k'⟩ x' := by
  cases hk
  cases hx
  rfl

/-- Two fiber elements of `objPresheaf Y` over equal indices whose underlying
dom values are equal are heterogeneously equal. -/
private theorem objPresheaf_obj_heq {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) (Y : Iᵒᵖ ⥤ Type (max uI uA uB))
    {k k' : I} (hk : k = k') {u : (F.objPresheaf Y).obj ⟨k⟩} {u' : (F.objPresheaf Y).obj ⟨k'⟩}
    (h : u.1 = u'.1) : u ≍ u' := by
  cases hk
  exact heq_of_eq (Subtype.ext h)

/-- Value restriction coherence at the fold level: the fold value on the
root-restriction of a tree is the `Y`-restriction of the fold value. A one-level
argument: the restricted node's fold node is the `objPresheaf`-restriction of the
node, so `α`'s naturality relates their `α`-images. -/
theorem value_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y)
    (t : F.toSlicePFunctor.W) ⦃i i' : I⦄ (f : i' ⟶ i)
    (hqi : F.q (PFunctor.W.head t.1) = i)
    (hv : (pElimData F Y α t.1).valid) (hn : (pElimData F Y α t.1).H hv)
    (hv' : (pElimData F Y α (F.wRestrTree f t hqi).1).valid)
    (hn' : (pElimData F Y α (F.wRestrTree f t hqi).1).H hv') :
    (pElimData F Y α (F.wRestrTree f t hqi).1).value hv' hn' =
      ⟨i', Y.map f.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
          (((pElimData F Y α t.1).over hv hn).trans
            ((pElimData_index F Y α t.1).trans hqi)))
        ((pElimData F Y α t.1).value hv hn).2)⟩ := by
  obtain ⟨tree, hval⟩ := t
  cases tree with
  | mk a fchild =>
    refine Sigma.ext (F.shapeRestr f ⟨a, hqi⟩).2 ?_
    have hqa : F.q a = i := hqi
    subst hqa
    have hnat :
        Y.map f.op (α.app ⟨F.q a⟩ (⟨⟨pNodeSlice (fun b ↦ pElimData F Y α (fchild b)) hv hn.1,
            hn.2 hn.1⟩, rfl⟩ : (F.objPresheaf Y).obj ⟨F.q a⟩)) =
          α.app ⟨i'⟩ ((F.objPresheaf Y).map f.op
            ⟨⟨pNodeSlice (fun b ↦ pElimData F Y α (fchild b)) hv hn.1, hn.2 hn.1⟩, rfl⟩) :=
      (FunctorToTypes.naturality _ _ α f.op _).symm
    change (α.app ⟨F.q (F.shapeRestr f ⟨a, hqi⟩).1⟩
          (⟨⟨F.objRestrElt f (pNodeSlice (fun b ↦ pElimData F Y α (fchild b)) hv hn.1) hqi,
            hn'.2 hn'.1⟩, rfl⟩ : (F.objPresheaf Y).obj ⟨F.q (F.shapeRestr f ⟨a, hqi⟩).1⟩)) ≍
        Y.map f.op (α.app ⟨F.q a⟩
          (⟨⟨pNodeSlice (fun b ↦ pElimData F Y α (fchild b)) hv hn.1, hn.2 hn.1⟩, rfl⟩ :
            (F.objPresheaf Y).obj ⟨F.q a⟩))
    rw [hnat]
    exact app_heq α (F.shapeRestr f ⟨a, hqi⟩).2
      (objPresheaf_obj_heq F Y (F.shapeRestr f ⟨a, hqi⟩).2 (Subtype.ext rfl))

/-- The node the value fold assembles at a slice node whose children are folds of
hereditarily-natural subtrees is natural: local naturality of the enclosing tree
(each child restricting to the child at the reindexed direction) transports
through the fold's value-restriction coherence `value_wRestrTree`. -/
private theorem isNatural_pNodeSlice {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y)
    {a : F.toPFunctor.A} (fc : F.toPFunctor.B a → F.toSlicePFunctor.W)
    (hv : F.toSlicePFunctor.NodeValid a (fun b ↦ (pElimData F Y α (fc b).1).toWIndex))
    (hc : ∀ b, (pElimData F Y α (fc b).1).H (hv.1 b))
    (hloc : ∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction a i)
        (hq : F.q (PFunctor.W.head (fc b.1).1) = i),
        fc (F.directionRestr a g b).1 = F.wRestrTree g (fc b.1) hq) :
    F.IsNatural (pNodeSlice (fun b ↦ pElimData F Y α (fc b).1) hv hc) := by
  intro i i' g b
  change F.value (pNodeSlice (fun b ↦ pElimData F Y α (fc b).1) hv hc) (F.directionRestr a g b) =
    Y.map g.op (F.value (pNodeSlice (fun b ↦ pElimData F Y α (fc b).1) hv hc) b)
  have hqit : F.q (PFunctor.W.head (fc b.1).1) = i :=
    (pElimData_index F Y α (fc b.1).1).symm.trans ((congrFun hv.2 b.1).trans b.2)
  have hgen : ∀ (T : F.toSlicePFunctor.W) (hvT : (pElimData F Y α T.1).valid)
      (hnT : (pElimData F Y α T.1).H hvT), T = F.wRestrTree g (fc b.1) hqit →
      (pElimData F Y α T.1).value hvT hnT =
        ⟨i', Y.map g.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
            (((pElimData F Y α (fc b.1).1).over (hv.1 b.1) (hc b.1)).trans
              ((pElimData_index F Y α (fc b.1).1).trans hqit)))
          ((pElimData F Y α (fc b.1).1).value (hv.1 b.1) (hc b.1)).2)⟩ := by
    intro T hvT hnT hT
    subst hT
    exact value_wRestrTree F Y α (fc b.1) g hqit (hv.1 b.1) (hc b.1) hvT hnT
  have hchild :
      (pNodeSlice (fun b ↦ pElimData F Y α (fc b).1) hv hc).1.2
          (F.directionRestr a g b).1 =
        ⟨i', Y.map g.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
            (((pElimData F Y α (fc b.1).1).over (hv.1 b.1) (hc b.1)).trans
              ((pElimData_index F Y α (fc b.1).1).trans hqit)))
          ((pElimData F Y α (fc b.1).1).value (hv.1 b.1) (hc b.1)).2)⟩ :=
    hgen (fc (F.directionRestr a g b).1) (hv.1 (F.directionRestr a g b).1)
      (hc (F.directionRestr a g b).1) (hloc g b hqit)
  simp only [PresheafDomPFunctorData.value]
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  rw [hchild]
  rfl

/-- The value fold's hereditary-naturality proxy `H` holds at every validated
hereditarily-natural tree: the children's proxies hold by the tree recursion
(`SlicePFunctor.W.induction`), and the node the fold assembles (`pNodeSlice`)
is natural by `isNatural_pNodeSlice`, from the tree's local naturality. -/
theorem pElimData_H_of_isHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y)
    (w : F.toSlicePFunctor.W) (hv : (pElimData F Y α w.1).valid)
    (hn : F.IsHereditarilyNatural w) : (pElimData F Y α w.1).H hv :=
  SlicePFunctor.W.induction
    (motive := fun z ↦ ∀ (hv : (pElimData F Y α z.1).valid),
      F.IsHereditarilyNatural z → (pElimData F Y α z.1).H hv)
    (fun x ih hv hHN ↦ by
      refine ⟨fun b ↦ ih b (hv.1 b) (((F.isHereditarilyNatural_mk x).mp hHN).2 b), fun _ ↦ ?_⟩
      exact isNatural_pNodeSlice F Y α x.1.2 hv
        (fun b ↦ ih b (hv.1 b) (((F.isHereditarilyNatural_mk x).mp hHN).2 b))
        (fun _ _ g b _ ↦ ((F.isHereditarilyNatural_mk x).mp hHN).1 g b))
    w hv hn

/-- The fiber value the fold contributes to a validated hereditarily-natural
tree indexed at `j`: the total-space value's `Y`-component, transported to the
fiber over `j` through the fold's `over` law and root-index agreement. -/
@[expose] def elimVal {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) {j : I}
    (z : (F.W).obj ⟨j⟩) : Y.obj ⟨j⟩ :=
  cast (congrArg (fun i : I ↦ Y.obj ⟨i⟩)
      ((((pElimData F Y α z.down.1.1).over
          ((pElimData_valid F Y α z.down.1.1) ▸ z.down.1.2)
          (pElimData_H_of_isHereditarilyNatural F Y α z.down.1
            ((pElimData_valid F Y α z.down.1.1) ▸ z.down.1.2) z.down.2.2)).trans
        (pElimData_index F Y α z.down.1.1)).trans z.down.2.1))
    ((pElimData F Y α z.down.1.1).value
      ((pElimData_valid F Y α z.down.1.1) ▸ z.down.1.2)
      (pElimData_H_of_isHereditarilyNatural F Y α z.down.1
        ((pElimData_valid F Y α z.down.1.1) ▸ z.down.1.2) z.down.2.2)).2

/-- The total-space fold value at a carrier element is `elimVal` paired with the
index: the `Y`-component is `elimVal` and the base point is the fiber index.
Proof-irrelevance identifies the fold's internal hereditary-naturality proof with
any supplied one. -/
theorem value_eq_elimVal {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) {j : I}
    (z : (F.W).obj ⟨j⟩) (hv : (pElimData F Y α z.down.1.1).valid)
    (hn : (pElimData F Y α z.down.1.1).H hv) :
    (pElimData F Y α z.down.1.1).value hv hn = ⟨j, elimVal F Y α z⟩ := by
  refine Sigma.ext (((((pElimData F Y α z.down.1.1).over hv hn).trans
    (pElimData_index F Y α z.down.1.1)).trans z.down.2.1)) ?_
  exact (cast_heq _ _).symm

/-- `elimVal` commutes with the restriction maps: the value of a restricted
carrier element is the `Y`-restriction of the value. It glues the fold-level
restriction coherence `value_wRestrTree` (the one-level argument, combining the
fold's one-level computation with `α`'s naturality) with `value_eq_elimVal`,
which identifies the two total-space fold values' fiber components with the two
`elimVal`s; the tree recursion is confined to `pElimData_H_of_isHereditarilyNatural`. -/
theorem elimVal_wRestr {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) ⦃i i' : I⦄
    (g : i' ⟶ i) (z : (F.W).obj ⟨i⟩) :
    elimVal F Y α ((F.W).map g.op z) = Y.map g.op (elimVal F Y α z) := by
  have hvz : (pElimData F Y α z.down.1.1).valid :=
    (pElimData_valid F Y α z.down.1.1) ▸ z.down.1.2
  have hnz : (pElimData F Y α z.down.1.1).H hvz :=
    pElimData_H_of_isHereditarilyNatural F Y α z.down.1 hvz z.down.2.2
  have hvzr : (pElimData F Y α ((F.W).map g.op z).down.1.1).valid :=
    (pElimData_valid F Y α ((F.W).map g.op z).down.1.1) ▸ ((F.W).map g.op z).down.1.2
  have hnzr : (pElimData F Y α ((F.W).map g.op z).down.1.1).H hvzr :=
    pElimData_H_of_isHereditarilyNatural F Y α ((F.W).map g.op z).down.1 hvzr
      ((F.W).map g.op z).down.2.2
  have eR := value_eq_elimVal F Y α ((F.W).map g.op z) hvzr hnzr
  have eW := value_wRestrTree F Y α z.down.1 g z.down.2.1 hvz hnz hvzr hnzr
  have key : (⟨i', elimVal F Y α ((F.W).map g.op z)⟩ : Σ k : I, Y.obj ⟨k⟩)
      = ⟨i', Y.map g.op (elimVal F Y α z)⟩ := eR.symm.trans eW
  exact eq_of_heq (Sigma.ext_iff.mp key).2

/-- The eliminator of the presheaf W-type: the natural transformation into any
presheaf algebra `(Y, α)`. Its component over `j` is the bespoke value fold
`elimVal`; naturality is `elimVal_wRestr`. The existence half of initiality. -/
@[expose] def elim {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) :
    NatTrans F.W Y where
  app j := ↾ fun z ↦ elimVal F Y α (j := j.unop) z
  naturality _ _ g := by
    ext z
    exact elimVal_wRestr F Y α g.unop z

/-- `elim` is a presheaf morphism: it commutes with the restriction
maps of `F.W` and `Y`. The `NatTrans` naturality of `elim`, mirroring the slice
`comp_elim`. -/
theorem comp_elim {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) ⦃i i' : I⦄
    (g : i' ⟶ i) (z : (F.W).obj ⟨i⟩) :
    (elim F Y α).app ⟨i'⟩ ((F.W).map g.op z) = Y.map g.op ((elim F Y α).app ⟨i⟩ z) :=
  elimVal_wRestr F Y α g z

/-- The computation rule for `elim`: it commutes with the constructor `mk`, i.e.
it is a morphism of presheaf algebras. -/
theorem elim_mk {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) :
    (elim F Y α).app ⟨j⟩ (mk x) =
      α.app ⟨j⟩ ((F.mapPresheaf (elim F Y α)).app ⟨j⟩ x) := by
  have hv : (pElimData F Y α (mk x).down.1.1).valid :=
    (pElimData_valid F Y α (mk x).down.1.1) ▸ (mk x).down.1.2
  have hn : (pElimData F Y α (mk x).down.1.1).H hv :=
    pElimData_H_of_isHereditarilyNatural F Y α (mk x).down.1 hv (mk x).down.2.2
  have hq : F.q x.1.1.1.1 = j := x.2
  have hchild : ∀ b, (pElimData F Y α (x.1.1.1.2 b).2.down.1.1).value (hv.1 b) (hn.1 b)
      = (⟨(x.1.1.1.2 b).1, elimVal F Y α (x.1.1.1.2 b).2⟩ : Σ i : I, Y.obj ⟨i⟩) :=
    fun b ↦ value_eq_elimVal F Y α (x.1.1.1.2 b).2 (hv.1 b) (hn.1 b)
  have hval := value_eq_elimVal F Y α (mk x) hv hn
  apply eq_of_heq
  refine ((Sigma.ext_iff.mp hval).2.symm).trans ?_
  refine app_heq α hq ?_
  refine objPresheaf_obj_heq F Y hq ?_
  apply Subtype.ext
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ hchild b))

end W

/-- Membership of a raw W-tree in the carrier presheaf's fiber over `j`: the
tree is admissible, its index is `j`, and it is hereditarily natural. Stated on
`F.toPFunctor.W` rather than on `W`'s fiber so that a decision procedure has a
raw tree to fold over; `memW_iff_exists_obj` identifies it with the fiber. -/
@[expose] def MemW {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) (j : I)
    (w : F.toPFunctor.W) : Prop :=
  ∃ hw : F.toSlicePFunctor.WValid w,
    F.toSlicePFunctor.wIndex ⟨w, hw⟩ = j ∧ F.IsHereditarilyNatural ⟨w, hw⟩

/-- `MemW` holds exactly of the trees underlying the carrier presheaf's fiber
over `j`. -/
theorem memW_iff_exists_obj {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) (j : I)
    (w : F.toPFunctor.W) :
    F.MemW j w ↔ ∃ u : (F.W).obj ⟨j⟩, u.down.1.1 = w := by
  constructor
  · rintro ⟨hw, hq, hn⟩
    exact ⟨ULift.up ⟨⟨w, hw⟩, hq, hn⟩, rfl⟩
  · rintro ⟨⟨⟨⟨w', hw'⟩, hq, hn⟩⟩, rfl⟩
    exact ⟨hw', hq, hn⟩

end PresheafPFunctor
