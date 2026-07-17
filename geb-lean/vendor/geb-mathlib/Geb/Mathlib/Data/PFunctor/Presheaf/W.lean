/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

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

`wRestrTree` is the root-only restriction of a slice W-tree along a morphism: it
restricts the root shape and reindexes the direction-assignment via the
generalized `PresheafPFunctor.objRestrElt`, conjugated by the slice destructor
and constructor. `IsHereditarilyNatural` folds the local naturality equation
over the whole tree through the slice W-type's `Prop`-valued paramorphism
`SlicePFunctor.W.recProp`; `isHereditarilyNatural_mk` is its one-level
computation rule.

## Main definitions

* `PresheafPFunctor.wRestrTree` — the root-only restriction of a slice W-tree
  along a morphism, via the generalized `objRestrElt` at `p := windex`.
* `PresheafPFunctor.IsHereditarilyNatural` — the tree-level naturality predicate
  on slice W-trees, defined by `SlicePFunctor.W.recProp`.
* `PresheafPFunctor.wRestr` — restriction on the `ULift`ed carrier fibre,
  reindexing the underlying tree along a morphism while preserving the index and
  hereditary naturality.
* `PresheafPFunctor.W` — the carrier presheaf `Iᵒᵖ ⥤ Type (max uI uA uB)`, whose
  fibre over `j` is the `ULift` of the hereditarily-natural slice W-trees indexed
  at `j` and whose restriction maps are `wRestr`.
* `PresheafPFunctor.W.forgetNode` / `PresheafPFunctor.W.rememberNode` — the
  mutually inverse translations between a presheaf node over the carrier
  presheaf `F.W` and the underlying slice node over `windex` together with the
  hereditary naturality of its children.
* `PresheafPFunctor.W.mk` / `PresheafPFunctor.W.dest` — the fixed-point
  constructor and destructor: mutually inverse fibrewise maps between the
  `objPresheaf`-value at `F.W` and `F.W`, exhibiting `F.W` as a fixed point of
  the `objPresheaf`-action at `F.W`.
* `PresheafPFunctor.W.PElimData` / `pelimStep` / `pelimData` — the eliminator's
  fold carrier, algebra, and fold (a `WType.elim` fold whose value is guarded by
  hereditary naturality, since the presheaf algebra acts only on natural nodes):
  the presheaf analogue of the slice `ElimData` machinery.
* `PresheafPFunctor.W.elimVal` — the eliminator's value on a carrier element,
  extracted from the fold given the tree's hereditary naturality.
* `PresheafPFunctor.W.elim` — the eliminator into any presheaf algebra `(Y, α)`,
  a natural transformation `F.W ⟶ Y`.

## Main statements

* `PresheafPFunctor.isHereditarilyNatural_mk` — the one-level unfolding of
  `IsHereditarilyNatural` on a constructor `SlicePFunctor.W.mk x`: local
  naturality at the root, together with hereditary naturality of every child.
* `PresheafPFunctor.windex_wRestrTree` — the index of a root-restricted tree is
  the restriction morphism's source.
* `PresheafPFunctor.isHereditarilyNatural_wRestrTree` — hereditary naturality is
  preserved by the root-only restriction, a one-level argument.
* `PresheafPFunctor.wRestrTree_id` / `PresheafPFunctor.wRestrTree_comp` — the
  functoriality of `wRestrTree`, from which `W`'s functor laws transport.
* `PresheafPFunctor.W.dest_mk` / `PresheafPFunctor.W.mk_dest` — `mk` and `dest`
  are mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
  `F.W`.
* `PresheafPFunctor.W.isHereditarilyNatural_mk_forgetNode` — hereditary
  naturality of the slice tree built from a presheaf node over `F.W` is exactly
  the node's `IsNatural` datum; the correspondence underlying `mk` / `dest` and
  the eliminator fold.
* `PresheafPFunctor.W.comp_elim` — `elim` is a morphism of presheaves (its
  `NatTrans` naturality), from `elimVal_wRestr`.
* `PresheafPFunctor.W.elim_mk` — the computation rule: `elim` commutes with `mk`,
  i.e. it is a morphism of presheaf algebras.

## Implementation notes

This is the presheaf endofunctor case, `I = J`, so the slice endofunctor
`F.toSlicePFunctor : SlicePFunctor I I` has a W-type. `wRestrTree` and
`IsHereditarilyNatural` act on the un-lifted trees `F.toSlicePFunctor.W` of type
`Type (max uA uB)`; the carrier presheaf `W` `ULift`s the indexed subtype into
`Type (max uI uA uB)` so its fibres land in a single universe with the index
category `I`.

The recursion in `IsHereditarilyNatural` is confined to the slice W-type's
`Prop`-valued paramorphism `SlicePFunctor.W.recProp`: no explicit self-recursion
and no `induction` tactic appear. The child-index witness required by
`wRestrTree` is discharged from the compatibility of the node's
direction-assignment (`SliceDomPFunctor.compatible_iff`) together with the
direction's fibre constraint, exactly as `PresheafDomPFunctorData.value` obtains
its index equality.

The eliminator `elim` folds the underlying slice tree into a target value with a
bespoke `WType.elim` fold (`pelimData`, carrier `PElimData`, algebra
`pelimStep`), the presheaf analogue of the slice `elim`'s `ElimData` fold. The
presheaf algebra `α` acts only on natural nodes, so — unlike the slice `elim`,
whose algebra is total — the fold's value is a function of the subtree's
hereditary naturality, and the fold carries a naturality proxy (via the guard
`P ∧ ∀ hp : P, Q hp`, builtin `And` with `Q` proof-irrelevant in `hp`) letting
`α` apply at each node. The value fold is
a non-dependent `WType.elim` (code-generatable); the recursion in the
accompanying proofs (`pelimData_valid`, `elimVal_wRestr`) stays inside
`WType.rec` / `SlicePFunctor.W.ind`. Only the existence half of the
initial-algebra universal property is established — the carrier, its fixed-point
structure, and `elim` with its computation rule `elim_mk` and over-`I` law
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
(where `j` is the index of `z`): restrict the root shape and reindex its
direction-assignment via the generalized `objRestrElt` at the projection
`p := F.toSlicePFunctor.windex`, conjugating by the slice destructor and
constructor. The head-index witness required by `objRestrElt` is the hypothesis
`hq`, the root's `q`-output index being read from `PFunctor.W.head`. -/
@[expose] def wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.W :=
  SlicePFunctor.W.mk (F.objRestrElt g (SlicePFunctor.W.dest z)
    (by obtain ⟨w, hw⟩ := z; cases w with | mk a f => exact hq))

/-- Hereditary naturality of a slice W-tree: at every node, restricting a child
subtree along a morphism `g` agrees with selecting the child at the reindexed
direction, hereditarily. The local conjunct is the tree analogue of
`PresheafDomPFunctorData.IsNatural`; the fold over the tree is carried by the
slice W-type's `Prop`-valued paramorphism `SlicePFunctor.W.recProp`. -/
@[expose] def IsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : F.toSlicePFunctor.W → Prop :=
  SlicePFunctor.W.recProp (fun x ih ↦
    (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
        x.1.2 (F.directionRestr x.1.1 g b).1
          = F.wRestrTree g (x.1.2 b.1)
              (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex x.1.1 x.1.2).mp
                x.2 b.1).trans b.2)) ∧ ∀ b, ih b)

/-- One-level unfolding of `IsHereditarilyNatural` on a constructor
`SlicePFunctor.W.mk x`: local naturality at the root together with hereditary
naturality of every child subtree. From `SlicePFunctor.W.recProp_mk`. -/
theorem isHereditarilyNatural_mk {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
          x.1.2 (F.directionRestr x.1.1 g b).1
            = F.wRestrTree g (x.1.2 b.1)
                (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex x.1.1 x.1.2).mp
                  x.2 b.1).trans b.2)) ∧
        ∀ b, F.IsHereditarilyNatural (x.1.2 b) := by
  unfold IsHereditarilyNatural
  rw [SlicePFunctor.W.recProp_mk]

/-- The index of a root-restricted tree is `j'`: `wRestrTree g z` rebuilds the
root with the restricted shape `(shapeRestr g _).1`, whose `q`-output index is
`j'`. -/
theorem windex_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.windex (F.wRestrTree g z hq) = j' := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a f => exact (F.shapeRestr g ⟨a, hq⟩).2

/-- The child a root-restricted node assigns to a direction is the child the
original node assigns to the direction's `reindex`. The analogue of
`value_objRestrElt` for the raw child assignment; `rfl` after destructuring the
direction, matching `objRestrElt`'s internal `⟨·, rfl⟩` reconstruction. -/
private theorem snd_objRestrElt {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex) (hq : F.q x.1.1 = j) ⦃i : I⦄
    (d : F.toSliceDomPFunctor.Direction (F.objRestrElt g x hq).1.1 i) :
    (F.objRestrElt g x hq).1.2 d.1 = x.1.2 (F.reindex g ⟨x.1.1, hq⟩ d).1 := by
  obtain ⟨dv, rfl⟩ := d
  rfl

/-- Hereditary naturality is preserved by the root-only restriction: the
children of `wRestrTree g z` are the original subtrees reindexed (each already
hereditarily natural), and its root's local naturality follows from `z`'s own
root local naturality and `reindex_naturality`. A one-level argument, not a
recursion. -/
theorem isHereditarilyNatural_wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hz : F.IsHereditarilyNatural z) :
    F.IsHereditarilyNatural (F.wRestrTree g z hq) := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    obtain ⟨hz_local, hz_children⟩ :=
      (F.isHereditarilyNatural_mk (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩)).mp hz
    refine (F.isHereditarilyNatural_mk _).mpr ⟨?_, ?_⟩
    · intro i i' h b
      obtain ⟨bv, rfl⟩ := b
      rw [F.snd_objRestrElt]
      exact (congrArg (fun d ↦ (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩).1.2 d.1)
          (congrFun (F.isFunctorial.reindex_naturality g ⟨a, hq⟩ h) ⟨bv, rfl⟩).symm).trans
        (hz_local h (F.reindex g ⟨a, hq⟩ ⟨bv, rfl⟩))
    · intro b
      exact hz_children (F.reindex g ⟨a, hq⟩ ⟨b, rfl⟩).1

/-- Restriction on the ULifted carrier fibre: apply `wRestrTree` to the
underlying tree of `w` along `g`, re-establishing the index (`j'`, read from the
restricted root shape via `shapeRestr`) and hereditary naturality (preserved by
`wRestrTree`, a one-level consequence of `isHereditarilyNatural_mk` and
`reindex_naturality`). -/
@[expose] def wRestr {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j) :
    ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j ∧ F.IsHereditarilyNatural w } →
      ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j' ∧ F.IsHereditarilyNatural w } :=
  fun w ↦ ULift.up
    ⟨F.wRestrTree g w.down.1 w.down.2.1,
      F.windex_wRestrTree g w.down.1 w.down.2.1,
      F.isHereditarilyNatural_wRestrTree g w.down.1 w.down.2.1 w.down.2.2⟩

/-- Restriction along an identity fixes the tree: `objRestrElt_id` collapses the
rebuilt root, and `mk_dest` reassembles the original tree. -/
theorem wRestrTree_id {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j : I⦄
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.wRestrTree (𝟙 j) z hq = z := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    simp only [wRestrTree]
    rw [F.objRestrElt_id, SlicePFunctor.W.mk_dest]

/-- Restriction along a composite factors: `dest_mk` exposes the inner
restriction and `objRestrElt_comp` splits the rebuilt root. -/
theorem wRestrTree_comp {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' j'' : I⦄ (g : j' ⟶ j)
    (h : j'' ⟶ j') (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j)
    (hq2 : F.q (PFunctor.W.head (F.wRestrTree g z hq).1) = j') :
    F.wRestrTree (h ≫ g) z hq = F.wRestrTree h (F.wRestrTree g z hq) hq2 := by
  obtain ⟨tree, hvalid⟩ := z
  cases tree with
  | mk a fchild =>
    simp only [wRestrTree, SlicePFunctor.W.dest_mk]
    rw [F.objRestrElt_comp g h (SlicePFunctor.W.dest ⟨WType.mk a fchild, hvalid⟩) hq
      (F.shapeRestr g ⟨a, hq⟩).2]

/-- The carrier presheaf `W : Iᵒᵖ ⥤ Type` of the presheaf polynomial endofunctor
`F`: its fibre over `j` is the `ULift` of the hereditarily-natural slice W-trees
indexed at `j`, and its restriction maps are `wRestr`. The functor laws transport
from `objRestrElt_id` / `objRestrElt_comp` through `wRestrTree`, `ULift`, and
`Subtype`. -/
@[expose] def W {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : Iᵒᵖ ⥤ Type (max uI uA uB) where
  obj j := ULift.{uI} { w : F.toSlicePFunctor.W //
    F.toSlicePFunctor.windex w = j.unop ∧ F.IsHereditarilyNatural w }
  map g := ↾ (F.wRestr g.unop)
  map_id j := by
    ext w
    exact F.wRestrTree_id w.down.1 w.down.2.1
  map_comp g h := by
    ext w
    exact F.wRestrTree_comp g.unop h.unop w.down.1 w.down.2.1
      (F.windex_wRestrTree g.unop w.down.1 w.down.2.1)

namespace W

/-- Casting a carrier fibre element along an index equality leaves its
underlying slice W-tree unchanged. -/
private theorem cast_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {k k' : I} (e : k = k')
    (u : (F.W).obj ⟨k⟩) :
    (cast (congrArg (fun k : I ↦ (F.W).obj ⟨k⟩) e) u).down.1 = u.down.1 := by
  cases e
  rfl

/-- Two carrier fibre elements with equal underlying trees are equal. -/
private theorem obj_ext {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {k : I} {u u' : (F.W).obj ⟨k⟩}
    (h : u.down.1 = u'.down.1) : u = u' := by
  obtain ⟨u⟩ := u
  obtain ⟨u'⟩ := u'
  exact congrArg ULift.up (Subtype.ext h)

/-- The underlying tree of a restricted fibre element is the root-restriction of
the underlying tree. -/
private theorem map_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃i i' : I⦄ (f : i' ⟶ i)
    (u : (F.W).obj ⟨i⟩) :
    ((F.W).map f.op u).down.1 = F.wRestrTree f u.down.1 u.down.2.1 :=
  rfl

/-- The underlying tree of the value a presheaf node over `F.W` assigns to a
direction is the underlying tree of the carried child fibre element. -/
private theorem value_down {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction n.1.1 i) :
    (F.toPresheafDomPFunctorData.value n b).down.1 = (n.1.2 b.1).2.down.1 :=
  cast_down F
    (((F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) n.1.1 n.1.2).mp
      n.2 b.1).trans b.2)
    (n.1.2 b.1).2

/-- Rebuild a carrier fibre element from its underlying tree, its `windex`, and
its hereditary naturality: a total-space element over `windex w.down.1` equal to
the original total-space element over `i`. -/
private theorem sigma_eta {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) {i : I} (w : (F.W).obj ⟨i⟩) :
    (⟨F.toSlicePFunctor.windex w.down.1, ULift.up ⟨w.down.1, rfl, w.down.2.2⟩⟩ :
      Σ i : I, (F.W).obj ⟨i⟩) = ⟨i, w⟩ := by
  obtain ⟨⟨t, hi, hh⟩⟩ := w
  cases hi
  rfl

/-- Forget a presheaf node over the carrier presheaf `F.W` to the underlying
slice node over `windex`: retain the shape, and send each direction to the
underlying slice W-tree of its carried fibre element. -/
@[expose] def forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) :
    F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex :=
  ⟨⟨n.1.1, fun b ↦ (n.1.2 b).2.down.1⟩,
    (F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex _ _).mpr fun b ↦
      ((n.1.2 b).2.down.2.1).trans
        ((F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) _ _).mp
          n.2 b)⟩

/-- Remember a slice node over `windex` whose children are hereditarily natural
as a presheaf node over the carrier presheaf `F.W`: retain the shape, and send
each direction to the carried fibre element built from the child tree, its index
`windex`, and its hereditary naturality. -/
@[expose] def rememberNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (y : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex)
    (hchildren : ∀ b, F.IsHereditarilyNatural (y.1.2 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W)) :=
  ⟨⟨y.1.1, fun b ↦ ⟨F.toSlicePFunctor.windex (y.1.2 b),
      ULift.up ⟨y.1.2 b, rfl, hchildren b⟩⟩⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.W)) _ _).mpr fun b ↦
      (F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.windex _ _).mp y.2 b⟩

/-- `rememberNode` depends on the slice node only, not the hereditary-naturality
data (which occupies a `Prop` position). -/
private theorem rememberNode_eq {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    {y y' : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex}
    (hy : ∀ b, F.IsHereditarilyNatural (y.1.2 b))
    (hy' : ∀ b, F.IsHereditarilyNatural (y'.1.2 b)) (e : y = y') :
    rememberNode F y hy = rememberNode F y' hy' := by
  subst e
  rfl

/-- `forgetNode` inverts `rememberNode`. -/
private theorem forgetNode_rememberNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (y : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.windex)
    (hchildren : ∀ b, F.IsHereditarilyNatural (y.1.2 b)) :
    forgetNode F (rememberNode F y hchildren) = y := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := y
  rfl

/-- `rememberNode` inverts `forgetNode` (with the hereditary-naturality data
transported through the round trip). -/
private theorem rememberNode_forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W)))
    (hchildren : ∀ b, F.IsHereditarilyNatural ((forgetNode F n).1.2 b)) :
    rememberNode F (forgetNode F n) hchildren = n := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := n
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ sigma_eta F (v b).2))

/-- The hereditary naturality of the slice tree built from a presheaf node over
`F.W` is exactly the naturality of the node: the recursive conjunct of
`isHereditarilyNatural_mk` is discharged by the carried hereditary naturality of
each child, and its local conjunct matches the node's `IsNatural` datum through
the underlying-tree correspondence. -/
theorem isHereditarilyNatural_mk_forgetNode {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.W))) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk (forgetNode F n)) ↔
      F.toPresheafDomPFunctorData.IsNatural n := by
  rw [F.isHereditarilyNatural_mk]
  constructor
  · rintro ⟨hloc, -⟩ i i' f b
    apply obj_ext F
    simp only [value_down, map_down]
    exact hloc f b
  · intro hnat
    refine ⟨fun i i' g b ↦ ?_, fun b ↦ (n.1.2 b).2.down.2.2⟩
    have h := congrArg (fun u ↦ u.down.1) (hnat g b)
    simp only [value_down, map_down] at h
    exact h

/-- The fixed-point constructor of the presheaf W-type: the `objPresheaf`-value
at the carrier presheaf `F.W` maps into `F.W`, fibrewise over `I`. It builds the
slice W-tree from the node (via `forgetNode` and the slice constructor
`SlicePFunctor.W.mk`), reads its index from the node's `q`-output index, and
supplies hereditary naturality via `isHereditarilyNatural_mk_forgetNode`. -/
@[expose] def mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : (F.W).obj ⟨j⟩ :=
  ULift.up ⟨SlicePFunctor.W.mk (forgetNode F x.1.1), x.2,
    (isHereditarilyNatural_mk_forgetNode F x.1.1).mpr x.1.2⟩

/-- The fixed-point destructor of the presheaf W-type, inverse to `mk`: the
underlying tree decomposes (via the slice destructor `SlicePFunctor.W.dest`) as
a shape with a family of hereditarily-natural subtrees, reassembled (via
`rememberNode`) into a natural node over `F.W`, and re-indexed at the root's
`q`-output index. -/
@[expose] def dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : (F.objPresheaf F.W).obj ⟨j⟩ := by
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) := by
    rw [SlicePFunctor.W.mk_dest]
    exact z.down.2.2
  have hchildren := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest z.down.1)).mp hz).2
  exact ⟨⟨rememberNode F (SlicePFunctor.W.dest z.down.1) hchildren,
      (isHereditarilyNatural_mk_forgetNode F _).mp (by rw [forgetNode_rememberNode F]; exact hz)⟩,
    calc F.q (SlicePFunctor.W.dest z.down.1).1.1
        = F.toSlicePFunctor.windex (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) :=
          (SlicePFunctor.W.windex_mk (SlicePFunctor.W.dest z.down.1)).symm
      _ = F.toSlicePFunctor.windex z.down.1 := by rw [SlicePFunctor.W.mk_dest]
      _ = j := z.down.2.1⟩

/-- `dest` is a left inverse of `mk`. -/
@[simp]
theorem dest_mk {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : dest (mk x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (F := F.toSlicePFunctor)
      (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
        (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1)))) := by
    rw [SlicePFunctor.W.mk_dest]
    exact (isHereditarilyNatural_mk_forgetNode F x.1.1).mpr x.1.2
  have hch := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
    (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1)))).mp hz).2
  change rememberNode F (SlicePFunctor.W.dest (F := F.toSlicePFunctor)
    (SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F x.1.1))) hch = x.1.1
  have hy' : ∀ b, F.IsHereditarilyNatural ((forgetNode F x.1.1).1.2 b) :=
    fun b ↦ (x.1.1.1.2 b).2.down.2.2
  exact (rememberNode_eq F hch hy'
    (SlicePFunctor.W.dest_mk (F := F.toSlicePFunctor) (forgetNode F x.1.1))).trans
    (rememberNode_forgetNode F x.1.1 hy')

/-- `mk` is a left inverse of `dest`; with `dest_mk`, `mk` and `dest` are
mutually inverse, so `F.W` is a fixed point of the `objPresheaf`-action at
`F.W`. -/
@[simp]
theorem mk_dest {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : mk (dest z) = z := by
  have hz : F.IsHereditarilyNatural (SlicePFunctor.W.mk (SlicePFunctor.W.dest z.down.1)) := by
    rw [SlicePFunctor.W.mk_dest]
    exact z.down.2.2
  have hch := ((F.isHereditarilyNatural_mk (SlicePFunctor.W.dest z.down.1)).mp hz).2
  apply obj_ext F
  change SlicePFunctor.W.mk (F := F.toSlicePFunctor) (forgetNode F
    (rememberNode F (SlicePFunctor.W.dest (F := F.toSlicePFunctor) z.down.1) hch)) = z.down.1
  rw [forgetNode_rememberNode, SlicePFunctor.W.mk_dest]

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
@[expose] def pnodeSlice {I : Type uI} [Category.{vI} I]
    {F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I}
    {Y : Iᵒᵖ ⥤ Type (max uI uA uB)} {a : F.toPFunctor.A}
    (c : F.toPFunctor.B a → PElimData F Y)
    (hv : F.toSlicePFunctor.NodeValid a (fun b ↦ (c b).toWIndex))
    (hc : ∀ b, (c b).H (hv.1 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Y) :=
  ⟨⟨a, fun b ↦ (c b).value (hv.1 b) (hc b)⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj Y) a _).mpr
      fun b ↦ ((c b).over (hv.1 b) (hc b)).trans (congrFun hv.2 b)⟩

/-- The value-fold algebra step: index and admissibility as for `windexStep`; a
hereditary-naturality proxy `H` combining the children's proxies with the
naturality of the assembled node (`pnodeSlice`); and a value that applies the
presheaf algebra `α` to that node, packaged over the shape's `q`-output index. -/
@[expose] def pelimStep {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) :
    F.toPFunctor.Obj (PElimData F Y) → PElimData F Y :=
  fun x ↦
    { index := F.q x.1
      valid := F.toSlicePFunctor.NodeValid x.1 (fun b ↦ (x.2 b).toWIndex)
      H := fun hv ↦ (∀ b, (x.2 b).H (hv.1 b)) ∧
        (∀ hc : (∀ b, (x.2 b).H (hv.1 b)), F.IsNatural (pnodeSlice x.2 hv hc))
      value := fun hv hn ↦
        ⟨F.q x.1, α.app ⟨F.q x.1⟩ ⟨⟨pnodeSlice x.2 hv hn.1, hn.2 hn.1⟩, rfl⟩⟩
      over := fun _ _ ↦ rfl }

/-- The value fold: the `F.toPFunctor`-algebra morphism into
`(PElimData F Y, pelimStep)` given by `WType.elim`, a single non-dependent fold
with no explicit recursion. -/
@[expose] def pelimData {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) :
    F.toPFunctor.W → PElimData F Y :=
  WType.elim (PElimData F Y) (pelimStep F Y α)

/-- The index-and-admissibility projection of `pelimData` agrees with the slice
fold `windexValid`: the value fold refines the slice fold, so admissibility and
the root index transport from the slice results. Proved by the dependent
recursor `WType.rec`. -/
theorem pelimData_toWIndex {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pelimData F Y α w).toWIndex = F.windexValid w :=
  WType.rec (motive := fun w ↦ (pelimData F Y α w).toWIndex = F.windexValid w)
    (fun a f ih ↦ by
      change F.windexStep ⟨a, fun b ↦ (pelimData F Y α (f b)).toWIndex⟩ =
        F.windexStep ⟨a, fun b ↦ F.windexValid (f b)⟩
      rw [funext ih])
    w

/-- The admissibility component of `pelimData` is `WValid`. -/
theorem pelimData_valid {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pelimData F Y α w).valid = F.WValid w :=
  congrArg SlicePFunctor.WIndex.valid (pelimData_toWIndex F Y α w)

/-- The index component of `pelimData` is the root index. -/
theorem pelimData_index {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) (w : F.toPFunctor.W) :
    (pelimData F Y α w).index = F.windexRoot w :=
  (congrArg SlicePFunctor.WIndex.index (pelimData_toWIndex F Y α w)).trans
    (F.windexValid_index_eq_windexRoot w)

/-- A natural transformation's components respect heterogeneous equality of
fibre elements over equal indices. -/
private theorem app_heq.{w} {I : Type uI} [Category.{vI} I]
    {Z Z' : Iᵒᵖ ⥤ Type w} (β : NatTrans Z Z') {k k' : I} (hk : k = k')
    {x : Z.obj ⟨k⟩} {x' : Z.obj ⟨k'⟩} (hx : x ≍ x') :
    β.app ⟨k⟩ x ≍ β.app ⟨k'⟩ x' := by
  cases hk
  cases hx
  rfl

/-- Two fibre elements of `objPresheaf Y` over equal indices whose underlying
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
    (hv : (pelimData F Y α t.1).valid) (hn : (pelimData F Y α t.1).H hv)
    (hv' : (pelimData F Y α (F.wRestrTree f t hqi).1).valid)
    (hn' : (pelimData F Y α (F.wRestrTree f t hqi).1).H hv') :
    (pelimData F Y α (F.wRestrTree f t hqi).1).value hv' hn' =
      ⟨i', Y.map f.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
          (((pelimData F Y α t.1).over hv hn).trans
            ((pelimData_index F Y α t.1).trans hqi)))
        ((pelimData F Y α t.1).value hv hn).2)⟩ := by
  obtain ⟨tree, hval⟩ := t
  cases tree with
  | mk a fchild =>
    refine Sigma.ext (F.shapeRestr f ⟨a, hqi⟩).2 ?_
    have hqa : F.q a = i := hqi
    subst hqa
    have hnat :
        Y.map f.op (α.app ⟨F.q a⟩ (⟨⟨pnodeSlice (fun b ↦ pelimData F Y α (fchild b)) hv hn.1,
            hn.2 hn.1⟩, rfl⟩ : (F.objPresheaf Y).obj ⟨F.q a⟩)) =
          α.app ⟨i'⟩ ((F.objPresheaf Y).map f.op
            ⟨⟨pnodeSlice (fun b ↦ pelimData F Y α (fchild b)) hv hn.1, hn.2 hn.1⟩, rfl⟩) := by
      exact (FunctorToTypes.naturality _ _ α f.op _).symm
    change (α.app ⟨F.q (F.shapeRestr f ⟨a, hqi⟩).1⟩
          (⟨⟨F.objRestrElt f (pnodeSlice (fun b ↦ pelimData F Y α (fchild b)) hv hn.1) hqi,
            hn'.2 hn'.1⟩, rfl⟩ : (F.objPresheaf Y).obj ⟨F.q (F.shapeRestr f ⟨a, hqi⟩).1⟩)) ≍
        Y.map f.op (α.app ⟨F.q a⟩
          (⟨⟨pnodeSlice (fun b ↦ pelimData F Y α (fchild b)) hv hn.1, hn.2 hn.1⟩, rfl⟩ :
            (F.objPresheaf Y).obj ⟨F.q a⟩))
    rw [hnat]
    exact app_heq α (F.shapeRestr f ⟨a, hqi⟩).2
      (objPresheaf_obj_heq F Y (F.shapeRestr f ⟨a, hqi⟩).2 (Subtype.ext rfl))

/-- The node the value fold assembles at a slice node whose children are folds of
hereditarily-natural subtrees is natural: local naturality of the enclosing tree
(each child restricting to the child at the reindexed direction) transports
through the fold's value-restriction coherence `value_wRestrTree`. -/
private theorem isNatural_pnodeSlice {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y)
    {a : F.toPFunctor.A} (fc : F.toPFunctor.B a → F.toSlicePFunctor.W)
    (hv : F.toSlicePFunctor.NodeValid a (fun b ↦ (pelimData F Y α (fc b).1).toWIndex))
    (hc : ∀ b, (pelimData F Y α (fc b).1).H (hv.1 b))
    (hloc : ∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction a i)
        (hq : F.q (PFunctor.W.head (fc b.1).1) = i),
        fc (F.directionRestr a g b).1 = F.wRestrTree g (fc b.1) hq) :
    F.IsNatural (pnodeSlice (fun b ↦ pelimData F Y α (fc b).1) hv hc) := by
  intro i i' g b
  change F.value (pnodeSlice (fun b ↦ pelimData F Y α (fc b).1) hv hc) (F.directionRestr a g b) =
    Y.map g.op (F.value (pnodeSlice (fun b ↦ pelimData F Y α (fc b).1) hv hc) b)
  have hqit : F.q (PFunctor.W.head (fc b.1).1) = i :=
    (pelimData_index F Y α (fc b.1).1).symm.trans ((congrFun hv.2 b.1).trans b.2)
  have hgen : ∀ (T : F.toSlicePFunctor.W) (hvT : (pelimData F Y α T.1).valid)
      (hnT : (pelimData F Y α T.1).H hvT), T = F.wRestrTree g (fc b.1) hqit →
      (pelimData F Y α T.1).value hvT hnT =
        ⟨i', Y.map g.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
            (((pelimData F Y α (fc b.1).1).over (hv.1 b.1) (hc b.1)).trans
              ((pelimData_index F Y α (fc b.1).1).trans hqit)))
          ((pelimData F Y α (fc b.1).1).value (hv.1 b.1) (hc b.1)).2)⟩ := by
    intro T hvT hnT hT
    subst hT
    exact value_wRestrTree F Y α (fc b.1) g hqit (hv.1 b.1) (hc b.1) hvT hnT
  have hchild :
      (pnodeSlice (fun b ↦ pelimData F Y α (fc b).1) hv hc).1.2
          (F.directionRestr a g b).1 =
        ⟨i', Y.map g.op (cast (congrArg (fun k : I ↦ Y.obj ⟨k⟩)
            (((pelimData F Y α (fc b.1).1).over (hv.1 b.1) (hc b.1)).trans
              ((pelimData_index F Y α (fc b.1).1).trans hqit)))
          ((pelimData F Y α (fc b.1).1).value (hv.1 b.1) (hc b.1)).2)⟩ :=
    hgen (fc (F.directionRestr a g b).1) (hv.1 (F.directionRestr a g b).1)
      (hc (F.directionRestr a g b).1) (hloc g b hqit)
  simp only [PresheafDomPFunctorData.value]
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  rw [hchild]
  rfl

/-- The node the value fold assembles at a validated hereditarily-natural tree,
as an element of the output presheaf's fibre over the root index: the shape and
the children's fold values, natural by the tree's hereditary naturality. -/
theorem pelimData_H_of_isHN {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y)
    (w : F.toSlicePFunctor.W) (hv : (pelimData F Y α w.1).valid)
    (hn : F.IsHereditarilyNatural w) : (pelimData F Y α w.1).H hv :=
  SlicePFunctor.W.ind
    (motive := fun z ↦ ∀ (hv : (pelimData F Y α z.1).valid),
      F.IsHereditarilyNatural z → (pelimData F Y α z.1).H hv)
    (fun x ih hv hHN ↦ by
      refine ⟨fun b ↦ ih b (hv.1 b) (((F.isHereditarilyNatural_mk x).mp hHN).2 b), fun _ ↦ ?_⟩
      exact isNatural_pnodeSlice F Y α x.1.2 hv
        (fun b ↦ ih b (hv.1 b) (((F.isHereditarilyNatural_mk x).mp hHN).2 b))
        (fun _ _ g b _ ↦ ((F.isHereditarilyNatural_mk x).mp hHN).1 g b))
    w hv hn

/-- The fibre value the fold contributes to a validated hereditarily-natural
tree indexed at `j`: the total-space value's `Y`-component, transported to the
fibre over `j` through the fold's `over` law and root-index agreement. -/
@[expose] def elimVal {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) {j : I}
    (z : (F.W).obj ⟨j⟩) : Y.obj ⟨j⟩ :=
  cast (congrArg (fun i : I ↦ Y.obj ⟨i⟩)
      ((((pelimData F Y α z.down.1.1).over
          ((pelimData_valid F Y α z.down.1.1) ▸ z.down.1.2)
          (pelimData_H_of_isHN F Y α z.down.1
            ((pelimData_valid F Y α z.down.1.1) ▸ z.down.1.2) z.down.2.2)).trans
        (pelimData_index F Y α z.down.1.1)).trans z.down.2.1))
    ((pelimData F Y α z.down.1.1).value
      ((pelimData_valid F Y α z.down.1.1) ▸ z.down.1.2)
      (pelimData_H_of_isHN F Y α z.down.1
        ((pelimData_valid F Y α z.down.1.1) ▸ z.down.1.2) z.down.2.2)).2

/-- The total-space fold value at a carrier element is `elimVal` paired with the
index: the `Y`-component is `elimVal` and the base point is the fibre index.
Proof-irrelevance identifies the fold's internal hereditary-naturality proof with
any supplied one. -/
theorem value_eq_elimVal {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) {j : I}
    (z : (F.W).obj ⟨j⟩) (hv : (pelimData F Y α z.down.1.1).valid)
    (hn : (pelimData F Y α z.down.1.1).H hv) :
    (pelimData F Y α z.down.1.1).value hv hn = ⟨j, elimVal F Y α z⟩ := by
  refine Sigma.ext (((((pelimData F Y α z.down.1.1).over hv hn).trans
    (pelimData_index F Y α z.down.1.1)).trans z.down.2.1)) ?_
  exact (cast_heq _ _).symm

/-- `elimVal` commutes with the restriction maps: the value of a restricted
carrier element is the `Y`-restriction of the value. It glues the fold-level
restriction coherence `value_wRestrTree` (the one-level argument, combining the
fold's one-level computation with `α`'s naturality) with `value_eq_elimVal`,
which identifies the two total-space fold values' fibre components with the two
`elimVal`s; the tree recursion is confined to `pelimData_H_of_isHN`. -/
theorem elimVal_wRestr {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : NatTrans (F.objPresheaf Y) Y) ⦃i i' : I⦄
    (g : i' ⟶ i) (z : (F.W).obj ⟨i⟩) :
    elimVal F Y α ((F.W).map g.op z) = Y.map g.op (elimVal F Y α z) := by
  have hvz : (pelimData F Y α z.down.1.1).valid :=
    (pelimData_valid F Y α z.down.1.1) ▸ z.down.1.2
  have hnz : (pelimData F Y α z.down.1.1).H hvz :=
    pelimData_H_of_isHN F Y α z.down.1 hvz z.down.2.2
  have hvzr : (pelimData F Y α ((F.W).map g.op z).down.1.1).valid :=
    (pelimData_valid F Y α ((F.W).map g.op z).down.1.1) ▸ ((F.W).map g.op z).down.1.2
  have hnzr : (pelimData F Y α ((F.W).map g.op z).down.1.1).H hvzr :=
    pelimData_H_of_isHN F Y α ((F.W).map g.op z).down.1 hvzr ((F.W).map g.op z).down.2.2
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

/-- `elim` is a genuine presheaf morphism: it commutes with the restriction
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
  have hv : (pelimData F Y α (mk x).down.1.1).valid :=
    (pelimData_valid F Y α (mk x).down.1.1) ▸ (mk x).down.1.2
  have hn : (pelimData F Y α (mk x).down.1.1).H hv :=
    pelimData_H_of_isHN F Y α (mk x).down.1 hv (mk x).down.2.2
  have hq : F.q x.1.1.1.1 = j := x.2
  have hchild : ∀ b, (pelimData F Y α (x.1.1.1.2 b).2.down.1.1).value (hv.1 b) (hn.1 b)
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

end PresheafPFunctor
