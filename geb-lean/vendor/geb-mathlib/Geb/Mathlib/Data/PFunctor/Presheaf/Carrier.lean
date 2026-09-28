/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.FixedPoint

set_option doc.verso true

/-!
# Carrier presheaves of presheaf polynomial endofunctors

For a presheaf polynomial endofunctor {lit}`F : PresheafPFunctor I I`, a carrier
presheaf of trees is built on a fixed point {lit}`S` of the underlying slice
endofunctor ({name}`SlicePFunctor.FixedPoint`) and a predicate on its elements,
hereditary naturality. A tree is restricted along a morphism of {lit}`I` at its
root only: the root node is restricted by
{name}`PresheafPFunctor.objRestrElt`, conjugated by the fixed point's
destructor and constructor. A node is natural when restricting the child at a
direction agrees with the child at the restricted direction, and hereditary
naturality is any predicate satisfying the unfolding equation: it holds at a
tree exactly when the root node is natural and it holds at every child. The
carrier presheaf's fibre over {lit}`j` is the hereditarily natural trees
indexed at {lit}`j`, and it is a fixed point of
{name}`PresheafPFunctor.objPresheaf`.

The W-type of {lit}`F` and its M-type are instances: the slice W-type with
hereditary naturality defined by an inductive fold, and the slice M-type with
hereditary naturality defined coinductively. Every construction here uses only
the fixed-point structure and the unfolding equation, so it is stated once for
both.

## Main definitions

* {lit}`PresheafPFunctor.restrTree` — the root-only restriction of a tree along
  a morphism.
* {lit}`PresheafPFunctor.NodeNatural` — naturality of a node of trees.
* {lit}`PresheafPFunctor.HereditaryNaturality` — a predicate satisfying the
  unfolding equation of hereditary naturality.
* {lit}`PresheafPFunctor.carrier` — the carrier presheaf of the hereditarily
  natural trees.
* {lit}`PresheafPFunctor.carrier.forgetNode`,
  {lit}`PresheafPFunctor.carrier.rememberNode` — the translations between a node
  over the carrier presheaf and a node of hereditarily natural trees.
* {lit}`PresheafPFunctor.carrier.mk`, {lit}`PresheafPFunctor.carrier.dest` —
  the constructor and destructor, fibrewise.
* {lit}`PresheafPFunctor.carrier.destNat`, {lit}`PresheafPFunctor.carrier.mkNat`
  — the two as natural transformations.

## Main statements

* {lit}`PresheafPFunctor.index_restrTree`, {lit}`PresheafPFunctor.restrTree_id`,
  {lit}`PresheafPFunctor.restrTree_comp` — the restriction lies over its target
  and is functorial.
* {lit}`PresheafPFunctor.HereditaryNaturality.holds_restrTree` — hereditary
  naturality is preserved by restriction.
* {lit}`PresheafPFunctor.carrier.nodeNatural_forgetNode` — a node over the
  carrier presheaf is natural exactly when the node of trees it carries is.
* {lit}`PresheafPFunctor.carrier.dest_mk`, {lit}`PresheafPFunctor.carrier.mk_dest`,
  {lit}`PresheafPFunctor.carrier.mk_map`, {lit}`PresheafPFunctor.carrier.dest_map`
  — the constructor and destructor are mutually inverse and commute with
  restriction.

## Implementation notes

The inverse laws of {lit}`carrier.destNat` and {lit}`carrier.mkNat` are stated
componentwise, by {lit}`carrier.dest_mk` and {lit}`carrier.mk_dest`, rather than
through {name}`CategoryTheory.NatTrans.vcomp` or an isomorphism in the
functor category, whose definitions depend on {name}`Classical.choice`. The
fixed point's carrier lies in the universe of the polynomial's shapes and
directions, as the W-type's and the M-type's do, so that the carrier presheaf
and its image under {name}`PresheafPFunctor.objPresheaf` lie in one category.

## References

* \[Weber2007\]
* \[GambinoKock2013\]

## Tags

polynomial functor, presheaf, parametric right adjoint, fixed point,
naturality, restriction map
-/

@[expose] public section

open CategoryTheory

universe uI uA uB vI

namespace PresheafPFunctor

variable {I : Type uI} [Category.{vI} I] (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
  (S : SlicePFunctor.FixedPoint.{max uA uB} F.toSlicePFunctor)

/-! ## Root restriction and naturality -/

/-- The output index of a tree's root shape is its index. -/
theorem q_dest (t : S.T) : F.q (S.dest t).1.1 = S.index t :=
  S.obj_dest t

/-- The root-only restriction of a tree {lit}`t` indexed at {lit}`j` along a
morphism {lit}`g : j' ⟶ j`: restrict the root node by
{name}`PresheafPFunctor.objRestrElt`, conjugated by the destructor and
constructor. -/
def restrTree ⦃j j' : I⦄ (g : j' ⟶ j) (t : S.T) (hq : S.index t = j) : S.T :=
  S.mk (F.objRestrElt g (S.dest t) ((F.q_dest S t).trans hq))

/-- The index of a root-restricted tree is the source of the morphism. -/
theorem index_restrTree ⦃j j' : I⦄ (g : j' ⟶ j) (t : S.T) (hq : S.index t = j) :
    S.index (F.restrTree S g t hq) = j' :=
  (S.index_mk _).trans (F.shapeRestr g ⟨(S.dest t).1.1, (F.q_dest S t).trans hq⟩).2

/-- Restriction along an identity fixes the tree. -/
theorem restrTree_id ⦃j : I⦄ (t : S.T) (hq : S.index t = j) : F.restrTree S (𝟙 j) t hq = t := by
  simp only [restrTree]
  rw [F.objRestrElt_id]
  exact S.mk_dest t

/-- Restriction along a composite is the composite of the restrictions. -/
theorem restrTree_comp ⦃j j' j'' : I⦄ (g : j' ⟶ j) (h : j'' ⟶ j') (t : S.T)
    (hq : S.index t = j) (hq2 : S.index (F.restrTree S g t hq) = j') :
    F.restrTree S (h ≫ g) t hq = F.restrTree S h (F.restrTree S g t hq) hq2 := by
  simp only [restrTree, S.dest_mk]
  rw [F.objRestrElt_comp g h (S.dest t) ((F.q_dest S t).trans hq)
    (F.shapeRestr g ⟨(S.dest t).1.1, (F.q_dest S t).trans hq⟩).2]

/-- {name}`restrTree` respects equality of trees; the index witnesses are
proof-irrelevant. -/
theorem restrTree_congr ⦃j j' : I⦄ (g : j' ⟶ j) {t t' : S.T} (ht : t = t')
    (hq : S.index t = j) (hq' : S.index t' = j) :
    F.restrTree S g t hq = F.restrTree S g t' hq' := by
  subst ht
  rfl

/-- The root restriction of a tree is the constructor applied to the
restriction of any node equal to the tree's root node. -/
private theorem restrTree_eq_mk ⦃j j' : I⦄ (g : j' ⟶ j) (t : S.T) (hq : S.index t = j)
    (y : F.toSliceDomPFunctor.Obj S.index) (hy : S.dest t = y) (hy' : F.q y.1.1 = j) :
    F.restrTree S g t hq = S.mk (F.objRestrElt g y hy') := by
  subst hy
  rfl

/-- Restricting a constructed tree restricts its root node. -/
theorem restrTree_mk ⦃j j' : I⦄ (g : j' ⟶ j) (x : F.toSliceDomPFunctor.Obj S.index)
    (hq : S.index (S.mk x) = j) (hx : F.q x.1.1 = j) :
    F.restrTree S g (S.mk x) hq = S.mk (F.objRestrElt g x hx) :=
  restrTree_eq_mk F S g (S.mk x) hq x (S.dest_mk x) hx

/-- Naturality of a node of trees: restricting the child at a direction along a
morphism agrees with the child at the restricted direction. The analogue for
trees of {name}`PresheafDomPFunctorData.IsNatural`. -/
def NodeNatural (x : F.toSliceDomPFunctor.Obj S.index) : Prop :=
  ∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
    x.1.2 (F.directionRestr x.1.1 g b).1 =
      F.restrTree S g (x.1.2 b.1)
        (((F.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2 b.1).trans b.2)

/-- Restricting a natural node gives a natural node: its children are the
original children at the reindexed directions, and naturality transports
along {name}`PresheafPFunctorData.IsFunctorial.reindex_naturality`. -/
theorem nodeNatural_objRestrElt ⦃j j' : I⦄ (g : j' ⟶ j) (x : F.toSliceDomPFunctor.Obj S.index)
    (hq : F.q x.1.1 = j) (hx : F.NodeNatural S x) : F.NodeNatural S (F.objRestrElt g x hq) := by
  intro i i' h b
  obtain ⟨bv, rfl⟩ := b
  refine (F.snd_objRestrElt g x hq _).trans ?_
  have hr := congrFun (F.isFunctorial.reindex_naturality g ⟨x.1.1, hq⟩ h) ⟨bv, rfl⟩
  exact (congrArg (fun d : F.toSliceDomPFunctor.Direction x.1.1 _ ↦ x.1.2 d.1) hr.symm).trans
    (hx h (F.reindex g ⟨x.1.1, hq⟩ ⟨bv, rfl⟩))

/-! ## Hereditary naturality -/

/-- A predicate on the trees of {lit}`S` satisfying the unfolding equation of
hereditary naturality: it holds at a tree exactly when the root node is natural
and it holds at every child. -/
structure HereditaryNaturality : Type (max uA uB + 1) where
  /-- The predicate. -/
  holds : S.T → Prop
  /-- The unfolding equation. -/
  holds_iff : ∀ t, holds t ↔ F.NodeNatural S (S.dest t) ∧ ∀ b, holds ((S.dest t).1.2 b)

namespace HereditaryNaturality

variable {F S} (N : F.HereditaryNaturality S)

/-- The unfolding equation at a constructed tree. -/
theorem holds_mk (x : F.toSliceDomPFunctor.Obj S.index) :
    N.holds (S.mk x) ↔ F.NodeNatural S x ∧ ∀ b, N.holds (x.1.2 b) := by
  rw [N.holds_iff, S.dest_mk]

/-- Hereditary naturality is preserved by the root-only restriction: the
restricted children are original children, and the restricted root node is
natural by {name}`nodeNatural_objRestrElt`. -/
theorem holds_restrTree ⦃j j' : I⦄ (g : j' ⟶ j) (t : S.T) (hq : S.index t = j)
    (ht : N.holds t) : N.holds (F.restrTree S g t hq) := by
  obtain ⟨hloc, hch⟩ := (N.holds_iff t).mp ht
  exact (N.holds_mk _).mpr ⟨F.nodeNatural_objRestrElt S g (S.dest t) _ hloc,
    fun b ↦ hch (F.reindex g ⟨_, (F.q_dest S t).trans hq⟩ ⟨b, rfl⟩).1⟩

end HereditaryNaturality

/-! ## The carrier presheaf -/

variable {S} (N : F.HereditaryNaturality S)

/-- The fibre of the carrier presheaf over {lit}`j`: the hereditarily natural
trees indexed at {lit}`j`, lifted to the universe of {lit}`I`. -/
abbrev carrierFiber (j : I) : Type (max uI uA uB) :=
  ULift.{uI} { t : S.T // S.index t = j ∧ N.holds t }

/-- Restriction on fibres. -/
def carrierRestr ⦃j j' : I⦄ (g : j' ⟶ j) : F.carrierFiber N j → F.carrierFiber N j' :=
  fun w ↦ ULift.up ⟨F.restrTree S g w.down.1 w.down.2.1,
    F.index_restrTree S g w.down.1 w.down.2.1, N.holds_restrTree g w.down.1 w.down.2.1 w.down.2.2⟩

/-- The carrier presheaf of the hereditarily natural trees: its fibre over
{lit}`j` is {name}`carrierFiber`, and its restriction maps are
{name}`carrierRestr`. -/
def carrier : Iᵒᵖ ⥤ Type (max uI uA uB) where
  obj j := F.carrierFiber N j.unop
  map g := ↾ (F.carrierRestr N g.unop)
  map_id j := by
    ext w
    exact F.restrTree_id S w.down.1 w.down.2.1
  map_comp g h := by
    ext w
    exact F.restrTree_comp S g.unop h.unop w.down.1 w.down.2.1
      (F.index_restrTree S g.unop w.down.1 w.down.2.1)

namespace carrier

variable {F N}

/-- Casting a fibre element along an index equality leaves its tree
unchanged. -/
private theorem cast_down {k k' : I} (e : k = k') (u : (F.carrier N).obj ⟨k⟩) :
    (cast (congrArg (fun k : I ↦ (F.carrier N).obj ⟨k⟩) e) u).down.1 = u.down.1 := by
  cases e
  rfl

/-- Fibre elements with equal trees are equal. -/
theorem obj_ext {k : I} {u u' : (F.carrier N).obj ⟨k⟩} (h : u.down.1 = u'.down.1) : u = u' := by
  obtain ⟨u⟩ := u
  obtain ⟨u'⟩ := u'
  exact congrArg ULift.up (Subtype.ext h)

/-- The tree of a restricted fibre element is the root restriction of its
tree. -/
theorem map_down ⦃i i' : I⦄ (f : i' ⟶ i) (u : (F.carrier N).obj ⟨i⟩) :
    ((F.carrier N).map f.op u).down.1 = F.restrTree S f u.down.1 u.down.2.1 :=
  rfl

/-- The tree of the value a node over the carrier presheaf gives a direction
is the tree of the child it carries. -/
theorem value_down
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.carrier N))) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Direction n.1.1 i) :
    (F.toPresheafDomPFunctorData.value n b).down.1 = (n.1.2 b.1).2.down.1 :=
  cast_down (((F.toSliceDomPFunctor.compatible_iff
    (PresheafDomPFunctorData.elemProj (F.carrier N)) n.1.1 n.1.2).mp n.2 b.1).trans b.2)
    (n.1.2 b.1).2

/-- A fibre element is its tree placed over the tree's index. -/
theorem sigma_eta {i : I} (w : (F.carrier N).obj ⟨i⟩) :
    (⟨S.index w.down.1, ULift.up ⟨w.down.1, rfl, w.down.2.2⟩⟩ :
      Σ i : I, (F.carrier N).obj ⟨i⟩) = ⟨i, w⟩ := by
  obtain ⟨⟨t, hi, hh⟩⟩ := w
  cases hi
  rfl

/-- Forget a node over the carrier presheaf to the node of trees it carries. -/
def forgetNode (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.carrier N))) :
    F.toSliceDomPFunctor.Obj S.index :=
  ⟨⟨n.1.1, fun b ↦ (n.1.2 b).2.down.1⟩,
    (F.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b ↦
      ((n.1.2 b).2.down.2.1).trans ((F.toSliceDomPFunctor.compatible_iff
        (PresheafDomPFunctorData.elemProj (F.carrier N)) _ _).mp n.2 b)⟩

/-- Remember a node of hereditarily natural trees as a node over the carrier
presheaf, each child placed over its own index. -/
def rememberNode (y : F.toSliceDomPFunctor.Obj S.index) (hch : ∀ b, N.holds (y.1.2 b)) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.carrier N)) :=
  ⟨⟨y.1.1, fun b ↦ ⟨S.index (y.1.2 b), ULift.up ⟨y.1.2 b, rfl, hch b⟩⟩⟩,
    (F.toSliceDomPFunctor.compatible_iff (PresheafDomPFunctorData.elemProj (F.carrier N)) _ _).mpr
      fun b ↦ (F.toSliceDomPFunctor.compatible_iff _ _ _).mp y.2 b⟩

/-- {name}`rememberNode` depends on the node only. -/
theorem rememberNode_congr {y y' : F.toSliceDomPFunctor.Obj S.index} (e : y = y')
    (hy : ∀ b, N.holds (y.1.2 b)) (hy' : ∀ b, N.holds (y'.1.2 b)) :
    rememberNode y hy = rememberNode y' hy' := by
  subst e
  rfl

/-- {name}`forgetNode` inverts {name}`rememberNode`. -/
theorem forgetNode_rememberNode (y : F.toSliceDomPFunctor.Obj S.index)
    (hch : ∀ b, N.holds (y.1.2 b)) : forgetNode (rememberNode y hch) = y :=
  rfl

/-- {name}`rememberNode` inverts {name}`forgetNode`. -/
theorem rememberNode_forgetNode
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.carrier N)))
    (hch : ∀ b, N.holds ((forgetNode n).1.2 b)) :
    rememberNode (forgetNode n) hch = n := by
  apply Subtype.ext
  obtain ⟨⟨a, v⟩, hc⟩ := n
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ sigma_eta (v b).2))

/-- A node over the carrier presheaf is natural exactly when the node of trees
it carries is. -/
theorem nodeNatural_forgetNode
    (n : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj (F.carrier N))) :
    F.NodeNatural S (forgetNode n) ↔ F.toPresheafDomPFunctorData.IsNatural n := by
  constructor
  · intro hloc i i' f b
    apply obj_ext
    simp only [value_down, map_down]
    exact hloc f b
  · intro hnat i i' g b
    have h := congrArg (fun u ↦ u.down.1) (hnat g b)
    simp only [value_down n, map_down g] at h
    exact h

/-- The constructor: the value of {name}`PresheafPFunctor.objPresheaf` at the
carrier presheaf maps into it, fibrewise. -/
def mk {j : I} (x : (F.objPresheaf (F.carrier N)).obj ⟨j⟩) : (F.carrier N).obj ⟨j⟩ :=
  ULift.up ⟨S.mk (forgetNode x.1.1), (S.index_mk _).trans x.2,
    (N.holds_mk _).mpr ⟨(nodeNatural_forgetNode x.1.1).mpr x.1.2,
      fun b ↦ (x.1.1.1.2 b).2.down.2.2⟩⟩

/-- The destructor, inverse to {name}`mk`: the root node of the tree, its
children placed over their indices. -/
def dest {j : I} (z : (F.carrier N).obj ⟨j⟩) : (F.objPresheaf (F.carrier N)).obj ⟨j⟩ :=
  ⟨⟨rememberNode (S.dest z.down.1) ((N.holds_iff z.down.1).mp z.down.2.2).2,
      (nodeNatural_forgetNode _).mp ((N.holds_iff z.down.1).mp z.down.2.2).1⟩,
    (F.q_dest S z.down.1).trans z.down.2.1⟩

/-- The destructor inverts the constructor. -/
@[simp] theorem dest_mk {j : I} (x : (F.objPresheaf (F.carrier N)).obj ⟨j⟩) :
    dest (mk x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact (rememberNode_congr (S.dest_mk _) ((N.holds_iff (mk x).down.1).mp (mk x).down.2.2).2
    fun b ↦ (x.1.1.1.2 b).2.down.2.2).trans (rememberNode_forgetNode x.1.1 _)

/-- The constructor inverts the destructor. -/
@[simp] theorem mk_dest {j : I} (z : (F.carrier N).obj ⟨j⟩) : mk (dest z) = z :=
  obj_ext (S.mk_dest z.down.1)

/-- The constructor commutes with restriction: restricting a node and then
constructing is constructing and then restricting the root. -/
theorem mk_map ⦃i i' : I⦄ (g : i' ⟶ i) (x : (F.objPresheaf (F.carrier N)).obj ⟨i⟩) :
    mk ((F.objPresheaf (F.carrier N)).map g.op x) = (F.carrier N).map g.op (mk x) :=
  obj_ext (F.restrTree_mk S g (forgetNode x.1.1) (mk x).down.2.1 x.2).symm

/-- The destructor commutes with restriction. -/
theorem dest_map ⦃i i' : I⦄ (g : i' ⟶ i) (z : (F.carrier N).obj ⟨i⟩) :
    dest ((F.carrier N).map g.op z) = (F.objPresheaf (F.carrier N)).map g.op (dest z) :=
  (congrArg (fun w ↦ dest ((F.carrier N).map g.op w)) (mk_dest z).symm).trans
    ((congrArg dest (mk_map g (dest z)).symm).trans (dest_mk _))

variable (N) in
/-- The destructor as a natural transformation: the structure map making the
carrier presheaf a coalgebra of {name}`PresheafPFunctor.objPresheaf`. -/
def destNat : NatTrans (F.carrier N) (F.objPresheaf (F.carrier N)) where
  app j := ↾ fun z ↦ dest (j := j.unop) z
  naturality _ _ g := by
    ext z
    exact dest_map g.unop z

variable (N) in
/-- The constructor as a natural transformation. With {name}`destNat`, it
exhibits the carrier presheaf as a fixed point of
{name}`PresheafPFunctor.objPresheaf`, their components being mutually inverse
by {name}`dest_mk` and {name}`mk_dest`. -/
def mkNat : NatTrans (F.objPresheaf (F.carrier N)) (F.carrier N) where
  app j := ↾ fun x ↦ mk (j := j.unop) x
  naturality _ _ g := by
    ext x
    exact mk_map g.unop x

end carrier

end PresheafPFunctor
