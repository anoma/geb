/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.MType.Hereditary
public import Geb.Mathlib.Data.PFunctor.Slice.FixedPoint

set_option doc.verso true in
/-!
# M-types of slice polynomial functors

When {lit}`dom = cod = I`, a {name}`SlicePFunctor` {lit}`F` is an endofunctor of
{lit}`Type/I`. Its M-type (terminal coalgebra) is obtained from the M-type of
the underlying polynomial functor, as its W-type
({name}`SlicePFunctor.W`) is obtained from the underlying W-type: a tree is
admitted when every node's children lie over the direction-input indices
prescribed by {lit}`r`, and it is indexed by the {lit}`q`-assigned output
index of its root shape. Admissibility is the hereditary form
({name}`Geb.MType.Hereditary`) of the condition on a single root layer
({lit}`NodeAdmissible`), which is {name}`SliceDomPFunctor.Compatible` for the
root indices of the children; for W-types it is an inductive fold, and here
it is coinductive.

The constructor and destructor are those of the underlying M-type,
restricted, and the corecursor into the M-type from a slice coalgebra is the
corecursor of the underlying coalgebra, whose image is admissible by
coinduction. It lies over {lit}`I`, is a morphism of slice coalgebras, and is
the only one, by the uniqueness of the underlying corecursor, so
{lit}`SliceM F` is the terminal slice coalgebra among slice coalgebras in
every universe.

## Main definitions

* {lit}`mIndexRoot`, {lit}`NodeAdmissible`, {lit}`MValid` — the root index
  of a tree of the underlying M-type, admissibility of a root layer, and
  hereditary admissibility.
* {lit}`SliceM` — the M-type of {lit}`F`: the admissible trees.
* {lit}`SliceM.index` — its structure map into {lit}`I`.
* {lit}`SliceM.mk`, {lit}`SliceM.dest`, {lit}`SliceM.destEquiv` — the
  constructor and destructor, and the two as an equivalence.
* {lit}`SliceM.fixedPoint` — {lit}`SliceM F` as a fixed point of the slice
  endofunctor.
* {lit}`SliceM.corec` — the corecursor from a slice coalgebra.

## Main statements

* {lit}`SliceM.dest_mk`, {lit}`SliceM.mk_dest` — the constructor and
  destructor are mutually inverse.
* {lit}`SliceM.index_mk` — the constructor lies over {lit}`I`.
* {lit}`SliceM.comp_corec`, {lit}`SliceM.dest_corec` — the corecursor lies
  over {lit}`I` and is a morphism of slice coalgebras.
* {lit}`SliceM.corec_unique` — it is the only one.

## References

* \[GambinoHyland2004\]
* \[GambinoKock2013\]
* \[VanDenBergDeMarchi2007\], Section 2.

## Tags

M-type, terminal coalgebra, polynomial functor, dependent polynomial functor,
slice category, container, coinduction
-/
set_option doc.verso true

@[expose] public section

universe uA uB uI uY

namespace Geb.MType

variable {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)

/-- The index of a tree of the underlying M-type: the output index of its
root shape. -/
def mIndexRoot (w : M F.toPFunctor) : I := F.q w.head

/-- A root layer is admissible when its children's indices lie over the
direction-input map. -/
def NodeAdmissible (x : F.toPFunctor.Obj (M F.toPFunctor)) : Prop :=
  F.toSliceDomPFunctor.Compatible (mIndexRoot F) x.1 x.2

/-- Hereditary admissibility: every root layer reached through children is
admissible. -/
def MValid : M F.toPFunctor → Prop := Hereditary M.dest (NodeAdmissible F ∘ M.dest)

/-- Admissibility unfolded one level. -/
theorem mValid_iff (w : M F.toPFunctor) :
    MValid F w ↔ NodeAdmissible F w.dest ∧ ∀ b, MValid F (w.children b) :=
  hereditary_iff M.dest (NodeAdmissible F ∘ M.dest) w

/-- Admissibility at a constructor. -/
theorem mValid_mk (x : F.toPFunctor.Obj (M F.toPFunctor)) :
    MValid F (M.mk x) ↔ NodeAdmissible F x ∧ ∀ b, MValid F (x.2 b) :=
  hereditary_mk (NodeAdmissible F) x

/-- The M-type of the slice endofunctor {lit}`F`: the admissible trees of the
underlying M-type. -/
def SliceM : Type (max uA uB) := { w : M F.toPFunctor // MValid F w }

namespace SliceM

/-- The structure map into {lit}`I`: the index of the underlying tree. -/
def index (z : SliceM F) : I := mIndexRoot F z.1

variable {F}

/-- Elements with equal underlying trees are equal. -/
theorem ext {z z' : SliceM F} (h : z.1 = z'.1) : z = z' := Subtype.ext h

/-- The constructor: the slice endofunctor's value at {lit}`(SliceM F, index)`
maps into {lit}`SliceM F`. -/
def mk (x : F.toSliceDomPFunctor.Obj (index F)) : SliceM F :=
  ⟨M.mk (F.toPFunctor.map Subtype.val x.1), (mValid_mk F _).mpr ⟨x.2, fun b ↦ (x.1.2 b).2⟩⟩

/-- The destructor: the root shape with its admissible children, compatible
with the direction-input map. -/
def dest (z : SliceM F) : F.toSliceDomPFunctor.Obj (index F) :=
  ⟨⟨z.1.head, fun b ↦ ⟨z.1.children b, ((mValid_iff F z.1).mp z.2).2 b⟩⟩,
    ((mValid_iff F z.1).mp z.2).1⟩

/-- The destructor inverts the constructor. -/
@[simp] theorem dest_mk (x : F.toSliceDomPFunctor.Obj (index F)) : (mk x).dest = x :=
  Subtype.ext (PFunctor.map_injective Subtype.val_injective
    (M.dest_mk (F.toPFunctor.map Subtype.val x.1)))

/-- The constructor inverts the destructor. -/
@[simp] theorem mk_dest (z : SliceM F) : mk z.dest = z :=
  ext (M.mk_dest z.1)

/-- The constructor lies over {lit}`I`: its index is the output index of the
layer's shape. -/
theorem index_mk (x : F.toSliceDomPFunctor.Obj (index F)) : index F (mk x) = F.obj (index F) x :=
  congrArg (fun d : F.toPFunctor.Obj (M F.toPFunctor) ↦ F.q d.1)
    (M.dest_mk (F.toPFunctor.map Subtype.val x.1))

/-- The destructor lies over {lit}`I`. -/
theorem obj_dest (z : SliceM F) : F.obj (index F) z.dest = index F z :=
  rfl

variable (F) in
/-- The constructor and destructor exhibit {lit}`SliceM F` as a fixed point of
the slice endofunctor. -/
def destEquiv : SliceM F ≃ F.toSliceDomPFunctor.Obj (index F) where
  toFun := dest
  invFun := mk
  left_inv := mk_dest
  right_inv := dest_mk

variable (F) in
/-- {lit}`SliceM F` as a fixed point of the slice endofunctor
({name}`SlicePFunctor.FixedPoint`). Reducible, so that instance resolution sees
{lit}`SliceM F` and its index through the fixed point's fields. -/
@[reducible] def fixedPoint : SlicePFunctor.FixedPoint.{max uA uB} F where
  T := SliceM F
  index := index F
  mk := mk
  dest := dest
  dest_mk := dest_mk
  mk_dest := mk_dest
  obj_dest := obj_dest

section Corec

variable (F) {Y : Type uY} (p : Y → I) (g : Y → F.toSliceDomPFunctor.Obj p)
  (hg : F.obj p ∘ g = p)

include hg

/-- The root index of the underlying corecursion from {lit}`y` is {lit}`p y`. -/
theorem mIndexRoot_corec (y : Y) : mIndexRoot F (M.corec (fun y ↦ (g y).1) y) = p y :=
  (congrArg (fun d : F.toPFunctor.Obj (M F.toPFunctor) ↦ F.q d.1) (M.dest_corec _ y)).trans
    (congrFun hg y)

/-- The underlying corecursion from a slice coalgebra is admissible: its
root layers are admissible, by {name}`mIndexRoot_corec`, so it is admissible by
{name}`Geb.MType.hereditary_of_hom`. -/
theorem mValid_corec (y : Y) : MValid F (M.corec (fun y ↦ (g y).1) y) := by
  refine hereditary_of_hom M.dest _ (fun y ↦ (g y).1) _ (M.dest_corec _) (fun y ↦ ?_) y
  change NodeAdmissible F (M.corec _ y).dest
  rw [M.dest_corec]
  exact funext fun b ↦ (mIndexRoot_corec F p g hg ((g y).1.2 b)).trans (congrFun (g y).2 b)

/-- The corecursor from a slice coalgebra {lit}`(Y, p, g)` over {lit}`I`. -/
def corec (y : Y) : SliceM F := ⟨M.corec (fun y ↦ (g y).1) y, mValid_corec F p g hg y⟩

/-- The corecursor lies over {lit}`I`. -/
theorem comp_corec : index F ∘ corec F p g hg = p :=
  funext (mIndexRoot_corec F p g hg)

/-- The computation rule for the corecursor: it is a morphism of slice
coalgebras. -/
@[simp] theorem dest_corec (y : Y) :
    (corec F p g hg y).dest =
      F.toSliceDomPFunctor.map (corec F p g hg) (comp_corec F p g hg) (g y) :=
  Subtype.ext (PFunctor.map_injective Subtype.val_injective (M.dest_corec (fun y ↦ (g y).1) y))

/-- The corecursor is the only morphism of slice coalgebras into
{lit}`SliceM F`. -/
theorem corec_unique (f : Y → SliceM F) (hfp : index F ∘ f = p)
    (hf : ∀ y, (f y).dest = F.toSliceDomPFunctor.map f hfp (g y)) : f = corec F p g hg := by
  have h : (fun y ↦ (f y).1) = M.corec fun y ↦ (g y).1 :=
    M.corec_unique _ _ fun y ↦
      congrArg (fun x : F.toSliceDomPFunctor.Obj (index F) ↦ F.toPFunctor.map Subtype.val x.1)
        (hf y)
  exact funext fun y ↦ ext (congrFun h y)

end Corec

end SliceM

end Geb.MType
