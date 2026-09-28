/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.W

set_option doc.verso true in
/-!
# Fixed points of slice endofunctors

A fixed point of a slice endofunctor {lit}`F : SlicePFunctor I I` is an object
{lit}`(T, index)` of {lit}`Type/I` together with a constructor from the value
of {lit}`F` at that object and a destructor back, mutually inverse, the
destructor lying over {lit}`I`. The W-type {name}`SlicePFunctor.W`, the
initial algebra, is one, and so is the terminal coalgebra. A construction
that uses only this structure, such as the root restriction of trees along
the action of a presheaf polynomial functor, is stated once over a fixed
point and serves both.

## Main definitions

* {lit}`SlicePFunctor.FixedPoint` — a fixed point of a slice endofunctor.
* {lit}`SlicePFunctor.wFixedPoint` — the W-type as a fixed point.

## Main statements

* {lit}`SlicePFunctor.FixedPoint.index_mk` — the constructor lies over
  {lit}`I`.

## Tags

fixed point, slice category, polynomial functor, W-type
-/
set_option doc.verso true

@[expose] public section

universe u uA uB uI

namespace SlicePFunctor

variable {I : Type uI}

/-- A fixed point of the slice endofunctor {lit}`F`: a type over {lit}`I`
with mutually inverse constructor and destructor, the destructor lying over
{lit}`I`. -/
structure FixedPoint (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    Type (max (u + 1) uA uB uI) where
  /-- Assemble a fixed point from its fields. -/
  intro ::
  /-- The carrier. -/
  T : Type u
  /-- The structure map into {lit}`I`. -/
  index : T → I
  /-- The constructor. -/
  mk : F.toSliceDomPFunctor.Obj index → T
  /-- The destructor. -/
  dest : T → F.toSliceDomPFunctor.Obj index
  /-- The destructor inverts the constructor. -/
  dest_mk : ∀ x, dest (mk x) = x
  /-- The constructor inverts the destructor. -/
  mk_dest : ∀ t, mk (dest t) = t
  /-- The destructor lies over {lit}`I`. -/
  obj_dest : ∀ t, F.obj index (dest t) = index t

namespace FixedPoint

variable {F : SlicePFunctor.{uA, uB, uI, uI} I I} (S : FixedPoint.{u} F)

/-- The constructor lies over {lit}`I`. -/
theorem index_mk (x : F.toSliceDomPFunctor.Obj S.index) : S.index (S.mk x) = F.obj S.index x :=
  (S.obj_dest (S.mk x)).symm.trans (congrArg (F.obj S.index) (S.dest_mk x))

end FixedPoint

/-- The W-type of {lit}`F` as a fixed point of {lit}`F`. Reducible, so that
instance resolution sees the W-type and its index through the fixed point's
fields. -/
@[reducible] def wFixedPoint (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    FixedPoint.{max uA uB} F where
  T := F.W
  index := F.wIndex
  mk := W.mk
  dest := W.dest
  dest_mk := W.dest_mk
  mk_dest := W.mk_dest
  obj_dest z := by
    obtain ⟨w, hw⟩ := z
    cases w
    rfl

end SlicePFunctor
