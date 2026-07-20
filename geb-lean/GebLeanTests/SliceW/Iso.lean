import GebLean.SliceW.Iso

/-! Smoke test for `SlicePFunctor.Iso` and its induced W-equivalence. A toy
slice endofunctor over `Unit` (shapes `Bool`, the false shape nullary and the
true shape unary) is related to itself by the identity isomorphism; a sample
two-level tree transports under `wMap` with its index preserved and round-trips
through `wEquiv`. -/

namespace SliceWIsoTest

open SlicePFunctor

/-- Toy slice endofunctor over `Unit`: shapes `Bool`, with the false shape
nullary (`Empty` positions) and the true shape unary (`Unit` positions). -/
def F : SlicePFunctor.{0, 0, 0, 0} Unit Unit where
  A := Bool
  B := fun b => match b with | true => Unit | false => Empty
  r := fun _ => ()
  q := fun _ => ()

/-- The identity isomorphism `F ≅ F`. -/
def e : SlicePFunctor.Iso F F where
  shapeEquiv := Equiv.refl _
  posEquiv := fun _ => Equiv.refl _
  q_comm := fun _ => rfl
  r_comm := fun _ _ => rfl

/-- A leaf: the nullary false shape with no children. -/
def leaf : F.W :=
  W.mk ⟨⟨false, fun b => b.elim⟩,
    (F.toSliceDomPFunctor.compatible_iff F.wIndex false _).mpr (fun b => b.elim)⟩

/-- A two-level tree: the unary true shape with the leaf as its single child. -/
def tree : F.W :=
  W.mk ⟨⟨true, fun _ => leaf⟩,
    (F.toSliceDomPFunctor.compatible_iff F.wIndex true _).mpr (fun _ => rfl)⟩

/-- `wMap` preserves the tree's index. -/
example : F.wIndex (e.wMap tree) = F.wIndex tree :=
  e.wIndex_wMap tree

/-- The equivalence and its inverse compose to the identity on the sample
tree. -/
example : e.wEquiv.symm (e.wEquiv tree) = tree :=
  e.wEquiv.symm_apply_apply tree

end SliceWIsoTest
