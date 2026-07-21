import GebLean.SliceW.Reindex
import Mathlib.Logic.Equiv.Bool

/-! Smoke test for `SlicePFunctor.reindex` and its induced W-equivalence. A
toy slice endofunctor over `Bool` is base-changed along `Equiv.boolNot`; a
sample two-level tree exercises the field characterization lemmas, the
`wIndex_wMap` index law, and the `wEquiv` round trip. The one-sided
`domReindex` / `codReindex` are exercised on a non-endofunctor, reindexed on
its two sides by different maps. -/

namespace SliceWReindexTest

open SlicePFunctor

/-- Toy slice endofunctor over `Bool`: shapes `Bool`, with the false shape
nullary (`Empty` positions) and the true shape unary (`Unit` positions);
every direction maps to `false`, and the shape-output map is the identity. -/
def F : SlicePFunctor.{0, 0, 0, 0} Bool Bool where
  A := Bool
  B := fun a => match a with | true => Unit | false => Empty
  r := fun _ => false
  q := id

/-- A leaf: the nullary false shape with no children. -/
def leaf : F.W :=
  W.mk ⟨⟨false, fun b => b.elim⟩,
    (F.toSliceDomPFunctor.compatible_iff F.wIndex false _).mpr (fun b => b.elim)⟩

/-- A two-level tree: the unary true shape with the leaf as its single child. -/
def tree : F.W :=
  W.mk ⟨⟨true, fun _ => leaf⟩,
    (F.toSliceDomPFunctor.compatible_iff F.wIndex true _).mpr (fun _ => rfl)⟩

/-- The shape-output map of the reindexed functor at a sample shape. -/
example : (reindex Equiv.boolNot F).q true = Equiv.boolNot (F.q true) := by simp

/-- The direction-input map of the reindexed functor at a sample position. -/
example : (reindex Equiv.boolNot F).r ⟨true, ()⟩ = Equiv.boolNot (F.r ⟨true, ()⟩) := by
  simp only [reindex_r]

/-- `wMap` conjugates `wIndex` by `Equiv.boolNot` on the sample tree. -/
example : (reindex Equiv.boolNot F).wIndex (reindex.wMap Equiv.boolNot F tree) =
    Equiv.boolNot (F.wIndex tree) :=
  reindex.wIndex_wMap Equiv.boolNot F tree

/-- The `wEquiv` round trip on the sample tree. -/
example : (reindex.wEquiv Equiv.boolNot F).symm (reindex.wEquiv Equiv.boolNot F tree) = tree :=
  (reindex.wEquiv Equiv.boolNot F).symm_apply_apply tree

/-- Summing along `Bool → Unit` leaves the endofunctors: a slice functor from
`Type/Bool` to `Type/Unit`, with the direction-input map untouched. -/
def G : SlicePFunctor.{0, 0, 0, 0} Bool Unit := codReindex (fun _ => ()) F

/-- The shape-output map of `G` is `F`'s composed with the collapse. -/
example : G.q true = () := by simp [G]

/-- The direction-input map survives `codReindex` unchanged. -/
example : G.r ⟨true, ()⟩ = F.r ⟨true, ()⟩ := by simp [G]

/-- Reindexing the two sides by different maps: `G`'s domain by
`Equiv.boolNot`, its codomain having already been collapsed. -/
example : (domReindex Equiv.boolNot G).r ⟨true, ()⟩ = Equiv.boolNot (F.r ⟨true, ()⟩) := by
  simp [G]

/-- `domReindex` leaves the shape-output map, hence the codomain side, alone. -/
example : (domReindex Equiv.boolNot G).q true = () := by simp [G]

end SliceWReindexTest
