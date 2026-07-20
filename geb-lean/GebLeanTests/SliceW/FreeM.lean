import GebLean.SliceW.FreeM
import GebLeanTests.SliceW.Iso
import GebLeanTests.SliceW.Translate

/-! Smoke test for `SlicePFunctor.FreeM`, `FreeM.pure`, and `FreeM.node`, on
the toy translate functor of `GebLeanTests.SliceW.Translate` (the toy slice
endofunctor `F` of `GebLeanTests.SliceW.Iso`, translated along the constant
leaf map `v : Bool → PUnit`). -/

namespace SliceWFreeMTest

open SlicePFunctor

/-- A `pure` leaf, from the leaf datum `true` (`v true = PUnit.unit` by
`rfl`). -/
def pureLeaf : FreeM SliceWTranslateTest.v SliceWIsoTest.F PUnit.unit :=
  FreeM.pure ⟨true, rfl⟩

/-- `pureLeaf`'s fiber proof: its underlying tree's index is `PUnit.unit`. -/
example :
    (translate SliceWTranslateTest.v SliceWIsoTest.F).wIndex pureLeaf.1 = PUnit.unit :=
  pureLeaf.2

/-- `pureLeaf`'s underlying tree, via `val_pure`. -/
example :
    pureLeaf.1 = W.mk (F := translate SliceWTranslateTest.v SliceWIsoTest.F)
      ⟨⟨Sum.inl true, fun e => e.elim⟩, funext fun e => e.elim⟩ := by
  rfl

/-- A `node` at the unary `true` shape of the toy functor `F`, with `pureLeaf`
as its single child. -/
def nodeWithLeaves : FreeM SliceWTranslateTest.v SliceWIsoTest.F (SliceWIsoTest.F.q true) :=
  FreeM.node true (fun _ => pureLeaf)

/-- `nodeWithLeaves`'s fiber proof: its underlying tree's index is
`F.q true`. -/
example :
    (translate SliceWTranslateTest.v SliceWIsoTest.F).wIndex nodeWithLeaves.1
      = SliceWIsoTest.F.q true :=
  nodeWithLeaves.2

/-- `nodeWithLeaves`'s underlying tree, via `val_node`. -/
example : nodeWithLeaves.1 =
    W.mk (F := translate SliceWTranslateTest.v SliceWIsoTest.F)
      ⟨⟨Sum.inr true, fun _ => pureLeaf.1⟩,
        (SliceDomPFunctor.compatible_iff _ _ _ _).mpr fun _ => pureLeaf.2⟩ := by
  rfl

end SliceWFreeMTest
