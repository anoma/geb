import GebLean.SliceW.Translate
import GebLeanTests.SliceW.Iso

/-! Smoke test for `SlicePFunctor.translate`. The toy slice endofunctor `F`
of `GebLeanTests.SliceW.Iso` is translated along a constant leaf map
`v : Bool → PUnit`; the shape-output map on each summand recovers `v` (left)
or `F.q` (right). -/

namespace SliceWTranslateTest

open SlicePFunctor

/-- The leaf-data map for the translated shapes: constant into `F`'s index
type. -/
def v : Bool → PUnit := fun _ => PUnit.unit

/-- The left summand's shape-output map is `v`. -/
example : (translate v SliceWIsoTest.F).q (.inl true) = v true := by
  simp

/-- The right summand's shape-output map is `F`'s. -/
example (a : SliceWIsoTest.F.A) :
    (translate v SliceWIsoTest.F).q (.inr a) = SliceWIsoTest.F.q a := by
  simp

end SliceWTranslateTest
