import GebLean.PolyBridge.WEquiv
import GebLean.Ramified.AlgSig

/-! Smoke test for `GebLean.PolyBridge.polyFixSliceEquiv`: the fiberwise
equivalence between `PolyFix natAlgSig.polyEndo PUnit.unit` and the
`PUnit.unit`-indexed slice W-trees of `toSlice natAlgSig.polyEndo`. A sample
tree (the unary constructor applied to the nullary constructor) round-trips
through the equivalence, and its image carries the expected index. -/

open GebLean GebLean.Ramified GebLean.PolyBridge

/-- A sample tree: the unary constructor of `natAlgSig` applied to the
nullary constructor (a copy of the natural number `1`). -/
def sampleTree : PolyFix natAlgSig.polyEndo PUnit.unit :=
  FreeAlg.mk true (fun _ => FreeAlg.mk false Fin.elim0)

/-- The equivalence and its inverse compose to the identity on the sample
tree. -/
example :
    (polyFixSliceEquiv natAlgSig.polyEndo PUnit.unit).symm
        ((polyFixSliceEquiv natAlgSig.polyEndo PUnit.unit) sampleTree) = sampleTree :=
  (polyFixSliceEquiv natAlgSig.polyEndo PUnit.unit).symm_apply_apply sampleTree

/-- The image of the sample tree is indexed by `PUnit.unit`. -/
example :
    SlicePFunctor.wIndex (toSlice natAlgSig.polyEndo)
        ((polyFixSliceEquiv natAlgSig.polyEndo PUnit.unit sampleTree).1) = PUnit.unit :=
  (polyFixSliceEquiv natAlgSig.polyEndo PUnit.unit sampleTree).2
