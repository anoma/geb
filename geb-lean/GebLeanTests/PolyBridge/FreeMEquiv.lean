import GebLean.PolyBridge.FreeMEquiv
import GebLean.Ramified.AlgSig

/-! Smoke test for `GebLean.PolyBridge.polyFreeMSliceEquiv`: the fiberwise
equivalence between the legacy free monad `PolyFreeM V natAlgSig.polyEndo
PUnit.unit` and the slice free monad `SlicePFunctor.FreeM V.hom
(toSlice natAlgSig.polyEndo) PUnit.unit`, for a two-element variable family
`V` over `PUnit`. A sample `polyFreeMPure` leaf round-trips through the
equivalence. -/

open CategoryTheory GebLean GebLean.Ramified GebLean.PolyBridge

/-- A two-element variable family over `PUnit`: the leaf map from `Bool`. -/
def sampleVars : Over PUnit.{1} :=
  Over.mk (fun _ : Bool => PUnit.unit)

/-- A sample leaf: the free-monad `pure` of the variable `true`. -/
def sampleLeaf : PolyFreeM sampleVars natAlgSig.polyEndo PUnit.unit :=
  polyFreeMPure sampleVars natAlgSig.polyEndo ⟨true, rfl⟩

/-- The equivalence and its inverse compose to the identity on the sample
leaf. -/
example :
    (polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit).symm
        ((polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit) sampleLeaf) =
      sampleLeaf :=
  (polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit).symm_apply_apply sampleLeaf
