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

/-- A leaf-child substitution: replace each variable by its own `pure`. -/
def sampleBindF :
    ∀ y, { a : sampleVars.left // sampleVars.hom a = y } →
      PolyFreeM sampleVars natAlgSig.polyEndo y :=
  fun _ a => polyFreeMPure sampleVars natAlgSig.polyEndo a

/-- Transport naturality at the identity reindexing on the sample leaf. -/
example :
    polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit sampleLeaf =
      polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit sampleLeaf :=
  polyFreeMSliceEquiv_transport sampleVars natAlgSig.polyEndo rfl sampleLeaf

/-- Pure naturality: the equivalence carries the sample leaf to the slice
free-monad `pure`. -/
example :
    polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit sampleLeaf =
      SlicePFunctor.FreeM.pure ⟨true, rfl⟩ :=
  polyFreeMSliceEquiv_pure sampleVars natAlgSig.polyEndo PUnit.unit ⟨true, rfl⟩

/-- Node naturality: the equivalence carries a unary node with one leaf child to
the slice free-monad `node`. -/
example :
    polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit
        (PolyFix.mk PUnit.unit (Sum.inr true) (fun _ => sampleLeaf)) =
      SlicePFunctor.FreeM.node (F := toSlice natAlgSig.polyEndo) (v := sampleVars.hom)
        ⟨PUnit.unit, true⟩
        (fun e => polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo _ ((fun _ => sampleLeaf) e)) :=
  polyFreeMSliceEquiv_node sampleVars natAlgSig.polyEndo PUnit.unit true (fun _ => sampleLeaf)

/-- Bind naturality: the equivalence intertwines legacy and slice `bind` on the
sample leaf. -/
example :
    polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit
        (polyFreeMBind sampleVars sampleVars natAlgSig.polyEndo sampleLeaf sampleBindF) =
      (polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo PUnit.unit sampleLeaf).bind
        (fun y a => polyFreeMSliceEquiv sampleVars natAlgSig.polyEndo y (sampleBindF y a)) :=
  polyFreeMSliceEquiv_bind sampleVars sampleVars natAlgSig.polyEndo PUnit.unit sampleLeaf
    sampleBindF
