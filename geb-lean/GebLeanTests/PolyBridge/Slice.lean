import GebLean.PolyBridge.Slice
import GebLean.Ramified.AlgSig

/-! Smoke test for `GebLean.PolyBridge.toSlice`: the `SlicePFunctor`
translation of `natAlgSig.polyEndo` (the `1 + X` word signature) has the
two constructor-label shapes of `Bool`, each with shape-output
`PUnit.unit` (`natAlgSig.polyEndo : PolyEndo PUnit`). -/

open GebLean GebLean.Ramified GebLean.PolyBridge

/-- The `false`-labelled constructor shape of `natAlgSig.polyEndo`,
translated to `SlicePFunctor`. -/
example : (toSlice natAlgSig.polyEndo).A := ⟨PUnit.unit, false⟩

/-- The `true`-labelled constructor shape of `natAlgSig.polyEndo`,
translated to `SlicePFunctor`. -/
example : (toSlice natAlgSig.polyEndo).A := ⟨PUnit.unit, true⟩

example : (toSlice natAlgSig.polyEndo).q ⟨PUnit.unit, false⟩ = PUnit.unit := by decide

example : (toSlice natAlgSig.polyEndo).q ⟨PUnit.unit, true⟩ = PUnit.unit := by decide
