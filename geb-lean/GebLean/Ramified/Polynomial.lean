import GebLean.Ramified.Polynomial.FreeAlg

/-!
# Ramified recurrence on the vendored polynomial-functor stack

Directory index for the reimplementation of the `Ramified` recursive layer
(`GebLean/Ramified/AlgSig.lean`) on the vendored `geb-mathlib`
`SlicePFunctor` stack, connected to the existing implementation by the
generic bridge `GebLean/PolyBridge/`. `FreeAlg` supplies the free algebra
`FreeAlg'` on the slice `W`-type, its native recurrence
`FreeAlg'.recurse`, the bridge equivalence `freeAlgSliceEquiv : FreeAlg' A ≃
FreeAlg A`, and the numeric carrier of `natAlgSig`.
-/
