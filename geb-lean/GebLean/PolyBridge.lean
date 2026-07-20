import GebLean.PolyBridge.Slice
import GebLean.PolyBridge.WEquiv
import GebLean.PolyBridge.FreeMEquiv

/-!
# Polynomial-functor bridge

Directory index for translations between this development's polynomial
functor presentations (`GebLean/Polynomial.lean`, `GebLean/PolyAlg.lean`)
and the vendored `geb-mathlib` `SlicePFunctor` stack
(`Geb.Mathlib.Data.PFunctor.Slice.Basic`), on which the ramified
free-algebra layer (`GebLean/Ramified/AlgSig.lean`) is being reimplemented.
`Slice` supplies the generic shape-level translation `toSlice`; `WEquiv`
carries it to the initial algebras, the fiberwise equivalence
`PolyFix P x ≃ { w : (toSlice P).W // wIndex w = x }`; `FreeMEquiv`
identifies the translate augmentations and carries the comparison to the
free monads, `PolyFreeM V P x ≃ SlicePFunctor.FreeM V.hom (toSlice P) x`.
-/
