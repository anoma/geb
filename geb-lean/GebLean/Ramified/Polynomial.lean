import GebLean.Ramified.Polynomial.Collapse
import GebLean.Ramified.Polynomial.FirstOrder
import GebLean.Ramified.Polynomial.FreeAlg
import GebLean.Ramified.Polynomial.HigherOrder
import GebLean.Ramified.Polynomial.HigherOrderEquiv
import GebLean.Ramified.Polynomial.Ident
import GebLean.Ramified.Polynomial.IdentEquiv
import GebLean.Ramified.Polynomial.Interp
import GebLean.Ramified.Polynomial.RType
import GebLean.Ramified.Polynomial.SynCat
import GebLean.Ramified.Polynomial.SynCatEquiv
import GebLean.Ramified.Polynomial.Term

/-!
# Ramified recurrence on the vendored polynomial-functor stack

Directory index for the reimplementation of the `Ramified` recursive layer
(`GebLean/Ramified/AlgSig.lean`) on the vendored `geb-mathlib`
`SlicePFunctor` stack, connected to the existing implementation by the
generic bridge `GebLean/PolyBridge/`. `FreeAlg` supplies the free algebra
`FreeAlg'` on the slice `W`-type, its native recurrence
`FreeAlg'.recurse`, the bridge equivalence `freeAlgSliceEquiv : FreeAlg' A ≃
FreeAlg A`, and the numeric carrier of `natAlgSig`. `RType` reimplements the
ramified types `RType'` and their operations on that stack, with a
compatibility lemma per operation across the bridge `rTypeSliceEquiv`.
`FirstOrder` carves out the first-order sub-theories on that stack: the
first-order identifier predicate `RIdent'.FirstOrder`, the sub-theory
presentation `firstOrderPresentation`, and the inclusion functor `foInclusion`
into the host `RMRecCat'`.
-/
