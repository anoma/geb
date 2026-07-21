import GebLean.Ramified.Polynomial.Characterization
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
generic bridge `GebLean/PolyBridge/`.

* `FreeAlg` — the free algebra `FreeAlg'` on the slice `W`-type, its native
  recurrence `FreeAlg'.recurse`, the bridge equivalence
  `freeAlgSliceEquiv : FreeAlg' A ≃ FreeAlg A`, and the numeric carrier of
  `natAlgSig`.
* `RType` — the ramified types `RType'` and their operations on that stack,
  with a compatibility lemma per operation across the bridge
  `rTypeSliceEquiv`.
* `Term` — the sorted term layer `Tm'` on the slice free monad
  `SlicePFunctor.FreeM`, with the clone laws and the bridge `tmSliceEquiv`.
* `Interp` — primed evaluation `Tm'.eval`, the interpretative quotient
  `interpQuotRel'`, and the evaluation agreement `tmSliceEquiv_eval`.
* `SynCat` — the generic primed syntactic category `SynCat'` with its chosen
  finite products.
* `SynCatEquiv` — the term-layer equivalence
  `synCatSliceEquiv : SynCat' P (interpQuotRel' P) ≌ SynCat P (interpQuotRel P)`.
* `Ident` — the primed schema-generated identifiers `RIdent'` on the slice
  `W`-type, with the application signature and the three schema formers.
* `IdentEquiv` — the identifier bridge `identSliceEquiv` relating `RIdent'` to
  the legacy `RIdent`.
* `HigherOrder` — the primed higher-order presentation `higherOrder'`, its
  syntactic category `RMRecCat'`, and the identifier morphism `identHom'`.
* `HigherOrderEquiv` — the presentation equivalence `higherOrderPresEquiv` and
  the category equivalence `rmRecCatSliceEquiv : RMRecCat' A ≌ RMRecCat A`.
* `FirstOrder` — the first-order sub-theories on that stack: the first-order
  identifier predicate `RIdent'.FirstOrder`, the sub-theory presentation
  `firstOrderPresentation`, and the inclusion functor `foInclusion` into the
  host `RMRecCat'`.
* `Collapse` — the primed first-order syntactic category `SynCatFO'`, its
  numeric denotation `collapseDenotation'`, the restriction equivalence
  `synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO`, and the denotation agreement
  across it.
* `Characterization` — the primed soundness functors `collapseFunctor'` and
  `collapseKFunctor'` with their faithfulness, and the transferred endpoints
  `ramified_definability'` and `ramified_definability_kSim'`.
-/
