import GebLean.Ramified.AlgSig
import GebLean.Ramified.SortedSig
import GebLean.Ramified.Term
import GebLean.Ramified.Interp
import GebLean.Ramified.SynCat
import GebLean.Ramified.RType
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.OmegaShift
import GebLean.Ramified.Examples
import GebLean.Ramified.Algebras
import GebLean.Ramified.Definability
import GebLean.Ramified.Soundness
import GebLean.Ramified.Characterization
import GebLean.Ramified.SigEquiv
import GebLean.Ramified.PresentationEquiv
import GebLean.Ramified.Polynomial

/-!
# Ramified recurrence

Directory index for the ramified-recurrence development, formalizing
Leivant's higher-type ramified recurrence (Leivant III, DOI
`10.1016/S0168-0072(98)00040-2`). Phase 1 supplies the core layers:
free-algebra signatures and their recurrence, together with the numeric
reading `natToFreeAlg`/`freeAlgToNat` of the standard carrier
`FreeAlg natAlgSig` (`AlgSig`),
multi-sorted signatures with the constructor summand (`SortedSig`), the
sorted term layer with its clone laws (`Term`), sorted models with the
interpretative setoid (`Interp`), and the generic syntactic category with
products (`SynCat`). Phase 2 opens the higher-order system with the
ramified types and their object sorts (`RType`), the higher-order
presentation with schema-generated identifiers (`HigherOrder`), and the
sort-level Omega shift with the auxiliary coercion kappa-hat
(`OmegaShift`). The worked examples of Leivant III section 2.4 over the
`1 + X` word algebra — the downward coercions `kappa` and `delta`,
addition, multiplication, the second-order exponential `ramExp`, the
`2_m` ladder `ramTwoPow` (aligned with `GebLean.tower`), and the size
function, each with its interpretation lemma — are in `Examples`. Phase 3
instantiates the three canonical free-algebra signatures — the monadic
word algebra `natAlgSig`, the polyadic binary-word algebra
`binWordAlgSig`, and the binary-tree algebra `treeAlgSig` — with a smoke
recurrence at each, the numeric equivalence
`natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ`, and the signature morphisms
`AlgSigHom` with their carrier transport `freeAlgMap` and image-point
naturality (`Algebras`). Phase 4 carves out the first-order sub-theories on the
polynomial stack: the first-order identifier predicate `RIdent'.FirstOrder`, the
sub-theory presentation `firstOrderPresentation` (its identifier summands
restricted to the `FirstOrder` subtype), and the inclusion functor `foInclusion`
into the host `RMRecCat'` (`Polynomial/FirstOrder`). Phase 5 opens the
definability development (`Definability`): the case function `ramCase`, the destructor
`ramDstr`, and the selector `chooseIdent`, the building blocks of Leivant III's Lemma 2
reduction of simultaneous recurrence to plain recurrence. Phase 6 packages the
soundness direction (`Soundness`): the first-order syntactic category
`SynCatFO` and the faithful collapse functor `collapseFunctor` into
`LawvereERCat`. Phase 7 assembles the elementary characterization
(`Characterization`): the definability statement `ramified_definability` over
the collapse denotation, paired with the collapse functor's faithfulness as
the denotational form of Leivant III's Theorem 14 items (1)-(2).

The generic transport layer for relating two presentations of the same theory
is `SigEquiv` — sorted-signature isomorphisms `SortedSigEquiv` with the term
translation `tmMap` and its equivalence packaging `tmEquiv` — and
`PresentationEquiv`, which adds a carrier equivalence commuting with the
operation interpretations and delivers the induced equivalence `synCatEquiv`
of syntactic categories. `Polynomial` reimplements the whole development on
the vendored `SlicePFunctor` stack and connects it back by that layer.

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
