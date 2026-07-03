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
import GebLean.Ramified.FirstOrder

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
naturality (`Algebras`). Phase 4 carves out the first-order sub-theories: the
tower-sort predicate `RType.IsTower`, the first-order identifier predicate
`RIdent.FirstOrder`, the sub-theory presentation `firstOrderPresentation` (its
identifier summands restricted to the `FirstOrder` subtype), and the inclusion
functor `foInclusion` into the host `RMRecCat` (`FirstOrder`).

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
