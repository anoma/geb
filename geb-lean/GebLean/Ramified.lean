import GebLean.Ramified.AlgSig
import GebLean.Ramified.SortedSig
import GebLean.Ramified.Term
import GebLean.Ramified.Interp
import GebLean.Ramified.SynCat

/-!
# Ramified recurrence

Directory index for the ramified-recurrence development, formalizing
Leivant's higher-type ramified recurrence (Leivant III, DOI
`10.1016/S0168-0072(98)00040-2`). Phase 1 supplies the core layers:
free-algebra signatures and their recurrence (`AlgSig`),
multi-sorted signatures with the constructor summand (`SortedSig`), the
sorted term layer with its clone laws (`Term`), sorted models with the
interpretative setoid (`Interp`), and the generic syntactic category with
products (`SynCat`).

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
