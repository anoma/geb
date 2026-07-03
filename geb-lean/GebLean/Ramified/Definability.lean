import GebLean.Ramified.Definability.Simultaneous
import GebLean.Ramified.Definability.Flat
import GebLean.Ramified.Definability.Bounds

/-!
# Ramified recurrence: definability

Directory index for the definability development of the ramified-recurrence
workstream (Leivant III, DOI `10.1016/S0168-0072(98)00040-2`), which transcribes
the reduction of simultaneous recurrence to plain recurrence (Lemma 2, section
2.6) and its supporting constructions. The first module supplies the case
function, the destructor, and the selector `choose` over the `1 + X` word
algebra `natAlgSig` — the building blocks of Lemma 2's selector argument
(`Simultaneous`). The second packages the destructor/case operations as a
signature summand generic in the algebra, realizes them by flat recurrence
over `natAlgSig` — the containment direction of Lemma 1 — and assembles the
O-variant presentation `RMRec_o^omega` of section 2.5, in which flat
recurrence is replaced by the destructor and case operations (`Flat`). The
third module carries the pure natural-number inequalities converting the
elementary-recurrence runtime tower bound into Leivant's clock format
`c · 2_q(sz)` (Lemma 6 hypothesis shape, section 3.2), including the
componentwise max-over-inputs handling of the arity remark (`Bounds`).

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
