import GebLean.Ramified.Soundness.Applicative
import GebLean.Ramified.Soundness.OneLambda
import GebLean.Ramified.Soundness.BarRep
import GebLean.Ramified.Soundness.Represents

/-!
# Ramified recurrence: soundness

Directory index for the soundness development of the ramified-recurrence
workstream (Leivant III, DOI `10.1016/S0168-0072(98)00040-2`). The first
module realizes the object-sorted applicative λ-calculus `RλMR_o^ω` of
section 4.1 as a binding signature over the ramified types, an instance of the
indexed binder-substitution kit (`GebLean/Binding/`), and transcribes
Proposition 7's soundness arm `(1)⟹(4)` — the translation of every ramified
identifier to a term of that calculus (`Applicative`). The second module
realizes the simply-typed calculus `1λ(A)` of section 4.2 as a second binding
signature over the ramified types, with its congruence-closed reduction
(`OneLambda`).

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
