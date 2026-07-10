import GebLean.Ramified.Soundness.Applicative
import GebLean.Ramified.Soundness.OneLambda
import GebLean.Ramified.Soundness.BarRep
import GebLean.Ramified.Soundness.Represents
import GebLean.Ramified.Soundness.Normalization
import GebLean.Ramified.Soundness.OneLambdaEval
import GebLean.Ramified.Soundness.DetStep
import GebLean.Ramified.Soundness.CodeTm
import GebLean.Ramified.Soundness.CodeNormalizer
import GebLean.Ramified.Soundness.NormStepER

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
(`OneLambda`). A further module develops Lemma 12's normalization bound for
`1λ(A)`, starting from the type-order measure `RType.ord` (`Normalization`). The
final module gives the standard simple-type evaluator `oneEval` of `1λ(A)` over
the standard word algebra, with its renaming- and substitution-fusion laws
(`OneLambdaEval`). A further module realizes the reduction strategy of Lemma 12
as the total computable deterministic step `detStep` on `1λ(A)` terms
(`DetStep`). A further module opens the code-normalizer realization layer with the
code-level single-variable substitution `subCode` and its supporting code-level
weakening `shiftCode`, the numeric images of `Binding.instantiate₁` and
`ren Thinning.weakAppend` under `codeTm` (`CodeNormalizer`). A further module opens
the elementary-recursive realization of that code-normalizer layer with the
non-recursive code reads as `ERMor1` morphisms whose interpretation equals the
mirrored ℕ-level function (`NormStepER`).

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/
