import VersoManual
import GebLeanDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Transcription map and scope

Part II chapter 6 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "Transcription map and scope" =>

This is the manual's closing chapter. Chapters 2 through 5 sample twelve
modules of `GebLean/Ramified/`, one declaration at a time. The table below
takes the opposite direction: for every section or numbered equation of
Leivant III {citep leivant3}[] that `GebLean/Ramified/` transcribes, it names
the module or modules carrying that transcription, across the whole
directory rather than only the twelve modules the manual has rendered. The
prose that follows the table states which of those modules Part II leaves
unread.

:::table +header
*
  * Transcribed item
  * Leivant III location
  * Lean module(s)
*
  * Free algebra; {tech}[monadic word algebra], {tech}[polyadic word
    algebra], {tech}[tree algebra]
  * section 2.1
  * `GebLean/Ramified/AlgSig.lean`, `GebLean/Ramified/Algebras.lean`
*
  * Recurrence over `A`, eq. (1); {tech}[monotonic], {tech}[closed],
    {tech}[flat] variants
  * section 2.1, eq. (1)
  * `GebLean/Ramified/AlgSig.lean`
*
  * Ramified types, the {tech}[r-type] grammar
  * section 2.3
  * `GebLean/Ramified/RType.lean`
*
  * Ramified recurrence `RRec-omega(A)` for type `tau`, eq. (4)
  * section 2.3, eq. (4)
  * `GebLean/Ramified/HigherOrder.lean`
*
  * Flat recurrence, `RMRec-omega` (the monotonic fragment), eq. (5)
  * section 2.3, eq. (5)
  * `GebLean/Ramified/HigherOrder.lean`
*
  * Coercions `kappa_tau`, `kappa-hat_tau`, `delta_theta`
  * section 2.4(1)
  * `GebLean/Ramified/OmegaShift.lean`, `GebLean/Ramified/Examples.lean`
*
  * Ramified addition, multiplication
  * section 2.4(2)
  * `GebLean/Ramified/Examples.lean`
*
  * First-order recurrence, restricted to {tech}[object type]s, p. 216
  * section 2.4(3), p. 216
  * `GebLean/Ramified/Polynomial/FirstOrder.lean`
*
  * Exponentiation via second-order recurrence
  * section 2.4(3)
  * `GebLean/Ramified/Examples.lean`
*
  * Iterated exponentials `2_m` at each object type
  * section 2.4(4)
  * `GebLean/Ramified/Examples.lean`,
    `GebLean/Ramified/Definability/Ladder.lean`
*
  * Size function `sz`
  * section 2.4(6)
  * `GebLean/Ramified/Examples.lean`
*
  * Lemma 1: flat recurrence versus destructors and case
  * section 2.5
  * `GebLean/Ramified/Definability/Flat.lean`
*
  * Simultaneous recurrence, Lemma 2, eqs. (6)-(7)
  * section 2.6, eqs. (6)-(7)
  * `GebLean/Ramified/Definability/Simultaneous.lean`
*
  * Collapse `f-minus`, raising `G-plus-tau`, Lemmas 3-4
  * section 2.7
  * `GebLean/Ramified/Soundness/Collapse.lean`
*
  * Register machines over `A`, Lemma 5
  * section 3.1
  * `GebLean/Ramified/Definability/Machine.lean`
*
  * Lemma 6: elementary-time machines are ramified-definable
  * section 3.2
  * `GebLean/Ramified/Definability/Machine.lean`,
    `GebLean/Ramified/Definability/Bounds.lean`,
    `GebLean/Ramified/Definability/Top.lean`
*
  * Object-sorted applicative calculus `RlMR-omega_o`
  * section 4.1
  * `GebLean/Ramified/Soundness/Applicative.lean`
*
  * Proposition 7: equational and applicative agreement
  * section 4.1
  * `GebLean/Ramified/Soundness/Applicative.lean`
*
  * Lambda-representation in `1l(A)`, Lemmas 8-10, Proposition 11
  * sections 4.2-4.3
  * `GebLean/Ramified/Soundness/OneLambda.lean`,
    `GebLean/Ramified/Soundness/BarRep.lean`,
    `GebLean/Ramified/Soundness/Represents.lean`
*
  * Normalization bound, Lemma 12, Proposition 13
  * section 5
  * `GebLean/Ramified/Soundness/Normalization.lean`
*
  * Theorem 14: the elementary characterization
  * section 6.1
  * `GebLean/Ramified/Soundness/Collapse.lean`,
    `GebLean/Ramified/Characterization.lean`
:::

Part II does not render the `GebLean/Ramified/Definability/` directory or its
index module `GebLean/Ramified/Definability.lean`. The table above locates
several of the paper's definability-route items there — the destructor and
case machinery of Lemma 1, Lemma 2's reduction of simultaneous recurrence,
and the register-machine simulation of Lemmas 5 and 6 — but the directory
carries that material as proof development extending well beyond the
schema-level declarations Part II samples.

Nor does Part II render the `GebLean/Ramified/Polynomial/` directory or its
index module `GebLean/Ramified/Polynomial.lean`: a reimplementation of the
generic core and the higher-order system on the vendored polynomial-functor
stack, connected to the modules above by a further layer of bridging
equivalences.

Chapter 5 renders `GebLean/Ramified/Soundness/Collapse.lean` alone, as the
source of both endpoint triples' first member. The remainder of
`GebLean/Ramified/Soundness/` and its index module
`GebLean/Ramified/Soundness.lean` — carrying the applicative calculi and
Proposition 7 of section 4.1, the lambda-representation of sections 4.2-4.3,
and the normalization bound of section 5 that the table above locates there
— stays outside Part II, along with `GebLean/Ramified/SigEquiv.lean`,
`GebLean/Ramified/PresentationEquiv.lean`, and the area's own index module
`GebLean/Ramified.lean`.

Each omission is deliberate. These modules carry further paper transcription
and the proof apparatus connecting it to the theorem chapter 5 states —
material outside this manual's remit, not schema-level constructions the
sampling above overlooked.
