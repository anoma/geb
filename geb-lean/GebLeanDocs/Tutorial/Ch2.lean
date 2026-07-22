import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.Examples

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The need to restrict recurrence

Part I chapter 2 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "The need to restrict recurrence" =>

Chapter 1 states the recurrence schema
{name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse` without restricting how a
{tech}[step functions] equation for one identifier may itself invoke identifiers already
defined by the schema. Nesting a recurrence inside the step function of another is
therefore unbounded in depth.

Nesting drives growth. A step function built from a recurrence that already computes
exponentiation exponentiates once more, and repeating this construction to depth `m`
yields the tower of twos `2_0(x) = x`, `2_{m+1}(x) = 2^{2_m(x)}`. Leivant III section
2.4(4) exhibits exactly this escalation over the monadic word algebra
{name GebLean.Ramified.natAlgSig}`natAlgSig` {citep leivant3}[]. Because the schema of
chapter 1 places no bound on nesting depth, it reaches every level of this ladder.

Part I chapter 5 realizes the ladder as
{name GebLean.Ramified.ramTwoPow}`ramTwoPow`. A schema that reaches every level of a
tower of exponentials by nesting, with no bound on how deep the nesting may go, needs
restraining before its growth can be tied to any complexity measure. Part I chapter 3
supplies the restraint.
