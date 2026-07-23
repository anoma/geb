import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.AlgSig
import GebLean.Ramified.Algebras
import GebLean.Ramified.RType
import GebLean.Ramified.HigherOrder

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Correspondence

Part II chapter 1 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "Correspondence" =>

Part I introduces the manual's vocabulary where the reader first needs it, each
term marked once with `deftech`. Leivant III {citep leivant3}[] fixes its own
symbols and names for the same distinctions, and the two vocabularies agree on
some terms and diverge on others. The table below reads the manual's term
against Leivant III's symbol and name, where the paper carries a counterpart,
and against the Lean declaration, or a position within a declaration's type,
where the term lands in the code Part II samples. An em dash marks the absence
of a counterpart.

Leivant III section 2.3 names both the {tech}[object type] and the
{tech}[`Omega`-type] directly, in the Definition of ramified functional
types {citep leivant3}[].

:::table +header
*
  * Term here
  * Leivant III's symbol
  * Leivant III's name
  * Where it lands in the Lean code
*
  * {tech}[constructor label]
  * `c_i`
  * constructor
  * first argument of `g` in {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`
*
  * {tech}[recurrence parameters]
  * `x_vec`
  * recurrence parameters
  * second argument of `g` in {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`
*
  * {tech}[recurrence argument]
  * `c_i (a_1 ... a_{r_i})`
  * recurrence argument
  * the matched {name GebLean.Ramified.FreeAlg.mk}`FreeAlg.mk` value in
    {name GebLean.Ramified.FreeAlg.recurse_mk}`FreeAlg.recurse_mk`
*
  * {tech}[subterms]
  * `a_1 ... a_{r_i}`
  * —
  * third argument of `g` in {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`
*
  * {tech}[recursive results]
  * `phi_1 ... phi_{r_i}`
  * critical arguments
  * fourth argument of `g` in {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`
*
  * {tech}[step functions]
  * `g_ci`
  * recurrence functions
  * `g`, the argument of {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`
*
  * {tech}[monotonic]
  * —
  * monotonic
  * {name GebLean.Ramified.MrecShape}`MrecShape`
*
  * {tech}[closed]
  * —
  * closed
  * —
*
  * {tech}[flat]
  * —
  * flat
  * {name GebLean.Ramified.FrecShape}`FrecShape`
*
  * {tech}[monadic word algebra]
  * —
  * monadic word algebra
  * {name GebLean.Ramified.natAlgSig}`natAlgSig`
*
  * {tech}[polyadic word algebra]
  * —
  * polyadic word algebra
  * {name GebLean.Ramified.binWordAlgSig}`binWordAlgSig`
*
  * {tech}[tree algebra]
  * —
  * tree algebra
  * {name GebLean.Ramified.treeAlgSig}`treeAlgSig`
*
  * {tech}[r-type]
  * —
  * r-type
  * {name GebLean.Ramified.RType}`RType`
*
  * {tech}[object type]
  * —
  * object type
  * {name GebLean.Ramified.RType.IsObj}`RType.IsObj`
*
  * {tech}[`Omega`-type]
  * `Omega tau`
  * `Omega`-type
  * {name GebLean.Ramified.RType.omega}`RType.omega`
*
  * {tech}[tier]
  * —
  * —
  * the `Nat` index of {name GebLean.Ramified.RType.tower}`RType.tower`
:::

Verso collects every `deftech` definition into a domain titled Terminology,
searchable from the generated site's quick-jump box; a `tech` reference
elsewhere in this manual is a hyperlink to that term's `deftech` site in the
prose, not to a rendered index page.
