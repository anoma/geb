import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.HigherOrder

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The ramified schema

Part I chapter 4 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "The ramified schema" =>

Chapter 1 stated the recurrence schema and chapter 2 exhibited its unbounded
growth; chapter 3 built a hierarchy of {tech}[r-type]s. This chapter joins the
two. The ramified schema is chapter 1's schema with its positions assigned
r-types, and the assignment is carried by the indices of the Lean type of
schema-generated identifiers, so that a recurrence violating the discipline
cannot be written down. The presentation transcribes Leivant III section 2.3
{citep leivant3}[].

# Schema-generated identifiers

{name GebLean.Ramified.RIdent}`RIdent A Γ τ` is the type of identifiers the schema
generates over a base algebra `A`, indexed by a context `Γ : List RType` — the
r-types of the identifier's arguments, in order — and a result {tech}[r-type]
`τ`. An identifier is a finite tree: each node applies one schema former to
non-recursive data, and the node's children are the previously defined
identifiers that the former refers to. Leivant III's stratification of
definitions, in which each identifier is introduced by one equation group over
identifiers already introduced, is exactly this well-foundedness.

Three shapes carry the non-recursive data, one per schema former.
{name GebLean.Ramified.DefnShape}`DefnShape` holds an explicit definition: a
defining term over the base signature extended by one hole operation per
occurrence of a previously defined identifier.
{name GebLean.Ramified.MrecShape}`MrecShape` holds a
{tech}[monotonic] ramified recurrence, Leivant III eq. (4), and
{name GebLean.Ramified.FrecShape}`FrecShape` a {tech}[flat] recurrence, eq. (5).
Both recurrence shapes hold the same non-recursive data — the r-types of the
{tech}[recurrence parameters] — and differ in the index they force on the
context. {name GebLean.Ramified.RIdent.defn}`RIdent.defn`,
{name GebLean.Ramified.RIdent.mrec}`RIdent.mrec` and
{name GebLean.Ramified.RIdent.frec}`RIdent.frec` are the derived formers, each
taking its shape's data together with the identifiers filling the children.

# Monotonic ramified recurrence

Leivant III eq. (4) defines `f` by one equation per {tech}[constructor labels]
`c_i`, of the form `f (x, c_i (a_1, …, a_{r_i})) = g_{c_i} (x, φ_1, …, φ_{r_i})`,
where `φ_j = f (x, a_j)`. The step function reads the parameters and the
{tech}[recursive results] and not the {tech}[subterms], which is what makes the
recurrence monotonic in chapter 1's sense. The ramification is the r-type
assignment laid over this shape.

```signature
GebLean.Ramified.RIdent.mrec
    {A : GebLean.Ramified.AlgSig} (params : List GebLean.Ramified.RType)
    (τ : GebLean.Ramified.RType)
    (steps : (i : A.B) →
      GebLean.Ramified.RIdent A (params ++ List.replicate (A.ar i) τ) τ) :
    GebLean.Ramified.RIdent A (params ++ [GebLean.Ramified.RType.omega τ]) τ
```

{margin}[The result index: the context ends at the recurrence argument's
r-type.]
The identifier formed has context `params ++ [RType.omega τ]` and result `τ`.
The {tech}[recurrence parameters] occupy the initial segment, at r-types the
caller chooses; the {tech}[recurrence argument] occupies the final position, at
the {tech}[`Omega`-type] `RType.omega τ`, against an output at `τ`.

{margin}[The step index: parameters, then one recursive result per subterm.]
Each step function is itself an identifier, of context
`params ++ List.replicate (A.ar i) τ` and result `τ`: the same parameters,
followed by one argument per subterm of the constructor `i`, all at `τ`. These
arguments are the recursive results. No position of a step function carries the
subterms, so nothing but the parameters and the recursive results is available
to it.

Read through the tower sorts of chapter 3, where `τ` is `RType.tower m` and
`RType.omega τ` is `RType.tower (m + 1)`, the two indices say that a recursion's
output sits one {tech}[tier] below its recurrence argument's. This is Leivant
III's discipline: the recurrence argument is one tier above the output, and a
recursive result, arriving at `τ`, is one tier too low to serve as the
recurrence argument of a recurrence of the same form. A recursion's own values
therefore cannot re-enter a recurrence position, and the nesting that chapter 2
used to climb the tower of exponentials terminates after a number of stages
fixed by the tier of the outermost argument.

# Flat recurrence

Leivant III eq. (5) defines `f` by one clause per constructor label, of the form
`f (x, c_i (a_1, …, a_{r_i})) = h_{c_i} (x, a_1, …, a_{r_i})`. The clause reads
the parameters and the subterms and has no recursive results available, so the
schema performs a case distinction on the outermost constructor.

```signature
GebLean.Ramified.RIdent.frec
    {A : GebLean.Ramified.AlgSig} (params : List GebLean.Ramified.RType)
    (τ : GebLean.Ramified.RType)
    (clauses : (i : A.B) →
      GebLean.Ramified.RIdent A
        (params ++ List.replicate (A.ar i) GebLean.Ramified.RType.o) τ) :
    GebLean.Ramified.RIdent A (params ++ [GebLean.Ramified.RType.o]) τ
```

The context ends at `RType.o` rather than at an {tech}[`Omega`-type], and each
clause takes the subterms at `RType.o` as well. The tier license that
`RType.omega` grants is what pays for a recursive result; a flat recurrence
produces none, so there is nothing for the license to pay for and no tier is
spent. Requiring `RType.omega τ` in the final position would restrict where flat
recurrences may be formed without restricting anything they can compute. The
output r-type `τ` is unconstrained by the argument's, since no value at `τ` is
fed back into the recurrence.

# Inexpressibility rather than rejection

The r-type assignment is in the index of the constructor's result type, not in a
predicate applied to a term already built. {name GebLean.Ramified.RIdent.mrec}`RIdent.mrec`
returns an inhabitant of `RIdent A (params ++ [RType.omega τ]) τ` and of no
other index, so there is no monotonic recurrence whose recurrence argument sits
at the same {tech}[object type] as its output, or below it: such an identifier
is not an ill-formed element of `RIdent` but an element of a type that has no
inhabitant of that description. Chapter 1's
{name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse`, uniform in its result
type `C`, admits every nesting the ramified schema excludes; the difference
between the two is carried entirely by the indices.

# Tier erasure in the denotation

{name GebLean.Ramified.RIdent.interp}`RIdent.interp` sends an identifier of
context `Γ` and result `τ` to a function from an environment over `Γ` to a value
at `τ`, over the standard carriers `RType.interp (FreeAlg A)`. Chapter 3 recorded
that every {tech}[object type] denotes a copy of the base carrier, whichever
object type it is; {name GebLean.Ramified.RType.interp_isObj}`RType.interp_isObj`
states the identification.

The denotation therefore erases what the indices enforce. A recurrence argument
at `RType.omega τ` and a value at an object type `τ` inhabit the same set, and
the interpretation of a monotonic recurrence reads the argument as a base-carrier
element and runs {name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse` on it
with the monotonic step function; the interpretation of a flat recurrence runs
the same operation with the flat step. Tier erasure is what makes ramification a
restriction on which functions are definable rather than a change to what any
one definition computes: the equations are chapter 1's equations, and the tiers
govern only which equation groups may be written.
