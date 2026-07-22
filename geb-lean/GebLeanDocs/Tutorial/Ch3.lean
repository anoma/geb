import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.RType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Ramified types

Part I chapter 3 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "Ramified types" =>

Chapter 1 fixed the machinery that generates a free algebra from a finitary
signature; chapter 2 showed that the recurrence schema over such an algebra,
taken without restriction, reaches every level of a tower of exponentials.
This chapter fixes what the restriction restricts: a hierarchy of types that
assigns every recurrence position a place in a fixed order, so that chapter 4
can state the ramified schema as a typing discipline rather than as a side
condition on chapter 1's schema. The type grammar transcribes Leivant III
section 2.3 {citep leivant3}[].

# r-types as a free algebra

{name GebLean.Ramified.RType}`RType` is
{name GebLean.Ramified.FreeAlg}`FreeAlg` {name GebLean.Ramified.rTypeSig}`rTypeSig` — the
construction of chapter 1, applied to a new signature. Introducing the type
layer therefore costs nothing beyond a choice of labels and arities:
{name GebLean.Ramified.RTypeShape}`RTypeShape` has three constructors — a
nullary `o`, a binary `arrow`, and a unary `omega` — and `rTypeSig` assigns
them arities `0`, `2`, `1`. An element of `RType` is an {deftech}[r-type],
Leivant III's term.

Three derived constructors present the shapes at their arities.
{name GebLean.Ramified.RType.o}`RType.o` is the base type. Given r-types `a`
and `b`, {name GebLean.Ramified.RType.arrow}`RType.arrow` applied to `a` and
`b`, written `RType.arrow a b`, is the function type from `a` to `b`,
Leivant III's `a → b`. Given an r-type `a`,
{name GebLean.Ramified.RType.omega}`RType.omega` applied to `a`, written
`RType.omega a`, is Leivant III's `Omega a`: the typing license for an
element of the base algebra to serve as the {tech}[recurrence argument] of a
recurrence whose {tech}[recursive results] carry type `a`.

# Object types and Omega-types

An r-type of the form `RType.omega a` is an {deftech}[`Omega`-type], for any
r-type `a`. `RType.o` and every `Omega`-type together are the
{deftech}[object type]s: the r-types an r-type-generated algebra's elements
themselves inhabit, as opposed to the function types `arrow` builds over
them. {name GebLean.Ramified.RType.IsObj}`RType.IsObj` is the object-type
predicate, holding of `RType.o` and of `RType.omega a` for every `a`, and of
nothing else.

# Towers and tiers

{name GebLean.Ramified.RType.tower}`RType.tower` iterates `omega` on `o`:
`RType.tower 0` is `RType.o`, and `RType.tower (m + 1)` is
`RType.omega (RType.tower m)`, so `RType.tower m` is Leivant III's
`Omega^m o` (section 2.4(3)). The natural number `m` indexing this iterate is
the {deftech}[tier] of the object type `RType.tower m`.
{name GebLean.Ramified.RType.IsTower}`RType.IsTower` is the predicate holding
of the r-types reached this way — a chain of `omega`s terminating in `o` —
so a tier is defined only for the object types the predicate picks out, not
for every object type: an `Omega`-type built over an `arrow` carries no tier.

# The standard denotation

{name GebLean.Ramified.RType.interp}`RType.interp` denotes an r-type over a
carrier: `RType.interp C (RType.arrow a b)` is the function space from
`RType.interp C a` to `RType.interp C b`, and every object type denotes a
copy of `C` itself, regardless of which object type it is or, for a tower
sort, which tier it carries. Leivant III section 2.7 identifies the
denotations of `o` and of every `Omega a` this way {citep leivant3}[];
{name GebLean.Ramified.RType.interp_isObj}`RType.interp_isObj` states the
identification. `Omega` therefore changes an r-type's tier and its standing
as a recurrence argument without changing what it denotes.

# The first-order tier reading

The tower sorts alone recover a familiar picture. First-order ramified
recurrence assigns each argument one of finitely many tiers and lets a
recursion's output sit one tier below its recurrence argument's; Leivant III
presents `RMRec-omega` as this discipline raised to higher type
{citep leivant3}[]. Read through the tower sorts, tier `m` is
`RType.tower m`, and moving from tier `m` to tier `m + 1` is exactly
`RType.omega`:

```lean
open GebLean.Ramified in
example : RType.tower 2 = RType.omega (RType.omega RType.o) := rfl
```

The r-types built with `arrow`, and the `Omega`-types over them, have no
place in this reading; they are what the higher-type system adds.
