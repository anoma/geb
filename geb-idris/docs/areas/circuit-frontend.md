# Circuit frontend

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area records one specific application of Geb: the use of its
categorical structure as a frontend for compiling user programs to
arithmetic circuits (targeting VampIR/Alucard). It owns no dedicated
source module; it documents an application framing that the original
`README.md` introduced and that remains the primary narrative of the
`geb-idris` codebase.

## Mathematical context

The compilation pipeline as described in
[`README.md`](../../README.md) proceeds through three
levels.

The back-end category has as objects possibly-empty ranges of natural
numbers (`NatRange`, `AugNatRange`) and as morphisms polynomial
operations together with division, modular reduction, and
range-extension/restriction operators. Coproduct introduction
compiles to addition, product introduction to multiplication,
and coproduct elimination (`RNMSwitchF`) to a less-than test;
projection (product elimination) compiles to `div`/`mod`. Polynomials
are represented in a normalized sorted list of `(power, coefficient)`
pairs (`PolyShape`), making isomorphism decidable by list equality.

The intermediate level is the zeroth-order topos of Geb, called
"Programmer's FinSet" in the Geb notes. It is the smallest category
closed under initial object, terminal object, finite products, finite
coproducts, equalizers, and coequalizers. Equalizers appear as
`Either`-valued predicates; coequalizers as predicates together with
normalizer functions that pick canonical representatives of each
equivalence class. Being a topos, it supports dependent types at the
zeroth order.

User-defined data structures occupy the category of polynomial
endofunctors of that topos. Objects are polynomial endofunctors
described by `PolyShape`; morphisms are natural transformations,
given by a position map `onPos` (matching on constructors of the
source polynomial) and a direction map `onDir` (selecting fields
contravariantly). Compilation uses `RNMSwitchF` to dispatch on the
output of `onPos` when generating circuits.

Two further front-end layers are described. A recursive macro
front-end allows writing programs that generate circuits of
parameterized depth by iterating a functor; for example,
`List[n] = 1 + x + ... + x^(n-1)` is obtained by iterating
the list functor `n` times. An STLC front-end compiles
simply-typed lambda calculus to the zeroth-order topos via
standard categorical semantics (following the "compiling to
categories" approach of Elliott 2017).

## Modules

This area owns no dedicated source module. The constructions it draws
on — polynomial endofunctors, the categorical vocabulary over `Type`,
and the language definitions — live in the polynomial-functors,
library, and geb-language areas.

The source narrative for this area is
[`README.md`](../../README.md).

## Dependencies

- [Polynomial functors](polynomial-functors.md)
- [Geb language](geb-language.md)

## Pointers

- [`README.md`](../../README.md) — primary narrative; describes the
  full compilation pipeline from STLC through the zeroth-order topos
  to the back-end category of natural-number ranges.
- [`EXAMPLES.md`](../../EXAMPLES.md) — test sessions illustrating
  Geb functions.
- The `geb-idris` codebase is the predecessor Idris 2 implementation;
  it is largely superseded by the Lean 4 continuation in `geb-lean`.
  Circuit compilation to VampIR/Alucard is not the main purpose of
  the active Lean work; it is the original motivating application
  recorded here for context.
