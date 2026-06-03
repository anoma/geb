# Library

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Alternative formulations](#alternative-formulations)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area provides the Idris-level foundations on which all of
`LanguageDef` builds: general-purpose utilities, category-theoretic
vocabulary over Idris's `Type`, algebraic structures (F-algebras and
free monads), and a thin aggregation shim that re-exports
`LanguageDef` for category-theoretic consumers.

## Mathematical context

The four modules span three layers of abstraction. The utility layer
(`IdrisUtils`) supplies basic combinators, dependent-pair helpers, and
the `Subset0` type that threads erased proof obligations through
computation. The categorical layer (`IdrisCategories`) internalises
standard category theory — slices, functors, natural transformations,
profunctors, ends, and adjunctions — within Idris's `Type`, treating
types and functions as the ambient ambient category; the slice-category
subcalculus (`SliceObj`, `Pi`, `Sigma`) is the direct precursor of the
polynomial-functor and presheaf machinery in `LanguageDef`. The algebra
layer (`IdrisAlgebra`) builds on that vocabulary to define `F`-algebras
(`FAlgObj`), initial algebras, and the Eilenberg–Moore equivalence
between algebras over a monad and algebras over its underlying
endofunctor (following nLab / Barr–Wells, *Toposes, Triples, and
Theories*, §3.6). The aggregation module (`CategoryTheory`) is a stub
that imports `LanguageDef.FullLanguageDef` and re-exports it without
adding declarations.

## Modules

- [`src/Library/IdrisUtils.idr`](../../src/Library/IdrisUtils.idr)
  — general-purpose Idris utilities: function-composition operators,
  `Subset0` (a record bundling a value with an erased proof),
  dependent-pair helpers (`dpEq12`, `dpBimap`), and import aggregation
  for the Idris standard library. `Subset0` is the type other modules
  use to carry proof obligations at zero runtime cost, making it the
  most-imported declaration in the area. `Subset0` is a variant of
  the standard `Subset` type with erased predicate parameter; all
  other definitions are standard functional-programming combinators;
  we have found no prior Idris formalization of `Subset0`.

- [`src/Library/IdrisCategories.idr`](../../src/Library/IdrisCategories.idr)
  — the categorical vocabulary over `Type`: `SCat` (the bundled
  Mac Lane–Eilenberg internal category record with hom, identity,
  composition, and equational laws), `SliceObj`/`SliceMorphism`/`Pi`/
  `Sigma` (the slice-category calculus), `NaturalTransformation`
  (as a `Pi` of `AppFunctor`), and `Profunctor` (a `dimap`-based
  interface with ends and the profunctor bicategory). At 14,570 lines
  this is the largest module in the codebase; it also contains
  W-type algebras, polynomial endofunctors, Yoneda lemma instances,
  and the `FAlgObj`/`FreeMonad` types that `IdrisAlgebra` builds on.
  These structures — slice categories, natural transformations,
  profunctors, ends, polynomial functors, free monads — are standard
  category theory (Mac Lane, *Categories for the Working
  Mathematician*; nLab); we have found no prior Idris formalization
  of them.

- [`src/Library/IdrisAlgebra.idr`](../../src/Library/IdrisAlgebra.idr)
  — algebras and morphisms of `F`-algebras (`FAlgObj`, `FAlgMorph`,
  `IsInitialFAlg`), the Eilenberg–Moore equivalence between the
  algebra category of a free monad and the algebra category of its
  underlying endofunctor (`bnAlgObjToFreeObj` / `bnAlgObjFromFree` /
  `bnAlgObjToFreeIso`), and the category of free monads
  (`FreeMonadCatMorph`). The module specializes the general machinery
  to `BinNatF` (lists of booleans) as a running example.
  F-algebra categories and the Eilenberg–Moore comparison theorem
  are standard (Mac Lane, op. cit., VI.8; nLab,
  [algebra for an endofunctor](https://ncatlab.org/nlab/show/algebra+for+an+endofunctor#relation_to_algebras_over_a_monad),
  prop. 3.1; Barr–Wells, *Toposes, Triples, and Theories*, §3.6);
  we have found no prior Idris formalization of them.

- [`src/Library/CategoryTheory.idr`](../../src/Library/CategoryTheory.idr)
  — a stub module that imports `LanguageDef.FullLanguageDef` (and
  `Library.IdrisUtils`) and declares no new definitions; its purpose
  is to provide a single re-export point for category-theoretic
  consumers that need the full language definition.
  Organizational infrastructure only; it carries no mathematical
  content.

## Alternative formulations

None. Each module serves a distinct layer; there are no competing
formulations of the same concept within this area.

## Dependencies

None. This area is the foundational layer; it does not import any
other area of the `geb-idris` codebase (beyond `LanguageDef` re-exported
by the stub `CategoryTheory`).

## Pointers

The Idris codebase is the predecessor implementation; the
category-theory vocabulary developed here has been substantially
reformalized in Lean 4 under `geb-lean`. Readers looking for
the actively maintained formulations should consult the Lean
areas:

- Slice-category and profunctor machinery: see
  `geb-lean/docs/areas/category-judgments.md` for the categorical
  vocabulary used in the Lean continuation.
- The Idris work is preserved as historical context; it is not under
  active development.
