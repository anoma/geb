# Recursion and compilation targets

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

This area provides three computation models that Geb can target or
formalize: a binary-tree datatype that serves as the shared substrate
for term-rewriting and structured data, an implementation of Jay's
tree calculus as a total, purely structural rewriting system over that
substrate, and an implementation of the Nock combinator machine as a
fuel-bounded evaluator over a noun/formula language.

## Mathematical context

The three modules together span a hierarchy of computation models
built on binary trees. Binary trees are the free monad of the product
monad — the least fixed point of the functor `BinTreeF(atom, -) =
atom + (- × -)` — giving them the universal property of being the
free algebra for a binary operation over a set of atoms; catamorphisms
(`binTreeCata`) are exactly the free-algebra morphisms.

Tree calculus, introduced by Barry Jay (*Reflective Programs in Tree
Calculus*, 2021, arXiv:2108.00969), is a computation model whose
programs and data share the same type — unlabeled binary trees — and
whose evaluation rule is a small structural rewriting relation on
those trees. The three-constructor leaf/stem/fork shape (Jay's
`△`, `△ x`, `△ x y`) is the primitive combinator basis; every
computable function is representable as a tree. This reflective
quality — programs are data and data is programs — makes tree calculus
a natural target for Geb's self-representational objectives.

The Nock combinator machine (Urbit specification, c. 2010–2012,
<https://urbit.org/docs/nock/>) is a deterministic reduction machine
whose data model is the inductively defined type of nouns (atoms or
cells) and whose computation is given by twelve opcodes (`Formula`).
Nock is complete for primitive-recursive functions and is used in
Urbit as a minimal substrate for a deterministic operating system.

## Modules

- [`src/LanguageDef/BinTree.idr`](../../src/LanguageDef/BinTree.idr)
  — the base binary-tree datatype and its free-monad structure.
  `BinTreeMu` is the least fixed point of `BinTreeF`, the bifunctor
  `atom + (- × -)`, identified with `ProdFM`, the free monad of the
  product monad; `binTreeCata` is the catamorphism; `prodFMEval` is
  the free-algebra evaluation morphism that is the right adjunct of
  the free/forgetful adjunction.
  Provenance: category 2 (known mathematics, formalized in this Idris
  codebase) — `BinTreeMu` as initial algebra / free monad of the
  product monad is standard (Barr–Wells, *Toposes, Triples, and
  Theories*, §4; nLab,
  [free monad](https://ncatlab.org/nlab/show/free+monad)). Searched
  2026-05-31, scope Idris2 standard library, nLab.

- [`src/LanguageDef/TreeCalculus.idr`](../../src/LanguageDef/TreeCalculus.idr)
  — Jay's tree calculus over unlabeled binary trees. `NatTree` is the
  least fixed point of `NatTreeF = BinTreeF Unit` (binary trees with
  unit atoms, i.e., unlabeled trees); `Δ`, `Ε`, and `Ɩ` are the
  leaf, application, and stem constructors; `natTreeCata` and its
  stack-machine variant `natTreeCataStack` fold algebras over trees;
  `NSExp` and the mutual conversions `RNSExpToNatTree` /
  `NatTreeToRNSExp` establish an isomorphism between `NatTree` and the
  type of unlabeled S-expressions, matching Jay's specification.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — tree calculus is due to Barry Jay (*Reflective Programs
  in Tree Calculus*, arXiv:2108.00969, 2021); the Idris encoding is an
  independent formalization. Searched 2026-05-31, scope Idris2
  standard library, nLab, arXiv. See also the cross-reference note
  in Pointers.

- [`src/LanguageDef/Nock.idr`](../../src/LanguageDef/Nock.idr)
  — the Nock combinator machine. `Noun` (atoms and cells) and
  `Formula` (the twelve Nock opcodes: `Slot`, `Quote`, `Deep`,
  `Bump`, `Inc`, `Eq`, `If`, `Comp`, `Push`, `Call`, `Hint`,
  `Core`) are the two mutually dependent datatypes; `evalBounded`
  is the fuel-limited evaluator; `slot` is the axis-addressing
  function on nouns.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — Nock is specified by the Urbit project
  (<https://urbit.org/docs/nock/>); this is an independent
  formalization. Searched 2026-05-31, scope Idris2 standard library,
  nLab.

## Alternative formulations

None. Each module formalizes a distinct computation model; there are
no competing formulations of the same concept within this area.

## Dependencies

This area depends on the [Library](library.md) area
(`Library.IdrisUtils`, `Library.IdrisCategories`) for the categorical
vocabulary (`BinTreeF` as a bifunctor, `Algebra`, `Coalgebra`,
free-monad infrastructure). `BinTree` is the base module for this
area; `TreeCalculus` imports it directly, and `Nock` is independent
of the tree-calculus formalization but sits at the same level.

## Pointers

The Idris codebase is the predecessor implementation; the
tree-calculus formalization developed here has been substantially
reformalized in Lean 4 under `geb-lean`. Readers looking for the
actively maintained tree-calculus formulations should consult the
Lean areas documentation index at
[`geb-lean/docs/areas/`](../../../geb-lean/docs/areas/).

The Idris work is preserved as historical context and is not under
active development.
