# geb-idris documentation

The Idris-2 implementation of Geb: the predecessor to the active Lean
formalisation under `geb-lean/`. It contains a large body of
category-theoretic and polynomial-functor code, much of it not yet
reproduced in Lean. For the project's own circuit-compilation framing
see [`../README.md`](../README.md); for worked examples see
[`../EXAMPLES.md`](../EXAMPLES.md).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Areas](#areas)
- [Reference documents](#reference-documents)
- [Coverage](#coverage)

<!-- END doctoc -->

## Areas

The source under `src/` is organised into nine areas, each with an
overview document under [`areas/`](areas/) naming the area's main
definitions and situating them in known mathematics and in Geb.

- [`areas/library.md`](areas/library.md) — Idris-level utilities and
  the category-theory vocabulary (`IdrisUtils`, `IdrisCategories`,
  `IdrisAlgebra`) on which everything else builds.
- [`areas/polynomial-functors.md`](areas/polynomial-functors.md) —
  polynomial endofunctors and their categories, slice and
  dependent-polynomial constructions: Geb's theory of data structures.
- [`areas/internal-cats-profunctors.md`](areas/internal-cats-profunctors.md)
  — internal categories, the families/cofamilies and twisted-arrow
  constructions, and profunctors, difunctors, and (co)ends.
- [`areas/geb-language.md`](areas/geb-language.md) — the assembled
  language: the zeroth-order topos (Programmer's FinSet), term syntax
  and its interpretation, and algebraic-datatype categories.
- [`areas/foundational-cats.md`](areas/foundational-cats.md) — general
  category-theoretic machinery: quivers, finite categories,
  adjunctions, universal properties, spans/cospans, parametric right
  adjoints, and named small categories.
- [`areas/logic-refinement.md`](areas/logic-refinement.md) — the logic,
  quotient- and refinement-type, effects, and embedded-language
  substrate, and the `FullLanguageDef` assembly capstone.
- [`areas/recursion-targets.md`](areas/recursion-targets.md) —
  combinatory and term-rewriting computation models: tree calculus,
  Nock, binary trees.
- [`areas/metaprogramming-syntax.md`](areas/metaprogramming-syntax.md)
  — abstract syntax, telescopes, figure-shapes, and metaprogramming
  support.
- [`areas/circuit-frontend.md`](areas/circuit-frontend.md) — Geb as a
  frontend for compiling through categories to arithmetic circuits:
  one application of the constructions above (the original README's
  framing), not a separate body of code.

## Reference documents

Background and topic notes that are not per-area overviews:

- [`geb-syllabus.md`](geb-syllabus.md) — Geb reading-group syllabus
  (category theory and polynomial-functor background).
- [`mldirichf-generalization.md`](mldirichf-generalization.md) —
  MLDirichF generalization plan.
- [`profunctor-end-characterization.md`](profunctor-end-characterization.md)
  — characterizing ends of polynomial profunctors.
- [`twisted-arrow-copresheaf-analysis.md`](twisted-arrow-copresheaf-analysis.md)
  — copresheaves versus presheaves on twisted-arrow categories.

## Coverage

The area documents partition the non-test source: every module under
`src/` other than the test trees (`*/Test/*`) is named in exactly one
area document. The partition is recorded in
[`areas/_partition-notes.md`](areas/_partition-notes.md) and checked by
`docs/tools/check-area-coverage.sh idris` from the repository root.
