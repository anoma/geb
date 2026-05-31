# The Geb language

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

This area assembles the Geb language as a typed, categorically-grounded
system: the zeroth-order topos called "Programmer's FinSet" (initial
and terminal objects, finite (co)products, (co)equalizers), the
expression syntax and its interpretation into categorical semantics,
the algebraic-datatype categories that model user-defined recursive
types, and the foundational universal-property vocabulary from which
all of these are derived. Together these modules form the core
language of Geb as an executable, homoiconic, multi-category
programming system.

## Mathematical context

The Geb language rests on a zeroth-order topos: a category inductively
defined as the smallest one closed under initial object, terminal
object, finite products, finite coproducts, equalizers, and
coequalizers. This is "Programmer's FinSet" (PFS) in the Geb notes
(Geb hackmd, <https://hackmd.io/qxHXAuyYQuGMUYSZ_neuXA?view>); it is a
pretopos in the sense of Johnstone (*Sketches of an Elephant*, vol. I,
A.1.4) but without power objects, reflecting the design choice to
exclude exponential objects from the core (a deliberate analogy with
the arithmetic required for Gödel self-representation). Objects of PFS
index the polynomial endofunctors that classify user-defined ADTs;
morphisms between those functors are natural transformations,
corresponding to pattern-matching functions.

The expression and interpretation layers give PFS and its polynomial
extension a term syntax and a semantics: expressions are encoded as
S-expressions over a reserved atom vocabulary, and interpretation maps
them into categorical structures in the host language (Idris).
`UniversalCategory` axiomatizes what it means to define a category via
universal properties and records the design rationale for the full Geb
language; `Interpretation` and `Expression` are stubs that re-export
that vocabulary.

`ADTCat` encodes basic ADTs (booleans, pairs, binary trees,
S-expressions) as polynomial functors (arenas), realizing Geb's
user-defined-data tier via initial algebras of polynomial endofunctors.

`Theories` explores categorical substrate structures — a computational
category close to bit-circuits (`CompCatObj`/`CompCatMorph`) and a
mutually-recursive family of slice categories — that sit between the
core topos and the back-end compilation target.

`GebTopos` builds on PFS and supplies the internal Yoneda machinery —
contravariant and covariant hom-representability types — needed to
state and use the Yoneda lemma internally within a category specified
by hom-slice data.

`Geb` assembles the full language, connecting `QType` (a quotient-type
layer for refined types) with `DiagramCat` (diagram-indexed categories)
via reachability W-types and free polynomial arenas over
`SlicePolyEndoFunc`.

## Modules

- [`src/LanguageDef/ProgFinSet.idr`](../../src/LanguageDef/ProgFinSet.idr)
  — the zeroth-order topos "Programmer's FinSet". `DRFSObj` is the
  inductive type of objects (initial `DRFS0`, terminal `DRFS1`,
  coproduct `DRFSC`, product `DRFSP`); `DDRFSMorph` gives morphisms
  via the universal-property adjuncts (coproduct elimination
  `DDRMcpR`/left adjuncts, product introduction `DDRMprL`/right
  adjuncts, distributivity `DDRMdistrib`); `DigTObj`/`DigTMorph`
  sketches a digital-topos extension with exponentials.
  Provenance: category 1 (novel — Geb's specific inductive topos
  construction) — the closure under the six listed universal
  properties with morphisms given by the resulting adjunctions is
  Geb-specific; the individual constructions (products, coproducts,
  equalizers) are standard (Johnstone, *Sketches of an Elephant*,
  vol. I). Searched 2026-05-31, scope nLab, Geb notes hackmd,
  general knowledge.

- [`src/LanguageDef/GebTopos.idr`](../../src/LanguageDef/GebTopos.idr)
  — internal Yoneda lemma utilities for categories specified by
  hom-slice data. `HomRep` collects the four variance-combination
  hom-representability types (`CovarToCovar`, `CovarToContravar`,
  `ContravarToContravar`, `ContravarToCovar`); `YonedaHomSetRep` and
  `YonedaCatRep` assemble these into a Yoneda-representability datum
  for a whole category.
  Provenance: category 2 (known mathematics, formalized in this Idris
  codebase) — the Yoneda lemma and hom-representability are standard
  (Mac Lane, *Categories for the Working Mathematician*, ch. III;
  nLab, [Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma)).
  Searched 2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/Theories.idr`](../../src/LanguageDef/Theories.idr)
  — categorical substrate structures intermediate between the core
  topos and compilation targets. `CompCatObj`/`CompCatMorph` define
  a category of bit-circuit objects (unit `CC1`, bit `CCB`, product
  `CCP`) with conditional `CCif`, projection, and pairing morphisms;
  `MinMLCat`/`MinMLObj`/`MinMLMorph` sketch a mutually-recursive
  family of slice categories indexed by objects of `MinMLCat`.
  Provenance: category 1 (novel — Geb's specific compilation-substrate
  categories); `CompCatObj` corresponds to a fragment of the Alucard /
  VampIR back-end described in the Geb README, not formalized
  elsewhere. Searched 2026-05-31, scope nLab, Geb notes hackmd,
  general knowledge.

- [`src/LanguageDef/ADTCat.idr`](../../src/LanguageDef/ADTCat.idr)
  — algebraic-datatype categories via polynomial functors. `BoolF`
  and `PairF` are arenas (`PolyFunc`) and `BinTree'F` is a
  parameterized arena (`ParamPolyFunc`); their initial algebras via
  `PolyFuncMu` / `pfCata` give, respectively,
  the Bool, product, and binary-tree types; `SexpXPos`/`SexpPosBase`
  begin an S-expression arena. The module establishes the pattern by
  which all user-defined recursive types in Geb are encoded as
  polynomial-functor initial algebras.
  Provenance: category 2 (known mathematics, formalized in this Idris
  codebase) — polynomial-functor initial algebras as a model of
  algebraic data types are standard (Abbott–Altenkirch–Ghani,
  *Containers*, 2005; nLab,
  [polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)).
  Searched 2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/Interpretation.idr`](../../src/LanguageDef/Interpretation.idr)
  — re-export stub for `UniversalCategory` (documented in the
  [foundational and finite-category machinery](foundational-cats.md)
  area); adds no declarations of its own. Its role is to provide a
  named boundary at which interpretation-layer consumers import the
  universal-category vocabulary.
  Provenance: not applicable — no mathematical content; organizational
  infrastructure only.

- [`src/LanguageDef/Expression.idr`](../../src/LanguageDef/Expression.idr)
  — re-export stub for `Interpretation`; adds no declarations of its
  own. Its role is to provide a named boundary at which expression-layer
  consumers import the interpretation vocabulary transitively.
  Provenance: not applicable — no mathematical content; organizational
  infrastructure only.

- [`src/LanguageDef/Geb.idr`](../../src/LanguageDef/Geb.idr)
  — top-level assembly of the Geb language. `QTDCat` converts the
  `QType` quotient-type category into a `DiagramCat` diagram category
  via `catToDiagForget`; `ReachableBase`/`ReachableFreeF` define
  reachability of elements of a type under iteration of a function as
  the initial algebra of a W-type polynomial endofunctor; `PolyFuncMu`
  and `PolyFuncMuPF` assemble reachable arenas into a polynomial
  functor whose positions and directions are the reachable ones.
  Provenance: category 1 (novel — Geb's specific encoding of
  reachability via W-type polynomial endofunctors and the
  free-polynomial-arena construction); the W-type construction follows
  the standard theory of W-types (Martin-Löf; Moerdijk–Palmgren,
  *Wellfounded trees*, 2000) applied in a Geb-specific way. Searched
  2026-05-31, scope nLab, general knowledge.

## Alternative formulations

The codebase contains two representations of the zeroth-order topos.
`DRFSObj`/`DDRFSMorph` in
[`src/LanguageDef/ProgFinSet.idr`](../../src/LanguageDef/ProgFinSet.idr)
is the "reduced FinSet" form: objects are inductive, morphisms are
given by explicit universal-property constructors (adjuncts). A
second, earlier sketch, `DigTObj`/`DigTMorph` in the same file,
extends the reduced form with a `DTO_FN` exponential constructor
but leaves morphisms and the hom-object function partially
unimplemented (hole `dtHomObj_hole`). Both encode the same intended
zeroth-order topos; the `DigTObj` form is exploratory material.

## Dependencies

This area builds on:

- [Library](library.md) — `IdrisUtils`, `IdrisCategories`, and
  `IdrisAlgebra` supply the slice-category calculus, polynomial
  functors, free monads, and F-algebra machinery that every module
  here uses.

The polynomial-functors, internal-categories-and-profunctors, and
foundational-categories areas (not yet assigned separate area docs)
contribute `PolyCat`, `InternalCat`, `SlicePolyCat`, `QType`,
`DiagramCat`, and related modules imported by `Geb.idr` and
`ADTCat.idr`; see
[`docs/areas/_coverage.tsv`](_coverage.tsv) for the module
partition.

## Pointers

- The Idris codebase is the original implementation; these modules
  are largely superseded by the Lean 4 reformalization in
  `geb-lean/`. Readers seeking the actively maintained formulations
  should consult the Lean area docs under `geb-lean/docs/areas/`.
- [`geb-idris/EXAMPLES.md`](../../EXAMPLES.md) illustrates the Geb
  language by example, including evaluation of morphisms in the
  zeroth-order topos.
- [`geb-idris/README.md`](../../README.md) describes the overall
  design, including the back-end circuit category and how polynomial
  endofunctors of PFS classify user-defined data structures.
