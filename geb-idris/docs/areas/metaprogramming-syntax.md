# Metaprogramming and syntax

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area provides the concrete syntactic layer of Geb: abstract
syntax trees for Geb terms (binary trees and S-expressions), the
quiver- and (co)presheaf-figure infrastructure for describing
diagram shapes, and an early-stage telescope framework for
dependent contexts. It is the part of the codebase closest to
surface syntax and metaprogramming support, sitting above the
polynomial-functor and internal-category foundations.

## Mathematical context

The surface-syntax layer draws on three standard bodies of
mathematics. The S-expression representation is the classical
Lisp-family encoding of tree-structured terms, here given a
categorical treatment via initial algebras (`BTExp`, `FrSExpM`)
and their catamorphisms; the parameterized variant `FrSExpM atom
ty` is the free monad on `SExpF atom` (Awodey, *Category Theory*,
ch. 10; Barr–Wells, *Toposes, Triples and Theories*, ch. 4).
The figures/quiver layer formalizes the notion of a *diagram
shape* as a functor from a small index category to `Type`,
following the presheaf / generic-figures approach to category
theory (Lawvere–Rosebrugh, *Sets for Mathematics*, ch. 7;
nLab, "generic figure"). `Copresheaf` and `IndexCat` give the
functorial notion of diagram; `PrafunctorData` attaches polynomial
arenas to positions and directions of a polynomial functor,
connecting diagram shapes to the parametric-right-adjoint
literature (Weber, "Generic morphisms, parametric representations
and weakly cartesian monads", *Theory and Applications of
Categories*, 2004). The telescope index type `TelIdx` is an
early-stage encoding of de Bruijn / dependent-context telescopes
(de Bruijn, *Selected Papers on Automath*, 1994; Martin-Löf,
"An intuitionistic theory of types", 1975), indexing position
types within a polynomial functor by Nat-valued vectors.

## Modules

- [`src/LanguageDef/Syntax.idr`](../../src/LanguageDef/Syntax.idr)
  — binary trees and S-expressions as initial algebras, together
  with their catamorphisms and substitution combinators.
  `BTExp atom` is the free binary tree on `atom`; `FrSExpM atom
  ty` is the free S-expression monad (S-expressions with
  variables of type `ty`, closed at `ty = Void`); `frsxCata` /
  `frslCata` are the mutual catamorphisms over the combined
  expression / list algebra `FrSXLAlg`.
  Provenance: known mathematics — classical initial-algebra /
  free-monad encoding of tree-structured terms; standard in the
  functional-programming and categorical-semantics literature
  (Awodey, *Category Theory*; Barr–Wells, *Toposes, Triples and
  Theories*). Searched 2026-05-31, scope nLab, the cited
  literature.

- [`src/LanguageDef/Metaprogramming.idr`](../../src/LanguageDef/Metaprogramming.idr)
  — stub module re-exporting `LanguageDef.Expression`; currently
  contains no declarations of its own beyond the import.
  It marks the intended extension point for metaprogramming
  support over the Geb surface language.
  Provenance: cat 1 (standard import re-export pattern);
  no substantive declarations to assess. Searched 2026-05-31,
  scope module file.

- [`src/LanguageDef/Figures.idr`](../../src/LanguageDef/Figures.idr)
  — quivers, paths, (co)presheaves, and parametric-right-adjoint
  functors over index categories. `MLQuiver` defines metalanguage
  quivers as functors from the walking quiver; `PCQuiver` is the
  path-closure (reflexive–transitive-closure) monad on quivers;
  `Copresheaf` and `IndexCat` package the copresheaf / diagram
  data, and `PrafunctorData` / `InterpPRAF` give the
  polynomial-arena interpretation of a parametric right adjoint
  over index categories.
  Provenance: known mathematics — metalanguage quivers and path
  closure are standard (nLab, "quiver"; Lawvere–Rosebrugh, *Sets
  for Mathematics*); `PrafunctorData` follows Weber's PRA
  construction (Weber 2004); no prior Idris formalization found.
  Searched 2026-05-31, scope nLab, the cited literature.

- [`src/LanguageDef/Telescope.idr`](../../src/LanguageDef/Telescope.idr)
  — early-stage index and position types for dependent-context
  telescopes, built over polynomial-functor and slice-polynomial
  machinery. `TelIdx` (= `Sigma Nat TelIdxN`) and `TelIdxN`
  encode de Bruijn–style telescope indices as iterated
  applications of `VectF`; `PNmu` is the least fixed point of the
  corresponding position functor `PNf`; `PFpra1` / `PFpra2`
  begin a two-level PRA functor decomposition over
  `MLDirichCatObj`. The module ends at a skeleton "Objects"
  section header, indicating work in progress.
  Provenance: cat 2 (de Bruijn dependent-context telescopes —
  de Bruijn 1994; Martin-Löf 1975); the specific polynomial
  encoding of telescope indices here appears to be novel
  (unverified). Searched 2026-05-31, scope nLab, the cited
  literature.

## Dependencies

- [`geb-idris/docs/areas/library.md`](library.md) — `IdrisUtils`,
  `IdrisCategories`, `IdrisAlgebra` utilities used throughout.
- Polynomial-functors area (no area doc yet) — `Figures.idr` and
  `Telescope.idr` import `PolyCat`, `DiagramCat`,
  `SlicePolyCat`, `PolySliceCat`, and `SlicePolyUMorph` from
  that area; they are filed here by explicit area assignment (see
  `_partition-notes.md`).

## Pointers

- This material is part of the Idris predecessor codebase;
  the Lean port (`geb-lean/`) has not yet taken up a
  metaprogramming-syntax layer corresponding to these modules.
- `Syntax.idr` imports `LanguageDef.Atom`, which is assigned to
  the `logic-refinement` area.
- `Metaprogramming.idr` imports `LanguageDef.Expression`, which
  is assigned to the `geb-language` area.
- Development status: `Syntax.idr` and `Figures.idr` are
  substantively developed; `Telescope.idr` is a partial skeleton;
  `Metaprogramming.idr` is a stub.
