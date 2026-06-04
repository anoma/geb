# Polynomial functors

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

This area develops the theory of polynomial endofunctors and
dependent polynomial functors inside Idris's `Type`, treating them
as the primary data-structure model for Geb's language semantics.
It covers the base polynomial functor calculus, finitary variants,
slice-polynomial (dependent-polynomial) functors between slice
categories, their algebra/coalgebra/dialgebra structure, limits and
colimits, slice categories of polynomial functors, dislice
categories, and the difunctorial machinery that unifies polynomial
and Dirichlet viewpoints.

## Mathematical context

A polynomial endofunctor on `Type` is an endofunctor of the form
`P(X) = Σ_{i : I} X^{d(i)}` for a "position" type `I` and a
"direction" family `d : I → Type`; the category `Poly` of such
functors and their natural transformations is the material of
Spivak and Niu, *Polynomial Functors* (2022). The slice-category
generalization, where positions are slice objects over a base `cod`
and directions are parameterized by pairs `(position, domain
element)`, yields the *dependent polynomial functors* of
Gambino–Kock (*Polynomial functors and polynomial monads*, Math.
Proc. Cambridge Phil. Soc. 154, 2013); these coincide with the
*parametric right adjoint* (PRA) functors between presheaf
categories in the sense of Weber (*Generic morphisms, parametric
representations and weakly cartesian monads*, Theory Appl.
Categ. 13, 2004). The dislice-category construction — objects of
the category of factorizations of a bundle — simultaneously
generalizes slice and coslice categories and provides the ambient
setting for the area's most general polynomial constructions. The
algebras, coalgebras, and dialgebras of slice-polynomial functors
are the data-type semantics for Geb's recursive types and
morphism spaces. The Idris formalization is the predecessor of the
active Lean 4 development; it is not under active development.

## Modules

- [`src/LanguageDef/PolyCat.idr`](../../src/LanguageDef/PolyCat.idr)
  — the foundational polynomial-functor definitions over `Type`.
  `PolyFunc` (a `DPair Type PolyFuncDir`) is the arena type;
  `InterpPolyFunc` interprets it as an endofunctor; `PolyNatTrans`
  and `PolyNatTransComp` give the morphisms and composition of the
  `Poly` category; `CPFSliceObj` defines slice objects over a fixed
  polynomial functor. The `Poly` category and its natural
  transformations are standard mathematics (Spivak–Niu,
  *Polynomial Functors*, 2022; nLab, polynomial functor).

- [`src/LanguageDef/FinPoly.idr`](../../src/LanguageDef/FinPoly.idr)
  — finitary polynomial functors encoded via a fixed
  `MaybeParProdF` polynomial functor whose least fixpoint encodes
  the natural numbers, and a "mutual-recursion as polynomial
  finite-slice functors" development. `MaybeParProdMu` is the
  initial algebra; `MaybeParProdMuToNatPairPred` is a
  characterization of its elements as pair-predicate data.
  Finitary/bounded polynomial functors and their free monads are
  standard mathematics (nLab, finitary monad; Barr–Wells,
  *Toposes, Triples, and Theories*); the specific `MaybeParProdF`
  encoding is a local definitional choice.

- [`src/LanguageDef/GenPolyFunc.idr`](../../src/LanguageDef/GenPolyFunc.idr)
  — aggregate import module and a characterization study of arrow
  morphisms from multiple viewpoints. `DirichNTasBC` and
  `PolyNTasBC` exhibit natural transformations between Dirichlet
  and polynomial functors as base-change morphisms; the `MLDirichF1`
  family develops PRA functors on `MLDirichCatObj` via
  coproducts-of-representables (Yoneda), with `InterpMLDirichF1` and
  `MLDirichF1NT` its headline declarations. PRA functors via
  coproducts of representables follow Weber (op. cit.) and the
  nLab account of PRA functors; the Yoneda-style `MLDirichF1NT`
  formula is standard.

- [`src/LanguageDef/HigherPolyCat.idr`](../../src/LanguageDef/HigherPolyCat.idr)
  — import aggregator only (8 lines); re-exports
  `InternalCat`, `SliceFuncCat`, `SlicePolyCat`, and
  `SlicePolyUMorph` under a single name for consumers that
  need the full slice-polynomial stack. No declarations of its
  own. Organizational infrastructure only; it carries no
  mathematical content.

- [`src/LanguageDef/PolyIndTypes.idr`](../../src/LanguageDef/PolyIndTypes.idr)
  — inductive-inductive type definitions expressed in terms of
  polynomial functors, following Altenkirch–Morris (*A Categorical
  Semantics for Inductive-Inductive Definitions*, 2011).
  `FinIndIndF1` and `FinIndF2Assign` encode the shapes of
  finitely-generated inductive-inductive specifications as lists of
  constructor records; `InterpFI1` interprets the first layer as
  a polynomial functor. The polynomial-functor semantics of
  inductive-inductive types follows Altenkirch–Morris (op. cit.)
  and nLab (inductive-inductive type).

- [`src/LanguageDef/SliceFuncCat.idr`](../../src/LanguageDef/SliceFuncCat.idr)
  — the slice-category adjoint triple (dependent sum ⊣ base change
  ⊣ dependent product) over `Type`. `BaseChangeF`, `SliceSigmaF`,
  and `SlicePiF` are the three functors; `SliceSigmaPiFR` and
  `SliceSigmaPiFL` are the composite right-adjoint (base change
  then Pi) and left-adjoint (base change then Sigma) used in the
  PRA decomposition of slice-polynomial functors. The adjoint
  triple is standard slice-category theory (Johnstone,
  *Sketches of an Elephant* A1.5; nLab, dependent product).

- [`src/LanguageDef/SlicePolyCat.idr`](../../src/LanguageDef/SlicePolyCat.idr)
  — the central dependent-polynomial-functor module. `SPFData dom
  cod` (a slice object `spfdPos` over `cod` plus a direction
  family `spfdDir`) is the arena type for slice-polynomial
  functors; `InterpSPFData` is its PRA interpretation; `SPFnt` is
  the natural-transformation type; `SPFDcat` assembles these into
  a category signature. Dependent polynomial functors as PRA
  functors on slice categories follow Gambino–Kock (op. cit.)
  and Weber (op. cit.); the arena encoding is a local Idris
  choice.

- [`src/LanguageDef/SlicePolyUMorph.idr`](../../src/LanguageDef/SlicePolyUMorph.idr)
  — limits and colimits of slice-polynomial diagrams.
  `SPFDColimit` and `SPFDLimit` compute the colimit and limit of an
  `SPFData`-indexed diagram in a slice category; `SPFDColimitMonad`
  and `SPFDLimitComonad` are the associated monad and comonad
  arising from the colimit–diagonal–limit adjoint triple.
  Limits and colimits of diagrams in slice categories are
  standard (Johnstone op. cit.; nLab, colimit), as is the
  diagonal–Sigma–Pi adjoint triple for slice categories.

- [`src/LanguageDef/PolySliceCat.idr`](../../src/LanguageDef/PolySliceCat.idr)
  — the slice category of polynomial functors over a fixed base
  polynomial functor `p`. `CPFSliceObj p` bundles a polynomial
  functor with a natural transformation to `p`; `CPFSliceMorph` is
  the slice-morphism type (with commutativity proof); `PFSliceMorph`
  is a proof-free alternative whose domain object is determined
  by the commutativity condition. Slice categories of a category
  are standard (Mac Lane, *Categories for the Working
  Mathematician*, II.6); the specific slice structure over `Poly`
  is described in Spivak–Niu (op. cit., §§3–4).

- [`src/LanguageDef/SlPolyImpred.idr`](../../src/LanguageDef/SlPolyImpred.idr)
  — import aggregator only (6 lines); re-exports
  `SlicePolyCat` and `SlicePolyUMorph` for consumers that need
  the slice-polynomial-with-limits package. No declarations of
  its own. Organizational infrastructure only; it carries no
  mathematical content.

- [`src/LanguageDef/DisliceCat.idr`](../../src/LanguageDef/DisliceCat.idr)
  — the dislice category over a bundle `cat : CBundleObj`.
  `CDisliceObj` records factorizations of the bundle projection
  into two composable morphisms (with an extensional equality
  proof); `CDisliceMorph` is the morphism type; identity
  (`cdsmId`) and composition (`cdsmComp`) complete the category.
  The module also provides an arena-style presentation
  (`ADisliceObj`, `ADisliceMorph`) parallel to the categorical one.

- [`src/LanguageDef/DislicePolyCat.idr`](../../src/LanguageDef/DislicePolyCat.idr)
  — polynomial functors between dislice categories. `ADSLbc`,
  `ADSLcbc`, and `ADSLdc` provide base change, cobase change, and
  simultaneous dibase change as functors on the arena-style
  dislice category; `ADSLsigma` is the dependent-sum functor from
  a slice of a dislice category to the corresponding dislice
  category.

- [`src/LanguageDef/SlicePolyDialg.idr`](../../src/LanguageDef/SlicePolyDialg.idr)
  — algebras, coalgebras, and dialgebras of slice-polynomial
  functors. `SPAlg`, `SPCoalg`, and `SPDialg` bundle a carrier
  slice object with the respective structure map; `SPAlgMap` and
  `SPDialgComm` provide morphisms and commutativity conditions for
  each. Algebras and coalgebras of an endofunctor are standard
  (nLab, algebra for an endofunctor; Barr–Wells op. cit. §3);
  dialgebras are described in Hagino, *A Categorical Programming
  Language* (1987) and on nLab.

- [`src/LanguageDef/SlicePolyDifunc.idr`](../../src/LanguageDef/SlicePolyDifunc.idr)
  — the difunctorial and closure structure of slice-polynomial
  functors on `Poly`. The module develops the locally Cartesian
  closed structure of `Poly`: `pfGenClosureObjPos` and
  `pfGenClosureObjDir` define the internal-hom object in `Poly`
  via a generalized closure construction; later sections handle
  the composition of `Poly`-slice functors (pullback, Pi,
  dependent sum) and the simplified formula for
  polynomial-functor composition `Poly → Poly`. Local Cartesian
  closure of `Poly` and composition of polynomial functors are
  described in Spivak–Niu (op. cit., §§3–4) and Gambino–Kock
  (op. cit.).

## Alternative formulations

The area contains two parallel presentations of natural
transformations between polynomial functors: the flat
`PolyNatTrans` of `PolyCat.idr` (a dependent pair of on-positions
and on-directions functions over `Type`) and the record `SPFnt`
of `SlicePolyCat.idr` (a `Pi` over the codomain type of pointwise
position and direction maps, for the general slice-polynomial
setting). Both encode the same underlying concept of polynomial
natural transformation; `SPFnt` specializes to `PolyNatTrans`
when `dom = cod = Unit`. Similarly, `DisliceCat.idr` provides
both a categorial-style (`CDisliceObj`/`CDisliceMorph`) and an
arena-style (`ADisliceObj`/`ADisliceMorph`) presentation of the
dislice category; the two are parallel encodings of the same
structure.

## Dependencies

This area builds on the
[Library](library.md) area (`IdrisUtils`, `IdrisCategories`,
`IdrisAlgebra`) for the slice-category vocabulary, profunctors,
W-types, and F-algebras it uses throughout.

## Pointers

- [`docs/mldirichf-generalization.md`](../mldirichf-generalization.md)
  — design notes for extending the `MLDirichF` PRA-functor
  construction from single walking-arrow copresheaves to arbitrary
  finite two-level DAGs; relevant to `GenPolyFunc.idr`.
- The Idris formalization in this area is the predecessor of the
  Lean 4 continuation. The Lean work on profunctors and parametric
  right adjoints is discussed in
  [`geb-lean/docs/areas/category-judgments.md`](../../../geb-lean/docs/areas/category-judgments.md).
  A dedicated Lean area doc for polynomial functors does not yet
  exist; this Idris area is the primary reference for that
  material.
- This codebase is not under active development; the Lean 4 port
  in `geb-lean/` is the continuation.
