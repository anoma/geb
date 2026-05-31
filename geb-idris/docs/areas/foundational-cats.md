# Foundational and finite-category machinery

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

This area provides the directed-graph and categorical foundations on
which the rest of `LanguageDef` builds: quiver types at multiple
enrichment levels, finite categories (including an S-expression
representation and a two-level-forest index category), parametric
right adjoint (PRA) structure, adjunction combinators over diagram
categories, universal-category templates, span and cospan categories,
and a collection of named small categories (helix, rope, nat-prefix,
and the multi-level quiver trio). Together these modules establish
the vocabulary of objects, morphisms, and categorical structure that
the higher Geb layers compose.

## Mathematical context

A quiver (directed multigraph) is the data underlying a category
before the identity and composition laws are imposed; the free
category on a quiver is the category of paths. Enriched quivers and
reflexive/compositional extensions stratify that idea over different
base categories (`Type`, `FinSet`) and serve as the ambient raw
material for presheaves and profunctors over quivers. Finite
categories are small categories whose hom-sets are finite; the
two-level-forest index category `F2FObj`/`F2FMor` in `FinCatPRA` is a
skeletal index for certain copresheaf data. Parametric right adjoints
(PRAs), introduced by Weber (*Generic morphisms, parametric
representability and weakly cartesian monads*, TAC 13, 2004), are
right adjoints that additionally preserve certain pullbacks; they
arise in the study of polynomial functors and polynomial monads.
Adjunctions, spans, and cospans are standard textbook constructions
(Mac Lane, *Categories for the Working Mathematician*; nLab). Spans
are diagrams `A ← C → B` whose colimits are pushouts; cospans `A → C
← B` whose limits are pullbacks. The helix and rope categories are
project-specific named small categories parameterized by
polynomial-functor data. The nat-prefix category treats bounded
natural numbers as objects and polynomial-circuit operations as
morphisms. The `MLQuiv*` trio organizes quiver-internal categories,
their universal properties (initial/terminal/coproduct quivers, Kan
extensions), and polynomial-functor structure on quivers into a
three-module cluster.

## Modules

- [`src/LanguageDef/Quiver.idr`](../../src/LanguageDef/Quiver.idr)
  — enriched quiver types at four enrichment levels: `QuivVE`
  (enriched, internal to an arbitrary base category), `EnrQuivVE`
  (enriched, internal to `Type`), `TypeQuivV` (internal to and
  enriched over `Type`), and `FinEnrQuivV`/`FinQuivN`
  (`FinSet`-enriched and `FinSet`-internal). Reflexive quivers
  (`TypeRQuivSL`) and compositional quivers (`TypeCQuivComp`) add
  self-loops and composition assignments; `ProquivVE` and `DiquivVE`
  provide the collage-shaped proquiver and its symmetric variant.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — directed multigraphs and their enriched generalizations
  are standard (Mac Lane, op. cit.; nLab,
  [quiver](https://ncatlab.org/nlab/show/quiver)); the `FinSet`-enriched
  variants are straightforward specializations. Searched 2026-05-31,
  scope Idris2 standard library, nLab, general knowledge.

- [`src/LanguageDef/FinCat.idr`](../../src/LanguageDef/FinCat.idr)
  — the `FinSet`-as-interface layer: `FinSetObjF` (the object-shape
  functor with constructors `FSO0`, `FSO1`, `FSOC` for initial,
  terminal, and binary coproduct) and `FinSetTermF` (the morphism-shape
  functor). Both are packaged as `FreeMonad`/`Mu`/`Nu` types via the
  `IdrisCategories` algebra machinery, supplying the building blocks
  for objects and terms of `FinSet`. Provenance: category 2 (known
  concept, formalized in this Idris codebase) — finite sets and
  their categorical presentation are standard (nLab,
  [FinSet](https://ncatlab.org/nlab/show/FinSet)); the algebraic
  packaging via initial algebras follows `IdrisCategories`. Searched
  2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/FinCatPRA.idr`](../../src/LanguageDef/FinCatPRA.idr)
  — S-expression representation of finite sets (`FinSetAtom`,
  `FinSetSExpr`, `FinSetSExprValid` with a decidability proof) and a
  two-level-forest index category (`Fin2Forest`, `F2FObj`, `F2FMor`
  with constructors `IdMor` and `DepToBase`). `WalkingArrow` is a
  distinguished instance showing the single-arrow category as a
  `[1]`-forest. The `PRA` in the name refers to the parametric right
  adjoint structure the forest category is designed to index.
  Provenance: category 2 (known concepts, formalized in this Idris
  codebase) — the walking-arrow and forest index categories are
  standard sketches; PRA structure follows Weber (2004, op. cit.);
  the S-expression representation is a project-specific encoding
  whose decidable validity checker appears novel. Searched 2026-05-31,
  scope nLab, Weber (2004).

- [`src/LanguageDef/Adjunctions.idr`](../../src/LanguageDef/Adjunctions.idr)
  — adjunction combinators over diagram categories: `AdjObjF` (a
  functor choosing an object from a `Diagram`), `LAUnitP`/`LAUApplyHom`
  (left-adjoint unit data with `LAUHv`/`LAUHc` constructors
  injecting vertices and adjoint-object morphisms), and
  `RACounitP`/`RACApplyHom` (the dual right-adjoint counit data).
  Several holes remain (`?ObjApplyRel_rel_hole`,
  `?lauApply_hole`), marking this module as a partial
  sketch. Provenance: category 2 (known concepts, partially formalized
  in this Idris codebase) — units and counits of adjunctions are
  standard (Mac Lane, op. cit., IV.1); this particular diagram-adjunction
  encoding is project-specific and unverified. Searched 2026-05-31,
  scope nLab, general knowledge.

- [`src/LanguageDef/UniversalCategory.idr`](../../src/LanguageDef/UniversalCategory.idr)
  — universal-category templates via algebraic signatures: `MagmaF`
  (binary-combination functor), `MonoidF` (free-monoid functor with
  law-rewriting constructors `MCancelIdL`/`MCancelIdR`/`MShiftR`), and
  polynomial-algebra helpers (`powerToListAlg`, `polyToPowerAlg`).
  The module also contains a long design commentary explaining how Geb
  constructs categories by axiomatizing universal properties rather
  than defining structures and proving they satisfy laws.
  Provenance: category 2 (known concepts, formalized in this Idris
  codebase) — magmas, monoids, and polynomial algebras are standard
  algebraic structures; the Geb-specific categorical-inversion
  philosophy described in the commentary is novel context. Searched
  2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/DiagramCat.idr`](../../src/LanguageDef/DiagramCat.idr)
  — a category-sort index (`CatSortObj` with constructors `CSOobj`,
  `CSOmorph`, `CSOcomp`, plus products and terminal) and its morphisms
  (`CatSortMorph` with `CSMdom`, `CSMcod`, `CSMcomp`, projections),
  plus variably-parameterized type families (`VPTSig`, `VPTEFunc`,
  `VPTFunc`). The composition `csmComp` and equality `csmEq` have
  open holes, marking this as a partial development.
  Provenance: category 2 (known concept, partially formalized) — the
  sort-index for a category presentation is an instance of the
  essentially-algebraic theory of categories (Adámek–Rosický,
  *Locally Presentable and Accessible Categories*, 1994); this
  specific dependent-type encoding is project-specific.
  Searched 2026-05-31, scope nLab, Adámek–Rosický.

- [`src/LanguageDef/SpanCospan.idr`](../../src/LanguageDef/SpanCospan.idr)
  — spans (`SpanObj` with fields `spCodL`, `spCodR`, `spDom`) and
  cospans (`CospanObj` with fields `cospCod`, `cospDomL`, `cospDomR`)
  in dependent-type style, with their morphisms (`SpanMorph`,
  `CospanMorph`), identities (`spanId`, `cospanId`), and composition.
  Spans and cospans are represented as fibrations rather than as
  explicit diagram functors, making commutativity conditions
  automatic from the dependent typing.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — spans and cospans are standard category theory (nLab,
  [span](https://ncatlab.org/nlab/show/span)); the dependent-type
  fibration encoding is a standard Idris/Agda idiom. Searched
  2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/HelixCat.idr`](../../src/LanguageDef/HelixCat.idr)
  — the helix category: `HelixObj` (a four-component record
  `hCodirich`/`hCopoly`/`hPoly`/`hDirich`) and `HelixMor` (a
  seven-field morphism record tracing a chain across the four
  components), with `hmId`, `hmComp`, and accessor combinators
  `hmDomCoasn`/`hmCodPolyArr`/`hmDomDirichArr`. The helix object
  represents a twisted-arrow morphism from a `Copoly → Poly` arrow to
  a `Codirich → Dirich` arrow, parameterized over the connecting
  morphisms. Provenance: category 1 (novel, unverified) — the
  helix-object shape is not a standard named construction; it appears
  to be a project-specific structure organizing polynomial and
  Dirichlet data. Searched 2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/RopeCat.idr`](../../src/LanguageDef/RopeCat.idr)
  — the rope category: `MLRope` (a `mlrPos : Type` with a
  `mlrDir : mlrPos -> HelixObj` direction map) and `InterpMLR` (a
  pairing of a position `imlrPos` with a `HelixMor` assignment
  `imlrDirAsn`), together with projection accessors
  (`imlrDirich`, `imlrPoly`, `imlrCodirich`, `imlrCopoly`) and
  the functor action `InterpMLRmap`. Ropes are polynomial-functor-style
  tetrafunctors on helix objects.
  Provenance: category 1 (novel, unverified) — the rope/tetrafunctor
  construction is project-specific; it is not a standard named
  category-theoretic structure. Searched 2026-05-31, scope nLab,
  general knowledge.

- [`src/LanguageDef/NatPrefixCat.idr`](../../src/LanguageDef/NatPrefixCat.idr)
  — natural numbers as bounded-set objects, in two representations:
  unary (`BUNat n = Either Unit (BUNat (n-1))`) and arithmetic
  (`BANat n`, a refinement of `Nat` with an upper-bound proof), with
  translations `u2a`/`a2u` and round-trip correctness
  `u2a2u_correct`/`a2u2a_correct`. The bounded-natural-number category
  (`BNCatObj = Nat`, `VBNCLM`, `bncLMA`) interprets each natural number
  as a finite set and list-encoded functions as morphisms.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — bounded natural numbers as finite sets and their
  polynomial-circuit morphisms are standard combinatorial category
  theory (nLab, [FinSet](https://ncatlab.org/nlab/show/FinSet));
  the dual unary/arithmetic representation is a project-specific
  convenience. Searched 2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/MLQuivCat.idr`](../../src/LanguageDef/MLQuivCat.idr)
  — quivers organized as a category: `TQuivObj` (a vertex type `tqV`
  paired with a `TypeQuivV tqV` edge type) and `TQuivMorph` (vertex
  map `tqmV` and edge map `tqmE`) with `tqId`/`tqComp`, plus
  presheaves (`TQPresheaf`) and copresheaves (`TQCopresheaf`) on
  quivers and their morphism-map components
  (`TypeQuivPreshfMmap`, `TypeQuivCopreshfMmap`).
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — the category of quivers and quiver morphisms, and
  (co)presheaves on quivers, are standard (nLab,
  [quiver](https://ncatlab.org/nlab/show/quiver)). Searched 2026-05-31,
  scope nLab, general knowledge.

- [`src/LanguageDef/MLQuivUniv.idr`](../../src/LanguageDef/MLQuivUniv.idr)
  — universal properties of quivers: initial (`TypeQuivInit`),
  terminal (`TypeQuivTerm`), and coproduct (`TypeQuivCoprodV`)
  quivers with their self-loop and composition witnesses, plus ends
  and coends expressed as `TypeQuivRKanExt`/`TypeQuivLKanExtBase`
  (right and left Kan extensions of copresheaves along the constant
  functor). The Kan-extension profunctor `TypeQuivKanExtProf` is
  shared by both directions because extending along the constant
  functor makes `1 × P` and `P ^ 1` isomorphic to `P`.
  Provenance: category 2 (known concept, formalized in this Idris
  codebase) — initial/terminal/coproduct objects and Kan extensions
  are standard (Mac Lane, op. cit.; nLab,
  [Kan extension](https://ncatlab.org/nlab/show/Kan+extension)).
  Searched 2026-05-31, scope nLab, general knowledge.

- [`src/LanguageDef/MLQuivPoly.idr`](../../src/LanguageDef/MLQuivPoly.idr)
  — quivers internal to the polynomial-functor category: `PolyQuiv`
  (a `pqPos : PolyFunc` with a direction algebra `pqDir : PFAlg pqPos
  PolyFunc`). This stub is the point of entry for polynomial functors
  on quivers; at 28 lines it records the definition without further
  development.
  Provenance: category 1 (novel, unverified) — quivers internal to
  the polynomial-functor category are not a standard named
  construction; the combination is project-specific. Searched
  2026-05-31, scope nLab, general knowledge.

## Alternative formulations

None within this area. The `FinSetObjF`-based finite-set representation
in `FinCat` and the S-expression representation in `FinCatPRA` both
encode finite sets, but they serve different purposes (`FinCat` provides
the algebraic interface layer; `FinCatPRA` provides the S-expression
check for the PRA machinery) and are not competing formulations of the
same construction.

## Dependencies

- [`docs/areas/library.md`](library.md) — all modules here
  import from `Library.IdrisUtils` and `Library.IdrisCategories`.
  `HelixCat`, `SpanCospan`, and `RopeCat` additionally import
  `Library.IdrisAlgebra`.

## Pointers

The Idris codebase is the predecessor implementation; active
development has moved to Lean 4 under `geb-lean`. Readers looking
for the actively maintained formulations should consult the Lean
areas:

- For quiver-based category presentations and the associated
  adjunction, see
  `geb-lean/docs/areas/category-judgments.md`.
- Several modules in this area (`Adjunctions`, `DiagramCat`,
  `MLQuivPoly`) contain open holes (`?`-named metavariables) and
  should be read as partial sketches rather than completed
  formalizations.
