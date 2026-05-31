# Internal categories and profunctors

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

This area defines the internal-category infrastructure that underlies Geb's
treatment of polynomial and Dirichlet functors: categories internal to
Idris's metalanguage `Type`, profunctors and difunctors between them,
the family and cofamily fibrations (free coproduct/product completions),
and the dinaturality / (co)end machinery that characterizes natural
transformations between arena-based functors.

## Mathematical context

An *internal category* in a category `E` is a diagram
`C₁ ⇉ C₀` in `E` equipped with identity and composition maps
satisfying the usual category axioms; when `E = Set` (here, Idris
`Type`) the result is an ordinary small category presented by explicit
data. The foundational reference is Johnstone,
*Sketches of an Elephant*, vol. I, or Borceux,
*Handbook of Categorical Algebra*, vol. 1.

A *profunctor* `P : C ↛ D` is a functor `Cᵒᵖ × D → Set`; profunctors
compose via coends and form the bicategory **Prof**. The (co)end
calculus is developed in Loregian, *Coend Calculus* (Cambridge
University Press, 2021). Internally, a profunctor between internal
categories is a set `P c d` with contravariant action on `c` and
covariant action on `d`.

A *Dirichlet functor* is a sum of contravariant representables —
equivalently a functor `E → Set` in the free coproduct completion
`Fam(C)` — and plays the role dual to polynomial functors (sums of
covariant representables). The families/cofamilies hierarchy is
analyzed in Spivak, *Polynomial Functors: A General Theory of
Interaction* (2022). The twisted-arrow category `Tw(C)` of a category
`C` has morphisms of `C` as objects and commutative squares as
morphisms; copresheaves on `Tw(C)` are the natural home for
paranatural transformations, as analyzed in
[`docs/twisted-arrow-copresheaf-analysis.md`](../twisted-arrow-copresheaf-analysis.md).

The *dipolynomial* / *difunctor* modules treat endoprofunctors
presented as polynomial arenas, connecting to the characterization
of ends developed in
[`docs/profunctor-end-characterization.md`](../profunctor-end-characterization.md).

## Modules

- [`src/LanguageDef/InternalCat.idr`](../../src/LanguageDef/InternalCat.idr)
  — foundational signatures for internal categories in Idris `Type`.
  `IntMorSig`, `IntIdSig`, `IntCompSig` are the raw signatures;
  `IntCatSig` bundles them; `IntCatEqSig`, `Isomorphism`, and
  `MorCongF` add a morphism-equality structure and congruence algebra.
  Provenance: cat 2 (known maths, unverified first formalization in
  any proof assistant) — internal categories in `Set`, Johnstone
  *Sketches of an Elephant* vol. I; searched 2026-05-31, scope nLab,
  Agda/Idris2 standard libraries.

- [`src/LanguageDef/InternalHigherCat.idr`](../../src/LanguageDef/InternalHigherCat.idr)
  — re-export aggregator lifting `InternalCat`, `SlicePolyCat`, and
  `IntDepFamCat` into a single higher-category import point; no
  independent declarations.
  Provenance: cat 2 (known maths) — structural convenience module;
  searched 2026-05-31.

- [`src/LanguageDef/InternalProfunctor.idr`](../../src/LanguageDef/InternalProfunctor.idr)
  — internal profunctors and difunctors between internal categories.
  `IntProfunctorSig d c` is a two-sided family; `IntDimapSig`,
  `IntLmapSig`, `IntRmapSig` encode the contravariant and covariant
  action laws; `IntLRmapsCommute` and the composition laws close the
  profunctor axioms. Also contains identity laws for `TypeMor`
  (`typeIdL`, `typeIdR`, `typeAssoc`).
  Provenance: cat 2 (known maths, unverified first internal-profunctor
  formalization in Idris2) — profunctors, Loregian *Coend Calculus*
  §1; searched 2026-05-31, scope nLab, Agda stdlib.

- [`src/LanguageDef/Diprofunctor.idr`](../../src/LanguageDef/Diprofunctor.idr)
  — the category of polynomial diprofunctors: objects as arenas
  `DiProAr = (pos : Type ** pos -> (Type, Type))` with both a
  contravariant and covariant direction per position.
  `InterpDPR`, `InterpDPRtw` give the interpretations; `DiProArMonId`
  and `DiProArMonComp'` assemble a monoidal structure; the
  `InterpDPRtwMap` lifts dipolynomial interpretation through
  twisted-arrow presheaves.
  Provenance: cat 1 (novel, unverified) — polynomial diprofunctors
  as a distinct arena category; searched 2026-05-31, scope nLab,
  Spivak polynomial-functor literature.

- [`src/LanguageDef/IntArena.idr`](../../src/LanguageDef/IntArena.idr)
  — arenas on internal categories: `IntArena c = CSliceObj c`, a
  slice object over the object-of-objects. Introduces `IA`, `iaIdx`,
  `iaObj`, and specializations `MLArena`; documents the four
  family/cofamily categories built from arenas.
  Provenance: cat 2 (known maths, unverified first Idris2
  formalization) — arena = slice object, Spivak *Polynomial Functors*
  §2; searched 2026-05-31, scope Agda polynomial-functor libraries.

The following eight modules define the four family and cofamily
categories (universal families = free cartesian monoidal completion;
existential families = free coproduct completion / Dirichlet functors;
their cofamily duals). Objects of all four categories share the arena
type; the categories differ only in their morphism definitions.

- [`src/LanguageDef/IntUFamCat.idr`](../../src/LanguageDef/IntUFamCat.idr)
  — universal families (free cartesian monoidal category).
  `IntUFamMor` has index map contravariant and object map covariant,
  making this the opposite of the polynomial-functor category; note
  in the source `IntUFamIsOpEFam`-style duality comments.
  Provenance: cat 2 (known maths) — `Fam_∀(C)`, nLab multi-adjoint
  §2.5; searched 2026-05-31.

- [`src/LanguageDef/IntEFamCat.idr`](../../src/LanguageDef/IntEFamCat.idr)
  — existential families (free coproduct completion, Dirichlet
  functors). `IntEFamMor` is covariant on both index and object;
  the source notes the equivalence with Dirichlet functor morphisms.
  Provenance: cat 2 (known maths) — `Fam_∃(C)`, Spivak
  *Polynomial Functors* §3; searched 2026-05-31.

- [`src/LanguageDef/IntUCofamCat.idr`](../../src/LanguageDef/IntUCofamCat.idr)
  — universal cofamilies (families of objects from `Cᵒᵖ` with
  universal morphisms). `IntUCofamMor` contracts index
  covariantly; `IntUCofamIsOpEFam` states this category is the
  opposite of `IntEFamCat`.
  Provenance: cat 2 (known maths) — opposite of existential
  families; searched 2026-05-31.

- [`src/LanguageDef/IntECofamCat.idr`](../../src/LanguageDef/IntECofamCat.idr)
  — existential cofamilies (polynomial functors). `IntECofamMor`
  maps positions covariantly and lifts morphisms contravariantly in
  the base category, giving the standard polynomial-functor
  morphisms.
  Provenance: cat 2 (known maths) — polynomial functors,
  Spivak *Polynomial Functors* §2; searched 2026-05-31.

- [`src/LanguageDef/IntDepFamCat.idr`](../../src/LanguageDef/IntDepFamCat.idr)
  — dependent families over internal categories: a joint import of
  all four family/cofamily modules, plus predicates `IDFsigma` and
  `IDFpi` expressing sigma-type and pi-type slices over a family
  object. Serves as the consolidated import point for the family
  hierarchy.
  Provenance: cat 2 (known maths) — dependent families as sigma/pi
  fibrations; searched 2026-05-31.

- [`src/LanguageDef/IntFactCat.idr`](../../src/LanguageDef/IntFactCat.idr)
  — factorization categories: imports all four family/cofamily
  modules to provide a uniform factorization-system context; no
  independent declarations beyond the aggregated imports.
  Provenance: cat 2 (known maths, unverified) — factorization
  systems on family/cofamily categories; searched 2026-05-31.

- [`src/LanguageDef/IntFactCatFunc.idr`](../../src/LanguageDef/IntFactCatFunc.idr)
  — functors on factorization categories: extends `IntFactCat` with
  the factorization-functor layer; no independent declarations beyond
  the import chain.
  Provenance: cat 2 (known maths, unverified); searched 2026-05-31.

- [`src/LanguageDef/IntParamCat.idr`](../../src/LanguageDef/IntParamCat.idr)
  — parameterized bundles: `PBundleObj x = x -> IntEFamObj TypeObj`
  packages a family of existential families indexed by `x`;
  `PBundleMor` gives the morphism type as an iterated existential
  family morphism. Supports parameterized adjunctions and
  bundle-level constructions.
  Provenance: cat 1 (novel, unverified) — parameterized-bundle
  objects as iterated existential families; searched 2026-05-31,
  scope nLab, Spivak literature.

- [`src/LanguageDef/IntTwistedArrowCat.idr`](../../src/LanguageDef/IntTwistedArrowCat.idr)
  — polynomial functors indexed by twisted-arrow categories.
  `PolyTwistF` is a five-component arena encoding a polynomial
  functor whose directions split into contravariant and covariant
  parts per position; `InterpPTw` interprets it as a
  `TwArrCoprSig`-valued functor.
  Provenance: cat 1 (novel, unverified) — polynomial structure on
  the twisted-arrow category; the twisted-arrow category itself is
  standard (nLab); the arena-style polynomial encoding is Geb-specific;
  searched 2026-05-31.

- [`src/LanguageDef/IntDisheafCat.idr`](../../src/LanguageDef/IntDisheafCat.idr)
  — sheaf-like constructions on polynomial categories. Defines
  `PolyPolyCat`, `PolyUnivCat`, `DirichDirichCat`, `PolyUnivCat`
  as iterated family/cofamily categories; proves a polynomial
  double-Yoneda lemma via `PolyDoubleYo` and `PolyAppFunc`.
  Provenance: cat 1 (novel, unverified) — double-Yoneda for the
  polynomial double category; searched 2026-05-31, scope Spivak
  polynomial-functor literature, nLab.

- [`src/LanguageDef/MLDirichCat.idr`](../../src/LanguageDef/MLDirichCat.idr)
  — Dirichlet functors in Idris's metalanguage. `MLDirichCatObj` is
  a dependent pair `(pos : Type ** pos -> Type)`; `MLDirichCatMor`
  is a covariant-on-both natural transformation; `InterpDirichFunc`
  gives the contravariant set-valued interpretation `(i : pos **
  x -> dir i)`.
  Provenance: cat 2 (known maths, unverified first Idris2
  formalization) — Dirichlet functors, Spivak *Polynomial
  Functors* §3; searched 2026-05-31.

- [`src/LanguageDef/MLBundleCat.idr`](../../src/LanguageDef/MLBundleCat.idr)
  — covariant fiber bundles over `Type`. `ABundleObj` is an
  existential family over `Type`; `CBundleObj` is the record form
  with base, total space, and projection; `CBOtoIBO` converts to
  the abstract internal-bundle form. Supplies the base for
  bundle-style twisted-pair constructions.
  Provenance: cat 2 (known maths, unverified) — fiber bundles as
  slice categories, standard categorical topology; searched 2026-05-31.

- [`src/LanguageDef/MLTwistPair.idr`](../../src/LanguageDef/MLTwistPair.idr)
  — the twisted-pair category, a dependent-pair reformulation of
  the twisted-arrow category. `TwistPairObj = IntArena TypeObj`;
  `TwistPairMor` and the equivalences `TwistPairToArr` /
  `TwistArrToPair` relate it to the standard `TwArrObj`
  presentation; `MLTwPobj` is the record form.
  Provenance: cat 1 (novel, unverified) — the dependent-pair
  ("twisted-pair") formulation of the twisted-arrow category;
  searched 2026-05-31, scope nLab twisted-arrow literature.

- [`src/LanguageDef/SlPolyIntCat.idr`](../../src/LanguageDef/SlPolyIntCat.idr)
  — embedding of internal categories into dependent polynomial
  functors via generalized elements. `IntGenEl`, `IntGenQuant`,
  `IntCodChangeF`, `IntDomChangeF` encode the Yoneda-embedding
  data; `CommutingCodChangeF` states the naturality condition;
  `TypeMorFromCodChangeF` recovers a metalanguage function from
  a commuting codomain-change.
  Provenance: cat 2 (known maths, unverified) — Yoneda lemma for
  internal categories, Johnstone *Sketches of an Elephant* vol. I;
  searched 2026-05-31.

- [`src/LanguageDef/DiPolyFunc.idr`](../../src/LanguageDef/DiPolyFunc.idr)
  — dipolynomial functors: coproducts of direpresentables over
  `opProd(c)`. `PolyDiSig c = IntEndoProAr`, with `InterpPolyDi`
  the difunctor interpretation; `InterpPolyLmap` and the
  corresponding right-map give the dinatural action. The source
  notes the analogy with polynomial vs. Dirichlet: same arenas,
  different morphisms.
  Provenance: cat 1 (novel, unverified) — dipolynomial functors as
  a distinct arena-based difunctor category; searched 2026-05-31,
  scope Spivak, Loregian.

- [`src/LanguageDef/MLDiPolyFunc.idr`](../../src/LanguageDef/MLDiPolyFunc.idr)
  — metalanguage specialization of `DiPolyFunc` to `c = Type`.
  `MLPolyDiSig`, `InterpMLPolyDi`, `MLPDiagObj`, and `mlpdeEl` are
  the specializations; delegates all proofs to `DiPolyFunc`.
  Provenance: cat 1 (novel, unverified) — same as `DiPolyFunc`;
  searched 2026-05-31.

- [`src/LanguageDef/PolyDifunc.idr`](../../src/LanguageDef/PolyDifunc.idr)
  — parametric right adjoint (PRA) endofunctors on polynomial
  functors. `PolyEndoPRA` packages the PRA data; `InterpPolyEndoPRA`
  and `InterpPolyEndoPRAmap` give the functor and naturality;
  `MLPolyF1` and `InterpMLPolyF1` are the metalanguage
  specialization.
  Provenance: cat 2 (known maths, unverified first Idris2
  formalization) — PRA functors, Weber *Familial 2-functors and
  parametric right adjoints* (2007); searched 2026-05-31, scope
  nLab PRA, Agda libraries.

- [`src/LanguageDef/PolyProfunctor.idr`](../../src/LanguageDef/PolyProfunctor.idr)
  — polynomial profunctors as profunctors on dependent-pair
  categories. `SigSliceObj`, `DProdSlice`, `DProdSPF` encode the
  domain data; `SubstObjMuPosPos` / `SubstObjMuPosDir` develop a
  worked example of the polynomial-profunctor representation for
  the substitution-object morphism signature.
  Provenance: cat 1 (novel, unverified) — polynomial profunctors
  and their arena representations; searched 2026-05-31, scope nLab,
  Spivak, Loregian.

- [`src/LanguageDef/PolyProfEnd.idr`](../../src/LanguageDef/PolyProfEnd.idr)
  — sections of polynomial functors as ends. `PolySection pf` is
  a choice of direction per position; `sectionApply` applies a
  section as a natural transformation `pf → Id`; `natTransToSection`
  inverts this; `sectionRoundTrip` and `natTransRoundTrip` (requiring
  `PolyNatTransNaturality`) prove the bijection, establishing
  `Nat(pf, Id) ≅ PolySection pf` — the end characterization for
  the identity profunctor.
  Provenance: cat 2 (known maths, unverified first Idris2
  formalization) — end as sections, Loregian *Coend Calculus* §1.2;
  see also [`docs/profunctor-end-characterization.md`](../profunctor-end-characterization.md);
  searched 2026-05-31, scope nLab, Agda coend libraries.

## Alternative formulations

There is no single concept with multiple parallel formulations here in the
sense of the template. However, note that the same arena data
`(pos : Type ** pos -> Type)` appears in four distinct roles:
`IntUFamObj` (universal families, morphisms contravariant on index),
`IntEFamObj` (existential families / Dirichlet functors, covariant),
`IntUCofamObj` (universal cofamilies, the opposite of `IntEFamCat`),
and `IntECofamObj` (existential cofamilies / polynomial functors,
morphisms covariant on index, contravariant on object). This
multi-role reuse of arena objects is not a search for a preferred
form but a deliberate exploration of the four quadrants of the
families/cofamilies cube; see `IntArena.idr` inline documentation for
the orienting description.

## Dependencies

This area is foundational; it imports only the base utility and
algebra libraries (`Library.IdrisUtils`, `Library.IdrisCategories`,
`Library.IdrisAlgebra`) and the QType module. The polynomial and
Dirichlet modules in this area import the internal-category core and
build on it. The area provides the infrastructure that the
polynomial-functors area and the slice-polynomial area consume.

## Pointers

- [`docs/profunctor-end-characterization.md`](../profunctor-end-characterization.md)
  — mathematical characterization of ends of polynomial profunctors;
  companion to `PolyProfEnd.idr`.
- [`docs/twisted-arrow-copresheaf-analysis.md`](../twisted-arrow-copresheaf-analysis.md)
  — analysis of paranatural transformations as copresheaves on
  twisted-arrow categories; companion to `IntTwistedArrowCat.idr`
  and `MLTwistPair.idr`.
- This Idris codebase is a predecessor to the Lean formalization in
  `geb-lean/`; profunctors have been partially redone in Lean under
  `GebLean/Utilities/Profunctors.lean`. The Lean versions are the
  current development focus; the Idris modules are largely
  superseded but remain the source record of the initial
  exploration.
