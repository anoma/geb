# Category judgments and the `L ⊣ Φ` adjunction

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

This area presents the data of a category — objects, morphisms,
identity assignments, composition assignments — as a copresheaf on a
finite index category, and constructs the reflective adjunction
`L ⊣ Φ` between `Cat` and that copresheaf category. It supplies Geb
with a judgment-style, type-theoretic presentation of categories that
sits adjacent to mathlib's typeclass-based `Category`.

## Mathematical context

A category can be specified by four sorts (objects, morphisms,
identity judgments, composition judgments) together with projection
maps (domain, codomain, identity-of, the three legs and three objects
of a composition triple) subject to typing constraints. Packaging
those sorts and maps as a covariant functor from a fixed finite index
category `J` to `Type` exhibits category-presentations as copresheaves
on `J`; `J` is a projective sketch whose `Set`-models are exactly such
presentations (Johnstone, *Sketches of an Elephant*, vol. II;
Adámek–Rosický, *Locally Presentable and Accessible Categories*, on
`Cat` as essentially algebraic). A copresheaf is thus a *relational,
proof-relevant specification* of a category: the composition and
identity data are recorded as relations, not yet required to be total,
single-valued, or lawful. The reflection `L` turns such a
specification into an actual category by completing the relation to
make it total, quotienting it to make it functional, and closing it
under identity, composition, and associativity so that the category
laws hold. The embedding `Φ` extracts the canonical specification of a
category, and the counit `L(Φ C) → C` is an isomorphism, so `Φ` is
fully faithful and `Cat` is reflective in the copresheaf category.
This is structurally parallel to the
nerve–realization adjunction `τ₁ ⊣ N : Cat ⇆ [Δᵒᵖ, Set]`, differing
in that the index category here is finite and the diagrams are
covariant. The novelty analysis of the construction is recorded in
[`docs/research/novelty-analysis.md`](../research/novelty-analysis.md).

## Modules

- [`GebLean/CategoryJudgments.lean`](../../GebLean/CategoryJudgments.lean)
  — the finite index category `J` and copresheaf data on it.
  `Obj` is the four-object type (`obj`, `mor`, `id`, `comp`) and
  `SemiHom`/`Hom` its generating morphisms, assembled into a
  `FinCategory Obj` instance; `FunctorData` packages a copresheaf as
  explicit sorts and projection maps, with `functorDataEquivCat`
  relating it to honest functors `Obj ⥤ C`.
  Provenance: novel mathematics — nearest antecedents are walking
  structures and the essentially-algebraic presentation of `Cat`
  (Johnstone, *Sketches of an Elephant* II; Adámek–Rosický 1994); no
  prior formalization of this finite-index copresheaf encoding found.
  Searched 2026-05-31, scope Mathlib (leansearch), nLab, the cited
  literature.
- [`GebLean/DepCategoryJudgments.lean`](../../GebLean/DepCategoryJudgments.lean)
  — the dependently-typed presentation and its equivalence with the
  copresheaf presentation. `DepCategoryData` carries `objT`, `morT`,
  `idT`, `compT` as dependent sorts; `depCatToCopresheaf` /
  `copresheafToDepCat` and `depCatCopresheafEquiv` establish the
  equivalence with `CopresheafData` (copresheaves on `J`).
  Provenance: novel mathematics — the dependent/copresheaf
  correspondence specific to this `J`; nearest antecedent is the
  general models-of-a-sketch reading. Searched 2026-05-31, scope
  Mathlib (leansearch), nLab.
- [`GebLean/CatJudgmentAdjunction.lean`](../../GebLean/CatJudgmentAdjunction.lean)
  — the `L ⊣ Φ` reflective adjunction in `Type`-valued copresheaf
  form, and its universal-property preservation analysis. `LFunctor`
  and `PhiFunctor` with `catCopresheafMathlibAdjunction`,
  `phiFunctorFullyFaithful`, and `phiFunctor_reflective` give the
  reflection; `phiFunctorPreservesCoproduct`,
  `phiFunctorPreservesInitial`, and `lToTerminalFunctor` record
  preservation results. The counit is an isomorphism
  (`catCopresheafCounitNatIso`).
  Provenance: novel mathematics — the finite-index reflective
  embedding of `Cat` into copresheaves; mathlib formalizes only the
  infinite-index nerve analogue
  (`CategoryTheory.instReflectiveSSetCatNerveFunctor`), confirming no
  prior Lean formalization of this construction. Searched 2026-05-31,
  scope Mathlib (leansearch/loogle), nLab.
- [`GebLean/DepCategoryAdjunction.lean`](../../GebLean/DepCategoryAdjunction.lean)
  — the reflective adjunction realized through the dependent
  presentation, built from layered reflective inclusions.
  `truncateWitnessesCounitIso` and `truncateUCLCounitIso` exhibit the
  per-property counits as isomorphisms (witness-subsingleton truncation
  and the existence/uniqueness/law layer), assembling the reflection of
  `Cat` inside `DepCategoryData`.
  Provenance: novel mathematics — the staged reflective-inclusion
  decomposition for this presentation; nearest antecedent is the
  general theory of reflective subcategories (mathlib
  `CategoryTheory.Reflective`). Searched 2026-05-31, scope Mathlib
  (loogle), nLab.
- [`GebLean/DepCategoryCat.lean`](../../GebLean/DepCategoryCat.lean)
  — the equivalence of `Cat` with the full subcategory of
  `DepCategoryData` cut out by the category-like conditions.
  `catToDepCategoryCatFunctor` is the embedding and
  `catDepCategoryCatEquiv` the equivalence; its full faithfulness is
  recorded via `catToDepCategoryCatFunctor.fullyFaithful`.
  Provenance: novel mathematics — the characterization of `Cat` as a
  full subcategory of this dependent presentation; nearest antecedent
  is `Cat` as models of an essentially algebraic theory
  (Adámek–Rosický 1994). Searched 2026-05-31, scope Mathlib
  (leansearch), nLab.
- [`GebLean/PLang/CatJudgment.lean`](../../GebLean/PLang/CatJudgment.lean)
  — the universe-polymorphic copresheaf presentation used by the PLang
  formulations. Sorts and projections are layered as sigma types
  (`ObjMorObj`, `ObjMorCopr`, up to the full category-judgment
  copresheaf object), giving four independent universe parameters for
  the four component sorts.
  Provenance: novel mathematics — universe-flexible repackaging of the
  `J`-copresheaf data; same antecedents as
  `CategoryJudgments.lean`. Searched 2026-05-31, scope Mathlib
  (leansearch), nLab.
- [`GebLean/PLang/CatJudgGrothendieck.lean`](../../GebLean/PLang/CatJudgGrothendieck.lean)
  — the layered Grothendieck-construction presentation of
  category-judgment copresheaves. `CompWitGr` is the three-layer total
  category (quiver, then identity witnesses, then composition
  witnesses) assembled from `Grothendieck`/`GrothendieckContra'` of
  the quiver, identity-witness, and composition-witness functors.
  Provenance: novel mathematics — Grothendieck-route presentation of
  this copresheaf data; nearest antecedent is the standard
  Grothendieck construction / category of elements (mathlib
  `CategoryTheory.Grothendieck`). Searched 2026-05-31, scope Mathlib
  (loogle), nLab.
- [`GebLean/PLang/CatJudgCoprAdjunction.lean`](../../GebLean/PLang/CatJudgCoprAdjunction.lean)
  — the `L ⊣ Φ` adjunction in the PLang copresheaf formulation.
  `LFunctorPLang` and `PhiFunctorPLang` are the functors;
  `counitNatTransPLang` and the `adjunctionAt` data assemble the
  pointwise reflection with the counit an isomorphism.
  Provenance: novel mathematics — PLang-form instance of the
  finite-index reflective embedding; same antecedents as
  `CatJudgmentAdjunction.lean`, no prior Lean formalization found.
  Searched 2026-05-31, scope Mathlib (leansearch/loogle), nLab.
- [`GebLean/PLang/CatJudgGrAdjunction.lean`](../../GebLean/PLang/CatJudgGrAdjunction.lean)
  — the `L ⊣ Φ` adjunction over the Grothendieck presentation
  `CompWitGr`. `PhiFunctor` and `LFunctor` between `Cat` and
  `CompWitGr` are packaged into `grAdjunction : L ⊣ Φ` with
  `phiReflective : Reflective Φ`; `phiFunctorFullyFaithful` records
  full faithfulness of the embedding.
  Provenance: novel mathematics — Grothendieck-route instance of the
  reflective embedding; same antecedents as
  `CatJudgmentAdjunction.lean`. Searched 2026-05-31, scope Mathlib
  (loogle), nLab.
- [`GebLean/PLang/CatJudgmentAdjunction.lean`](../../GebLean/PLang/CatJudgmentAdjunction.lean)
  — the embedding `Φ` for the PLang formulation at flexible universe
  levels, with its counit. `PhiFunctor_PLang : Cat ⥤ CatJudgCopr` is
  the embedding, `LFunctor_PLang` the reflection, and `counitNT` the
  counit natural transformation `Φ ⋙ L ⟶ 𝟭 Cat`.
  Provenance: novel mathematics — universe-flexible embedding for the
  PLang copresheaf form; same antecedents as
  `CatJudgmentAdjunction.lean`. Searched 2026-05-31, scope Mathlib
  (leansearch), nLab.
- [`GebLean/CatValuedFunctor.lean`](../../GebLean/CatValuedFunctor.lean)
  — the pointwise lift of `L ⊣ Φ` to functor categories.
  `phiWhiskering` post-composes with `PhiFunctor`;
  `catCopresheafFunctorAdjunction` is the lifted adjunction
  `(L ∘ −) ⊣ (Φ ∘ −) : [C, Cat] ⇄ [C, [J, Type]]` and
  `phiWhiskering_reflective` records that the lift is reflective, via
  full faithfulness of whiskering and pointwise lifting of adjunctions.
  Provenance: known maths, first Lean formalization — the lift uses
  mathlib's `Functor.FullyFaithful.whiskeringRight` and
  `Adjunction.whiskerRight`, applied to this novel `Φ`; the lifting
  principle itself is standard. Searched 2026-05-31, scope Mathlib
  (loogle).
- [`GebLean/PLang.lean`](../../GebLean/PLang.lean)
  — re-export aggregator for the `PLang/` modules; no declarations of
  its own.
- [`GebLean/Utilities/Category.lean`](../../GebLean/Utilities/Category.lean)
  — typeclass-free category, functor, and natural-transformation data
  used to state the adjunction without `eqToHom`/`heq` friction.
  `CategoryData` and `CategoryOfData` build a mathlib `Category` from
  bundled operations and laws, with `categoryDataOfCategory` the
  reverse extraction; parallel `FunctorData`/`FunctorOfData` handle
  functors.
  Provenance: known maths, first Lean formalization — an unbundled
  restatement of the standard category/functor axioms (mathlib
  `CategoryTheory.Category`, `Functor`). Searched 2026-05-31, scope
  Mathlib (leansearch/loogle).
- [`GebLean/Utilities/OverCategoryEquiv.lean`](../../GebLean/Utilities/OverCategoryEquiv.lean)
  — equivalences between the Over/Arrow-based and dependently-typed
  category structures of `Category.lean`. `CategoryData.toOverCategoryData`
  and `OverCategoryData.toCategoryData` convert between
  proof-irrelevant Over-based data and the dependent form, with
  matching functor-level and natural-transformation-level conversions.
  Provenance: known maths, first Lean formalization — bookkeeping
  equivalence between two presentations of the same standard data
  (mathlib `CategoryTheory.Comma.Over`). Searched 2026-05-31, scope
  Mathlib (leansearch).

## Alternative formulations

There is a single concept here: the reflective adjunction between
`Cat` and a presheaf category over a finite index category, where a
copresheaf is a relational, proof-relevant specification of a category
and the reflection produces the category obtained by completing the
relation to make it total, quotienting it to make it functional, and
closing it under identity, composition, and associativity so that the
category laws hold. The repository contains several formulations of
that one adjunction; the variations below are artifacts of searching
for a preferred specific formulation rather than distinct
constructions, and the curated `geb-mathlib` port may well settle on a
further variation. They differ along three axes.

- Presentation of the copresheaf data. The structural,
  `Type`-valued form in
  [`GebLean/CategoryJudgments.lean`](../../GebLean/CategoryJudgments.lean)
  carries the four sorts and their projection maps as flat functor
  data. The dependently-typed form in
  [`GebLean/DepCategoryJudgments.lean`](../../GebLean/DepCategoryJudgments.lean)
  carries them as dependent sorts (`idT`/`compT` indexed by the
  morphisms they constrain) rather than as sorts equipped with
  projections; the two are linked by `depCatCopresheafEquiv`. The
  PLang form in
  [`GebLean/PLang/CatJudgment.lean`](../../GebLean/PLang/CatJudgment.lean)
  is the structural form repackaged with four independent universe
  parameters.
- Route by which `Cat` is exhibited as reflective. The direct route
  in
  [`GebLean/CatJudgmentAdjunction.lean`](../../GebLean/CatJudgmentAdjunction.lean)
  (and its universe-flexible PLang counterparts
  [`GebLean/PLang/CatJudgmentAdjunction.lean`](../../GebLean/PLang/CatJudgmentAdjunction.lean)
  and
  [`GebLean/PLang/CatJudgCoprAdjunction.lean`](../../GebLean/PLang/CatJudgCoprAdjunction.lean))
  builds `L`, `Φ`, and the counit-iso over the copresheaf category
  directly. The Grothendieck route in
  [`GebLean/PLang/CatJudgGrAdjunction.lean`](../../GebLean/PLang/CatJudgGrAdjunction.lean),
  over the presentation in
  [`GebLean/PLang/CatJudgGrothendieck.lean`](../../GebLean/PLang/CatJudgGrothendieck.lean),
  instead reaches the same reflection through a layered Grothendieck
  construction. The dependent route in
  [`GebLean/DepCategoryAdjunction.lean`](../../GebLean/DepCategoryAdjunction.lean),
  over the full-subcategory equivalence of
  [`GebLean/DepCategoryCat.lean`](../../GebLean/DepCategoryCat.lean),
  reaches it by composing per-property reflective inclusions.
- Base versus lifted. The lift to functor categories in
  [`GebLean/CatValuedFunctor.lean`](../../GebLean/CatValuedFunctor.lean)
  reproduces the base adjunction pointwise over an arbitrary indexing
  category `C`.

The central definitions correspond evidently (each formulation's `Φ`
sends a category to the same four sorts and maps, each `L` to the same
completion-quotient-closure of the relational specification); the
correspondences are stated at the level of these definitions, not as
proved equivalences between the formulations.

## Dependencies

This area builds on the
[quivers, semicategories, acyclic categories](quivers.md) layer (free
and cofree categories on a quiver, presentations by generators and
relations), which supplies the underlying quiver and the free-morphism
machinery that `L` quotients.

## Pointers

- [`docs/research/novelty-analysis.md`](../research/novelty-analysis.md) — prior-art
  comparison of the `L ⊣ Φ` reflective embedding (nerve–realization,
  essentially algebraic theories, walking structures, polynomial
  functors) and the respects in which it appears novel.
- The
  [Category-judgment encodings](../index.md)
  section of the documentation index records the established narrative
  for this area, including the closure analysis of universal-property
  preservation under `L ⊣ Φ`.
