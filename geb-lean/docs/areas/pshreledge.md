# PshRelEdge and edge-of-presheaf machinery

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
  - [Foundations](#foundations)
  - [`PshRelEdge` family](#pshreledge-family)
  - [Relational span diagrams and bicategory](#relational-span-diagrams-and-bicategory)
  - [Type expressions and relational interpretation](#type-expressions-and-relational-interpretation)
  - [Utility modules](#utility-modules)
- [Alternative formulations](#alternative-formulations)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area constructs and studies the *edge category of presheaf
relations* `PshRelEdge(C)`: the category whose objects are triples
`(P, Q, R)` with `R` a subfunctor of `P × Q` in `PSh(C)`, and whose
morphisms are pairs of natural transformations preserving
relatedness. It provides Geb with a presheaf-level semantic domain for
parametricity — a setting in which types are presheaves, relations are
subfunctors of products, graphs of natural transformations are graph
relations, and the identity-extension and free-theorem properties hold
by construction.

## Mathematical context

The construction traces to Reynolds's parametricity (1983) and its
relational rendering in Wadler's *Theorems for free!* (1989): types
are interpreted as sets, and a type expression `T` is interpreted as a
relation `T(R)` between any two sets `A` and `B` connected by a
relation `R`. The presheaf generalization replaces sets with presheaves
on a small category `C` and functions with natural transformations;
subfunctors of product presheaves replace `Prop`-valued relations.

The *Barr extension* lifts an endofunctor `G : PSh(C) ⥤ PSh(C)` to act
on relations: `pshBarrLiftRel G R` is the relation whose elements are
pairs `(G P, G Q)`-related by applying `G` to related pairs, the
presheaf analogue of Wadler's `A* = {(map a x, map a y) | (x,y) ∈ A}`.
The *identity-extension property* (Reynolds 1983; Hermida–Reddy–Robinson
2014, Proposition 6.3) states that the identity section functor
`pshRelIdentFunctor : PSh(C) ⥤ PshRelEdge(C)`, which sends `P` to
`(P, P, pshRelId P)`, is cartesian closed and preserves all finite
limits and colimits. This distinguishes parametric from merely natural
behaviour.

The edge category sits inside a *reflective chain*:

```text
PSh(C) ↪ PshRelEdge(C) ↪ Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)
```

where each inclusion is reflective. The reflectors are: codomain
projection (for `PSh(C) ↪ Arrow(PSh(C))`), functionalization via
pushout (for `PshRelEdge(C) ↪ Arrow(PSh(C))`), and the span-to-arrow
pushout reflector.

`PshRelEdge(C)` is a *quasitopos*: it has finite limits, finite
colimits, and exponentials (making it cartesian closed), and a strong
subobject classifier `(Ω, Ω, full)` where `Ω` is the sieve presheaf of
`PSh(C)`. It is equivalently the full subcategory of separated spans in
`WalkingSpan ⥤ PSh(C)`.

The reflexive-graph structure on the chain — vertex category `PSh(C)`,
edge category `PshRelEdge(C)`, identity section
`pshRelIdentFunctor` — is captured abstractly by
`ReflexiveGraphData`. The identity-extension property is then the
statement that this section is cartesian closed and colimit-preserving,
distinguishing it from an arbitrary identity section.

## Modules

### Foundations

- [`GebLean/PshRelDouble.lean`](../../GebLean/PshRelDouble.lean) —
  the double category of presheaf relations. Introduces `PshRel P Q`
  (a `Subfunctor` of `pshProdPresheaf P Q`), `pshRelRelated`
  (the morphism condition / square type), `PshRelEdge C` (the edge
  category structure), and `pshBarrLiftRel` (the Barr extension of
  an endofunctor to relations). The presheaf-level double category of
  relations has its nearest antecedent in Wadler (1989) and the
  categorical account of the Barr extension.

- [`GebLean/RelDouble.lean`](../../GebLean/RelDouble.lean) —
  type-level double category of relations (see
  [Alternative formulations](#alternative-formulations)). `relType`,
  `graphRel`, `functorRelLift`, and `profBarrLiftRel` are the
  type-level analogues of the constructions in `PshRelDouble.lean`.
  This module is the pointwise (type-level) specialization of
  Wadler (1989); the `Type`-valued case is the special case of
  `PSh(Discrete Unit)`.

- [`GebLean/YonedaRelDouble.lean`](../../GebLean/YonedaRelDouble.lean)
  — Yoneda-relations double category (see
  [Alternative formulations](#alternative-formulations)). Introduces
  `YonedaRel X Y` (relations whose carrier is a presheaf on the
  category of elements of `yoneda X × yoneda Y`) and `relRelated`
  (the commutativity square for morphisms in `C`). Builds
  `yonedaProd : C ⥤ C ⥤ (Cᵒᵖ ⥤ Type v)` as a composition of the
  Yoneda embedding, `prodFunctorToFunctorProd`, and the binary
  product functor.
  The Yoneda-relations version of the double category has its
  nearest antecedent in the correspondence between spans on Yoneda
  and profunctors.

### `PshRelEdge` family

The modules below all operate on `PshRelEdge C` and its structure.
They are organized by theme; individual declarations are cited where
needed for orientation.

- [`GebLean/PshRelEdgeExp.lean`](../../GebLean/PshRelEdgeExp.lean) —
  cartesian-closed structure of `PshRelEdge C`.
  - `pshRelProd`: product of two presheaf relations.
  - `pshRelEdgeExp`: the exponential in `PshRelEdge C`, with
    `pshArrowRel R T` as the arrow relation.
  - `pshRelEdgeCurry` / `pshRelEdgeUncurry`: the currying
    isomorphism, witnessed constructively.
  The cartesian-closed structure follows Wadler (1989) Section 2
  and the standard internal-hom in functor categories.

- [`GebLean/PshRelEdgeLimits.lean`](../../GebLean/PshRelEdgeLimits.lean)
  — finite limits and colimits in `PshRelEdge C`.
  - `pshRelEdgeTerminal` / `pshRelEdgeInitial`: terminal and initial
    objects `(⊤, ⊤, pshRelId ⊤)` and `(∅, ∅, pshRelId ∅)`.
  - `pshRelEdgeCoprod`: binary coproduct.
  - `pshRelEdgeEqualizer` / `pshRelEdgeCoequalizer`: (co)equalizers.
  The finite limit/colimit constructions for the edge category
  have their antecedents in the general existence results for
  presheaf toposes.

- [`GebLean/PshRelEdgeIdentPreservation.lean`](../../GebLean/PshRelEdgeIdentPreservation.lean)
  — identity-extension property (IEP). Proves that
  `pshRelIdentFunctor` preserves exponentials (`pshRelIdentFunctor_preserves_exp`),
  finite products and terminal, and all finite colimits (initial,
  coproducts, coequalizers).
  The IEP follows Reynolds (1983) and Hermida–Reddy–Robinson
  (2014, Proposition 6.3); the colimit-preservation extension
  appears to be novel at this level of generality.

- [`GebLean/PshRelEdgeSOClassifier.lean`](../../GebLean/PshRelEdgeSOClassifier.lean)
  — strong subobject classifier. Establishes that `PshRelEdge C` is a
  quasitopos by constructing `pshRelEdgeSOClassifier` — the edge
  `(Ω, Ω, full)` where `Ω = pshSieveFunctor C` — together with
  `pshRelEdgeSOClassify` (the classifying morphism for a strong
  sub-edge).
  The quasitopos structure of the double category of relations is
  standard; mathlib has the subobject classifier for `PSh(C)`
  (`CategoryTheory.Topos.Classifier`) but not this edge-level
  extension.

- [`GebLean/PshRelEdgeInclusion.lean`](../../GebLean/PshRelEdgeInclusion.lean)
  — inclusion of `PshRelEdge C` into `PSh(C × I^op)`. Constructs the
  fully faithful functor `pshRelEdgeInclusionFunctor` (sending
  `(P, Q, R)` to the span `P ← R.toFunctor → Q`) and the reflective
  adjunction `pshRelEdgeSepFunctor ⊣ pshRelEdgeInclusionFunctor`,
  where the separation reflector replaces a span by its image.
  The separation-reflection adjunction has its nearest antecedent
  in the general theory of sheaves and separated presheaves.

- [`GebLean/PshRelEdgeSeparation.lean`](../../GebLean/PshRelEdgeSeparation.lean)
  — separated-span characterization of `PshRelEdge C`. Introduces
  `IsSeparatedSpan` (joint monicity of span projections) and
  `pshRelEdgeSepEquiv` (the equivalence between `PshRelEdge C` and
  the full subcategory of separated spans in `WalkingSpan ⥤ PSh(C)`).
  The separated-presheaf characterization
  `PshRelEdge C ≅ Sep_J(C × I^op)` is standard; mathlib has
  separated presheaves for sites but not this span form.

- [`GebLean/PshRelEdgeFunctionalize.lean`](../../GebLean/PshRelEdgeFunctionalize.lean)
  — functionalization reflector. Constructs
  `pshRelEdgeFunctionalizeFunctor` (the left adjoint sending an edge
  `(P, Q, R)` to the pushout-arrow `L(R)`) and the adjunction
  `pshRelEdgeFunctionalizeAdj : functionalize ⊣ graph`, establishing
  `PshRelEdge C` as a reflective subcategory of `Arrow(PSh(C))`.
  The functionalization adjunction via pushout has its nearest
  antecedent in image-factorization in a regular category.

- [`GebLean/PshRelEdgeGraphRestriction.lean`](../../GebLean/PshRelEdgeGraphRestriction.lean)
  — restriction to graph relations. Establishes that the
  parametricity condition `pshRelRelated` reduces to a naturality
  square on graph relations (`pshBarrLiftRel_graph_related_iff`), and
  that the Barr embedding `pshBarrEmbeddingFunctor` is fully faithful
  (`pshBarrEmbeddingFunctor_fullyFaithful`). Also contains the *free
  theorem* (`natTransToBarrEndo` / `barrEndoToNatTrans`) and
  `MapFamily` with its decomposition theorem
  (`mapFamilyDecompLeft` / `mapFamilyDecompRight`).
  The graph-restriction characterization and the Barr-embedding
  full faithfulness are implicit in Wadler (1989) Sections 3.1
  and 3.5, but the categorical formulation at presheaf level
  appears novel (`unverified`).

- [`GebLean/PshRelEdgeOverOmega.lean`](../../GebLean/PshRelEdgeOverOmega.lean)
  — connection to the subobject classifier. Constructs
  `pshOverOmegaEdgeFunctor : Over Ω ⥤ PshRelEdge C` (sending a
  characteristic map `χ : X ⟶ Ω` to the diagonal relation restricted
  to the classified subobject) and shows that `pshRelIdentFunctor`
  factors as `pshTruthLabelFunctor ⋙ pshOverOmegaEdgeFunctor`.
  The factorization of the identity section through `Over Ω` is
  standard; mathlib has the sieve classifier but not this
  factorization.

- [`GebLean/PshRelEdgeReflectiveChain.lean`](../../GebLean/PshRelEdgeReflectiveChain.lean)
  — the full reflective chain. Assembles the pairwise inclusions and
  reflectors into the composed chain
  `PSh(C) ↪ PshRelEdge(C) ↪ Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)`,
  with `Reflective` instances (`pshRelEdgeFromPshAdj`,
  `pshSpanFromArrowAdj`, `pshSpanFromPshAdj`) built by `Reflective.comp`.
  The individual steps of the reflective chain are known, but
  we have found no such construction in the literature for this
  exact four-level chain with presheaf pushouts.

### Relational span diagrams and bicategory

- [`GebLean/RelSpanDiagram.lean`](../../GebLean/RelSpanDiagram.lean)
  — type-level relational span category. Introduces `RelSpanObj`
  (a bipartite inductive with `typeNode` and `relNode` constructors)
  and its category structure, establishing the collage presentation of
  `relSpanProfunctor`.
  The collage / category of elements of a profunctor at the type
  level is standard.

- [`GebLean/PshRelSpanDiagram.lean`](../../GebLean/PshRelSpanDiagram.lean)
  — presheaf-level relational span category. Lifts `RelSpanObj` to
  presheaves, defining `PshRelSpanObj C` with embeddings
  `constPresheafEmbedding`, `pshCovariantEmbedding`,
  `pshContravariantEmbedding`, and `yonedaConstEmbedding` into
  `PshParametricFunctor C D`.
  The presheaf collage has its antecedent in the general
  two-sided Grothendieck construction.

- [`GebLean/PshSpanBicategory.lean`](../../GebLean/PshSpanBicategory.lean)
  — bicategory of spans in `PSh(C)`. Introduces `PshSpanBicat C`
  (presheaves as 0-cells, spans as 1-cells via `PshProdOver`), with
  `pshSpanWhiskerLeft` (left whiskering of 2-cells via pullback) and
  the bicategory laws; `PshSpanCat C` abbreviates
  `WalkingSpan ⥤ PSh(C)`.
  The span bicategory in a cartesian category is standard; mathlib
  has `CategoryTheory.Bicategory.Basic` but not the instantiation
  to presheaf spans.

### Type expressions and relational interpretation

- [`GebLean/PshTypeExpr.lean`](../../GebLean/PshTypeExpr.lean) —
  presheaf-level type expressions. Generalizes `TypeExpr` (from
  `ParanaturalTopos.lean`) to presheaf categories: `PshTypeExpr C`
  has constructors `var`, `app G T`, and `arrow T₁ T₂`; `interp T P Q`
  is the profunctor interpretation; `fullRelInterp T R` is the full
  relational interpretation of Wadler (1989); `PshTypeAbs` and
  `pshTypeAbsRel` formalize the relational interpretation of
  `∀X. T(X)`.
  `pshTypeAbsRel` is `unverified`.

- [`GebLean/RelInterpComposition.lean`](../../GebLean/RelInterpComposition.lean)
  — composition properties of `TypeExpr.relInterp`. Proves that the
  relational interpretation composes transitively for `var` and
  functor applications (`graphRel_comp`,
  `TypeExpr.relInterp_comp_leaf`) and characterizes when it
  decomposes, noting that the decomposition fails for nested
  contravariant arrow types.
  The composition/decomposition analysis of graph relations is
  standard; the failure for arrow types is the standard observation
  about parametricity and higher-order types.

### Utility modules

- [`GebLean/Utilities/ArrowSpanAdjunction.lean`](../../GebLean/Utilities/ArrowSpanAdjunction.lean)
  — the arrow–span adjunction. `arrowSpanInclusion C` embeds
  `Arrow C` into `WalkingSpan ⥤ C` (sending `f` to
  `P ←[id]─ P ─[f]→ Q`); `arrowSpanInclusion.fullyFaithful` records
  full faithfulness; `spanArrowReflector` is the left adjoint via
  pushout.
  The standard arrow–span reflective adjunction has its antecedent
  in the general theory of reflective subcategories.

- [`GebLean/Utilities/ReflexiveGraph.lean`](../../GebLean/Utilities/ReflexiveGraph.lean)
  — reflexive-graph category data. `ReflexiveGraphData V E` packages
  source, target, and identity functors `E ⥤ V` and `V ⥤ E` with
  the two retraction equalities `ident ⋙ src = 𝟭 V` and
  `ident ⋙ tgt = 𝟭 V`.
  The abstract data of a reflexive graph has antecedents in
  Hermida–Reddy–Robinson (2014) and standard graph-category theory.

- [`GebLean/Utilities/SpanFamily.lean`](../../GebLean/Utilities/SpanFamily.lean)
  — span-family data and morphisms. `SpanFamilyData` packages vertex
  objects, edge objects, and two projection families; `SpanFamilyHom`
  is the morphism structure satisfying the two naturality conditions;
  `SpanFamily` abbreviates `GraphSpanObj V E ⥤ D`.

- [`GebLean/Utilities/WSubfunctor.lean`](../../GebLean/Utilities/WSubfunctor.lean)
  — witnessed subfunctors. `WSubfunctor F` is a constructive variant
  of mathlib's `Subfunctor F`: it stores a total presheaf and an
  inclusion morphism rather than a `Prop`-valued membership predicate,
  enabling constructive inversions when the inclusion is mono.
  `WSubfunctor.toSubfunctor` forgets back to propositional membership.
  The constructive (witness-carrying) counterpart of `Subfunctor`
  is not in mathlib, which has `Subfunctor.Basic` but not the
  witnessed form.

## Alternative formulations

The shared concept is: *a double category of relations in a presheaf
topos*, with objects, horizontal morphisms, vertical relations, and
squares expressing when morphisms preserve relatedness. The repository
contains three formulations of this concept, at different levels of
generality and with different relation carriers. They are variations
arising from the search for the right level of abstraction and the
right embedding into Geb's parametricity machinery; the curated
`geb-mathlib` port may settle on one or a further variation.

- `Type`-level formulation in
  [`GebLean/RelDouble.lean`](../../GebLean/RelDouble.lean). Objects
  are types, vertical relations are `Prop`-valued predicates, and the
  Barr lift is `functorRelLift F R` (for a `Type ⥤ Type` functor).
  This is the direct encoding of Wadler (1989) without presheaves.

- Presheaf-level formulation in
  [`GebLean/PshRelDouble.lean`](../../GebLean/PshRelDouble.lean).
  Objects are presheaves on an arbitrary `C`, vertical relations are
  subfunctors of product presheaves, and the Barr lift is
  `pshBarrLiftRel G R` for `G : PSh(C) ⥤ PSh(C)`. This is the main
  working formulation for the area; the `PshRelEdge*` family builds
  on it.

- Yoneda-relations formulation in
  [`GebLean/YonedaRelDouble.lean`](../../GebLean/YonedaRelDouble.lean).
  Objects are objects of `C`, vertical relations are presheaves on the
  category of elements of `yoneda X × yoneda Y` (spans in `C` from
  `X` to `Y`), and squares are commutative squares of morphisms in
  `C`. This formulation connects the relational double category to
  the profunctor calculus via the standard equivalence
  `PSh(∫F) ≃ PSh(C)/F`.

The three formulations share the same double-category shape
(objects, horizontal morphisms, vertical morphisms, squares). The
`Type`-level formulation is the special case of the presheaf-level
one at `C = Discrete Unit`; the Yoneda-relations formulation differs
in that its vertical morphisms are presheaves on categories of
elements rather than subfunctors of product presheaves directly, and
its objects live in `C` rather than `PSh(C)`.

## Dependencies

This area builds on:

- The profunctors-ends area (`GebLean/Utilities/Profunctors.lean` and
  related): the Barr lift for profunctors (`profBarrLiftRel`) and the
  connection to the span bicategory depend on profunctor machinery.
- The internal-presheaf area (Grothendieck construction, the category
  of elements `∫F`): `YonedaRelDouble.lean` and `PshRelSpanDiagram.lean`
  use the equivalence `PSh(∫F) ≃ PSh(C)/F` and the Grothendieck
  construction to connect the relational span category to parametric
  functors.

## Pointers

Research notes directly relevant to this area:

- [`docs/research/DoubleCategory.md`](../research/DoubleCategory.md)
  — background on double categories, Wadler's relational
  interpretation, and the edge-category construction.
- [`docs/research/ParametricityViaYonedaRelations.md`](../research/ParametricityViaYonedaRelations.md)
  — the Yoneda-relations approach to parametricity and its
  connection to profunctors.
- [`docs/research/arrow-span-cospan-adjunctions.md`](../research/arrow-span-cospan-adjunctions.md)
  — the arrow–span–cospan adjunction chain underlying the
  reflective-chain construction.
- [`docs/research/bicategorical-correspondence.md`](../research/bicategorical-correspondence.md)
  — the bicategorical correspondence used in `PshSpanBicategory.lean`.
