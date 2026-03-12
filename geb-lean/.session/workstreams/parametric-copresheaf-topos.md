# Workstream: Parametric Polymorphism via PshRelEdge

## Status

Active

## Context

Develop the general theory of parametric polymorphism via
the edge category `PshRelEdge C` and its reflective
embedding into the presheaf topos `[WalkingSpan, PSh(C)]`.

`PshRelEdge C` is the category of presheaf relations:
objects are triples `(P, Q, R : PshRel P Q)`, morphisms
are pairs of natural transformations preserving
relatedness.  This is a standard double-categorical
construction (the horizontal edge category of the double
category of relations internal to `PSh(C)`), enriched
over a presheaf topos.

### Relationship to Wadler's framework

The primary goal is to match each concept in Wadler's
"Theorems for free!" (1989) and the Reasonably Polymorphic
blog post with a generalized version using `PshRelEdge C`
and `[WalkingSpan, PSh(C)]`.  See the Wadler correspondence
section below for the concept mapping.

### Why PshRelEdge (not PshRelSpanObj)

The former approach used `PshRelSpanObj C`, a category
whose objects are type-nodes and relation-nodes with only
projection morphisms.  That category ignores most morphisms
of the underlying category `C` and only recovers
parametricity after taking a limit or colimit.

`PshRelEdge C` is categorically natural: it respects
morphisms from the start, has a rich structure (finite
limits/colimits, exponentials, strong subobject
classifier), and embeds reflectively into the presheaf
topos `[WalkingSpan, PSh(C)]` (itself a presheaf category
by uncurrying).

The three-layer picture:

```text
[WalkingSpan, PSh(C)]  presheaf topos (exact)
       |
       | pshRelEdgeSepFunctor (separation reflector)
       v
  PshRelEdge C          quasitopos (separated presheaves)
       |
       | sheafification (conjectural)
       v
  Sh_J(C x I^op)       sheaf topos (exact)
```

### Relationship to old frameworks

- **PshRelSpanObj / PshParametricFunctor /
  PshParametricPresheaf**: Still exist in
  `PshRelSpanDiagram.lean` but are being superseded by
  `PshRelEdge`.  Definitions that target `PshRelSpanObj`
  (such as the covariant/contravariant/profunctor
  embeddings) need PshRelEdge analogues.
- **PshTypeExpr / PshParametricFamily**: Exploratory
  inductive constructions.  Not standard category theory;
  we aim to handle arbitrary categories rather than
  specific inductive type systems.
- **SpanFamily**: Equivalent unpacked view of copresheaves
  on `PshRelSpanObj`.  Useful for IEP analysis but
  secondary to the PshRelEdge approach.

## Completed

### Double category and relation infrastructure

- [x] **Double category of presheaf relations.**
  `PshRelDouble` with `pshRelId`, `pshRelComp`,
  `pshRelGraph`, `pshRelDagger`, `pshRelRelated`,
  `pshRelGraphFunctor`, and all double category laws.
  (`PshRelDouble.lean`)

- [x] **Yoneda relation double category.**
  `YonedaRelDouble` with identity, composition, graph
  functor, double category laws, and terminal
  specialization.  (`YonedaRelDouble.lean`)

- [x] **Barr extension (relation lifting).** Covariant
  `pshBarrLiftRel`, contravariant `pshContraBarrLiftRel`,
  profunctor `pshProfBarrLiftRel`, with graph
  preservation `pshBarrLiftRel_graph`.
  (`PshRelDouble.lean`)

- [x] **Arrow relation.** `pshArrowRel` with relatedness
  preservation.  (`PshRelDouble.lean`)

- [x] **Barr lift as edge endofunctor.**
  `pshBarrLiftEdgeFunctor G : PshRelEdge C => PshRelEdge C`.
  (`PshRelDouble.lean`)

### PshRelEdge category structure

- [x] **Named category instance.** `pshRelEdgeCategory`
  (`PshRelDouble.lean`)

- [x] **Finite limits and colimits.** Terminal, initial,
  binary products, binary coproducts, equalizers,
  coequalizers.  (`PshRelEdgeLimits.lean`)

- [x] **Exponential.** `(FunctorHom, FunctorHom,
  pshArrowRel)` with exponential adjunction.
  (`PshRelEdgeExp.lean`)

- [x] **Strong subobject classifier.**
  `pshRelEdgeSOClassifier` = `(Omega, Omega, full)`.
  Classifying morphism `pshRelEdgeSOClassify`, uniqueness
  `pshRelEdgeSOClassify_unique`, and pullback
  characterization `pshRelEdgeSOClassify_pullback`.
  (`PshRelEdgeSOClassifier.lean`)

### Identity section functor (Wadler: identity extension)

- [x] **pshRelIdentFunctor.** Sends `P` to
  `(P, P, pshRelId P)`.  (`PshRelDouble.lean`)

- [x] **Preserves exponentials.**
  `pshRelIdentFunctor_preserves_exp`: the IEP as a
  cartesian closed functor property.
  (`PshRelEdgeIdentPreservation.lean`)

- [x] **Preserves limits.** Products, terminal, equalizers.
  (`PshRelEdgeIdentPreservation.lean`)

- [x] **Preserves colimits.** Coproducts, initial,
  coequalizers.  (`PshRelEdgeIdentPreservation.lean`)

- [x] **Factorization through Over Omega.**
  `pshOverOmegaEdgeFunctor : Over Omega => PshRelEdge C`
  sends `(X, chi)` to `(X, X, Delta_chi)`.
  `pshTruthLabelFunctor : PSh(C) => Over Omega` sends
  `X` to `(X, true . !_X)`.
  `pshRelIdentFunctor_factorization :
  pshTruthLabelFunctor >> pshOverOmegaEdgeFunctor =
  pshRelIdentFunctor`.
  (`PshRelEdgeOverOmega.lean`)

  The reverse map `(P, Q, R) |-> (P x Q, chi_R)` from
  `PshRelEdge C` to `Over Omega` is NOT functorial:
  the `Over.w` condition requires sieve equality
  (biconditional), while `PshRelEdge` morphisms only
  give the forward direction.

### Reflective embedding into presheaf topos

- [x] **Fully faithful inclusion.**
  `pshRelEdgeInclusionFunctor` with
  `pshRelEdgeInclusionFullyFaithful`.
  (`PshRelEdgeInclusion.lean`)

- [x] **Separation reflector.**
  `pshRelEdgeSepFunctor` with adjunction
  `pshRelEdgeSepAdjunction`.
  (`PshRelEdgeInclusion.lean`)

- [x] **Reflector preserves finite products.**
  `pshRelEdgeSepPreservesFiniteProducts`,
  `CartesianMonoidalCategory (PshRelEdge C)`.
  (`PshRelEdgeInclusion.lean`)

- [x] **Exponential ideal.**
  `ExponentialIdeal (pshRelEdgeInclusionFunctor C)`.
  (`PshRelEdgeInclusion.lean`)

- [x] **Inclusion preserves coproducts.**
  `inclusionPreservesBinaryCoproducts`,
  `inclusionPreservesInitial`.
  (`PshRelEdgeInclusion.lean`)

### Span bicategory

- [x] **PshSpanBicategory.**
  `pshSpanBicategory : Bicategory (PshSpanBicat C)` with
  all 12 coherence axioms.
  (`PshSpanBicategory.lean`)

### Presheaf infrastructure

- [x] **Presheaf exponentials.** `functorCatMonoidalClosed`
  for general presheaf categories.  (`Presheaf.lean`)

- [x] **Subobject classifiers.** `pshClassifierData`,
  `coPshClassifierData`.  (`Presheaf.lean`)

- [x] **Sections of exponentials.**
  `functorHomSectionToNatTrans` with roundtrips.
  (`Presheaf.lean`)

### Old-framework results (PshRelSpanObj-based)

These are completed in the old framework but need
PshRelEdge analogues to be considered done for the new
approach:

- [x] (old) **Relational span category.**
  `PshRelSpanObj C`, `pshRelSpanCollageIso`,
  `relSpanPshRelSpanIso`.
  (`PshRelSpanDiagram.lean`)

- [x] (old) **Covariant embedding (fully faithful).**
  `pshCovariantEmbedding` into `PshRelSpanObj`.
  (`PshRelSpanDiagram.lean`)

- [x] (old) **Contravariant embedding (fully faithful).**
  `pshContravariantEmbedding` into `PshRelSpanObj`.
  (`PshRelSpanDiagram.lean`)

- [x] (old) **Profunctor embedding.**
  `pshProfunctorEmbedding` into `PshRelSpanObj`.
  (`PshRelSpanDiagram.lean`)

- [x] (old) **Paranatural embedding (faithful).**
  `pshParanaturalProfEmbedding` into `PshRelSpanObj`.
  (`PshRelSpanDiagram.lean`)

- [x] (old) **Identity extension for SpanFamily.**
  `HasIdentityExtension`, `pshCovariantSpanData_iep`,
  `pshContravariantSpanData_iep`.
  (`SpanFamily.lean`, `PshRelSpanDiagram.lean`)

- [x] (old) **Parametricity-paranaturality separation.**
  `divApplyId_parametric`, `divApplyId_not_paranatural`.
  (`ParanaturalTopos.lean`)

## Tasks

### Wadler correspondence (new)

Formalize the Wadler/"Theorems for free!" correspondence
using `PshRelEdge C` and `[WalkingSpan, PSh(C)]`.

- [x] **W1. Graph restriction to naturality.**
  `pshBarrLiftRel_graph_related_iff`,
  `pshBarrLiftRel_graph_related_hetero_iff`,
  `pshBarrLiftRel_id_related_iff`,
  `arrowEndofunctor`,
  `pshBarrLiftEdge_graphNatIso`,
  `pshBarrLiftEdge_identNatIso`.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W2. Rearrangement theorem.**
  `natTransToBarrEndo G σ` embeds `σ : G ⟶ G` as an
  endomorphism of `pshBarrEmbedding G`.
  `barrEndoToNatTrans G τ` extracts `G ⟶ G` from any
  such endomorphism by taking `srcMap`.
  `natTransToBarrEndo_barrEndoToNatTrans` and
  `barrEndoToNatTrans_natTransToBarrEndo` establish
  the bijection, with the forward direction deriving
  the commutativity square from `pshBarrLiftRel_id_related_iff`.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W3. Map decomposition.**
  `MapFamily G` is a natural transformation from
  `Arrow.leftFunc ⋙ G` to `Arrow.rightFunc ⋙ G`.
  `mapFamilyDecompLeft` and `mapFamilyDecompRight`
  derive the decomposition `m(α) = m(𝟙) ≫ G.map α`
  and `m(α) = G.map α ≫ m(𝟙)` from arrow-category
  naturality.  `mapFamilyToNatTrans` /
  `natTransToMapFamily` with roundtrip theorems give
  a bijection between map families and `G ⟶ G`.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W4. Fold free theorem.**
  `foldFreeTheorem_graph`: the catamorphism of an
  initial F-algebra commutes with algebra homomorphisms
  (Wadler Section 3.2/3.6).
  `foldFreeTheorem_pshRelRelated_graph`: expressed as
  `pshRelRelated` at graph edges with `pshRelId` domain.
  `foldFreeTheorem_barrLift_graph`: takes the algebra
  homomorphism hypothesis in `pshRelRelated` form at
  Barr-lifted graph relations.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W5. Sort/nub conditional free theorems.**
  Wadler Section 3.3: `sort` commutes with monotone
  maps, `nub` commutes with injective maps.
  `conditional_freeTheorem_graph`: given a family
  `σP` natural on morphisms satisfying predicate `P`,
  `σP` is related at Barr-lifted graphs of `P`-morphisms.
  `conditional_graph_implies_nat`: converse direction.
  `conditional_edge_freeTheorem`: generalization from
  morphism predicates to edge predicates.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W6. Filter decomposition.** Wadler Section 3.7:
  filter commutes with maps that preserve the
  predicate. Covered by the general conditional free
  theorem framework in W5
  (`conditional_freeTheorem_graph` and
  `conditional_edge_freeTheorem`), with `P` =
  "predicate-preserving". Specific filter instances
  would be applications of this general pattern.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W7. Polymorphic equality impossibility.** Wadler
  Section 3.4. `parametric_constant`: any graph-natural
  family `σ : ∀P c, P.obj c → P.obj c → β` satisfies
  `σ P c a b = σ P c a a` (constant in both arguments).
  `parametric_constant_value`: all values equal
  `σ (pshTerminal C) c ⟨⟩ ⟨⟩`.
  `no_parametric_equality`: Bool specialization.
  Proof: naturality at the unique map to the terminal
  presheaf collapses all elements.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W8. Yoneda isomorphism.** Wadler Section 3.8:
  `∀X. (A → X) → X ≅ A`.
  `yoneda_via_parametricity`: a graph-natural family
  `σ : ∀P, (A ⟶ P) → ∀c, P.obj c` satisfies
  `σ Q g c = g.app c (σ A (𝟙 A) c)`, so it is
  determined by `σ A (𝟙 A)`.
  `yoneda_embedding_natural`: every element
  `a : (c : Cᵒᵖ) → A.obj c` determines a natural
  family `fun P f c => f.app c (a c)`.
  `yoneda_parametricity_inverse`: alias for the
  inversion direction.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **W9. Parametricity as tautology in PshRelEdge.**
  `IsParametricSection F s`: a section is parametric
  iff it is natural w.r.t. edge morphisms.
  `natTrans_isParametricSection`: a global section
  (natural transformation from the terminal copresheaf)
  is automatically parametric.
  `parametricSectionToNatTrans`: converse, a parametric
  section determines a global section.
  `isParametricSection_at`: the parametricity condition
  at any edge morphism follows from `hs f` (tautological).
  (`PshRelEdgeGraphRestriction.lean`)

### Embedding endofunctors into PshRelEdge

Port the embeddings from PshRelSpanObj to PshRelEdge.

- [x] **E1. Covariant Barr embedding into PshRelEdge.**
  `pshBarrEmbedding G = pshRelIdentFunctor ⋙
  pshBarrLiftEdgeFunctor G`, with
  `pshBarrLiftEdge_identNatIso` giving
  `pshBarrEmbedding G ≅ G ⋙ pshRelIdentFunctor`.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **E2. Contravariant Barr embedding into PshRelEdge.**
  `pshContraBarrLiftEdgeFunctor F :
  (PshRelEdge C)^op => PshRelEdge C`
  (`PshRelDouble.lean`), with
  `pshContraBarrLiftRel_related` proving
  relatedness preservation. Embedding:
  `pshContraBarrEmbedding F =
  pshRelIdentFunctor.op ⋙
  pshContraBarrLiftEdgeFunctor F`, with
  `pshContraBarrLiftEdge_identNatIso` giving
  `pshContraBarrEmbedding F ≅
  F ⋙ pshRelIdentFunctor`.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **E3. Profunctor Barr embedding into PshRelEdge.**
  `pshProfBarrLiftRel G R` lifts a relation `R` through
  a profunctor `G : PSh(C)^op x PSh(C) => PSh(C)`.
  `pshProfBarrLiftRelMap` transports along natural
  transformations.  `pshProfBarrLiftRel_id` shows the
  identity relation is preserved.
  (`PshRelDouble.lean`)

- [x] **E4. Sections of Barr-embedded edges.**
  `natTrans_pshRelRelated_barrLiftRel`: naturality of
  `σ : G ⟶ G` implies relatedness at every
  Barr-lifted relation (full parametricity theorem).
  `natTransToBarrLiftEdgeEndo` lifts `σ` to a
  natural endomorphism of `pshBarrLiftEdgeFunctor G`,
  `barrLiftEdgeEndoToNatTrans` extracts back,
  `barrLiftEdgeEndoToNatTrans_natTransTo` gives
  the left inverse (extraction recovers `σ`),
  `natTransToBarrLiftEdgeEndo_restrict` shows
  agreement with `natTransToBarrEndo` at identity
  edges.
  (`PshRelDouble.lean`, `PshRelEdgeGraphRestriction.lean`)

### Graph subcategory and naturality

- [x] **G1. Graph subcategory of PshRelEdge.**
  `IsGraphEdge` predicate,
  `pshRelEdgeGraphSubcatFunctor` (lift to full
  subcategory), `pshRelEdgeGraphSubcatFullyFaithful`,
  `pshRelEdgeGraphSubcat_essSurj`.  The graph functor
  is a fully faithful, essentially surjective
  embedding into the full subcategory of graph edges.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **G2. Graph restriction functor.**
  `graphRestrictionFunctor`: precomposition with the
  graph embedding, taking copresheaves on `PshRelEdge C`
  to copresheaves on `Arrow(PSh C)`.
  `graphRestriction_barrLiftNatIso`: restriction of the
  Barr lift to graph edges recovers the arrow
  endofunctor.
  (`PshRelEdgeGraphRestriction.lean`)

- [x] **G3. Free theorem derivation via graphs.**
  `natTrans_pshRelRelated_barrLiftGraph`: naturality
  of `σ : G ⟶ G` entails relatedness at every
  Barr-lifted graph edge.
  `pshRelRelated_barrLiftGraph_implies_nat`: converse,
  graph-level parametricity recovers naturality.
  (`PshRelEdgeGraphRestriction.lean`)

### Relation composition in PshRelEdge

- [ ] **R1. Relation composition and edge morphisms.**
  Determine when an edge endofunctor `F` satisfies
  `F(R_1 ; R_2) ≅ F(R_1) ;_F F(R_2)`.  This is the
  edge-category analogue of `RelInterpComposition.lean`.

### Comparison with paranaturality

- [ ] **C1. Paranatural vs parametric in PshRelEdge.**
  Give a concrete edge-level example of a parametric
  morphism that is not paranatural.  This generalizes
  the type-level divergence (`divApplyId_parametric`,
  `divApplyId_not_paranatural`) to presheaves.

- [ ] **C2. Characterize the parametric-paranatural gap.**
  For a profunctor `H`, characterize the difference
  between parametric and paranatural morphisms in
  terms of edge-category structure.

### Internal language and type theory

- [ ] **I1. Internal parametricity statement.** Formulate
  "every element of every type is parametric" in the
  internal language of `[WalkingSpan, PSh(C)]` and
  verify it holds for elements in the image of the
  inclusion from `PshRelEdge C`.

- [ ] **I2. Directed type theory connection.** Investigate
  the connection between the internal language of the
  presheaf topos `[WalkingSpan, PSh(C)]` and
  Neumann-Licata directed type theory (POPL 2026).

### Structural results

- [ ] **S1. Sep_J equivalence.** Construct the equivalence
  `PshRelEdge C ≅ Sep_J(C x I^op)` explicitly (walking
  span I, topology J, separation).

- [ ] **S2. Yoneda extension.** Given a section restricted
  to representable presheaves (via Yoneda), extend to
  all presheaves via the density theorem.

### Documentation

- [ ] **D1. Annotate PshRelDouble.lean.** Add comments
  explaining the Wadler correspondence for each
  definition.

- [ ] **D2. Annotate PshRelEdge files.** Add comments to
  `PshRelEdgeExp.lean`, `PshRelEdgeLimits.lean`,
  `PshRelEdgeSOClassifier.lean`,
  `PshRelEdgeIdentPreservation.lean`,
  `PshRelEdgeInclusion.lean`,
  `PshRelEdgeOverOmega.lean` explaining their role in
  the Wadler correspondence.

- [ ] **D3. Update docs/parametric-copresheaf-topos.md.**
  Rewrite to center on PshRelEdge rather than
  PshRelSpanObj.

## Wadler Correspondence

- **Type as set**: presheaf `P : C^op => Type`
- **Type as relation**: `pshRelId P` via
  `pshRelIdentFunctor` (`PshRelDouble.lean`)
- **Relation**: `PshRel P Q = Subfunctor(P x Q)`
  (`PshRelDouble.lean:208`)
- **Identity relation**: `pshRelId P`
  (`PshRelDouble.lean:214`)
- **Graph of function**: `pshRelGraph alpha`
  (`PshRelDouble.lean:418`)
- **Product relation**: edge product
  (`PshRelEdgeLimits.lean`)
- **Coproduct relation**: edge coproduct
  (`PshRelEdgeLimits.lean`)
- **List/functor relation**: `pshBarrLiftRel G R`
  (`PshRelDouble.lean:1382`)
- **Function relation**: `pshArrowRel R1 R2`
  (`PshRelDouble.lean:2633`)
- **Exponential edge**:
  `(FunctorHom, FunctorHom, pshArrowRel)`
  (`PshRelEdgeExp.lean`)
- **Universal quantification**: section / limit
- **Identity extension**: `pshRelIdentFunctor`
  preserves structure
  (`PshRelEdgeIdentPreservation.lean`)
- **Parametricity Theorem**: naturality of sections
  (tautological)
- **Free theorem**: graph restriction recovers
  naturality (W1-W3, G1-G3)
- **Fold free theorem**: catamorphism commutes with
  algebra homomorphisms (W4)
- **Conditional free theorem**: parametricity over
  subcategories (W5-W6)
- **Equality impossibility**: `∀X. X → X → β` is
  constant (W7, `parametric_constant`)
- **Yoneda via parametricity**: `∀X. (A → X) → X ≅ A`
  (W8, `yoneda_via_parametricity`)
- **Parametricity as tautology**: naturality = parametricity
  (W9, `IsParametricSection`)
- **Blog: relations to bifunctors**: reflective
  embedding (`PshRelEdgeInclusion.lean`)
- **Subobject classifier**: `pshRelEdgeSOClassifier`
  (`PshRelEdgeSOClassifier.lean`)
- **Over Omega factorization**:
  `pshRelIdentFunctor_factorization`
  (`PshRelEdgeOverOmega.lean`)
- **Fixpoints**: polynomial initial algebras
  (`PolyAlg*.lean`)
