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

### Why relations replace profunctors

Parametric polymorphism associates a "free theorem"
to each universally-quantified type.  When the
quantified type has the form `∀X. F(X) → G(X)` for
covariant functors `F` and `G`, the free theorem
is a naturality condition, and naturality is
well-understood.  But for types involving mixed
variance — such as `∀X. (X → X) → (X → X)` — the
type-former `X ↦ X → X` is not a functor but a
profunctor (the hom-profunctor).

To handle profunctors, one might seek a notion of
"natural transformation between profunctors" that
captures parametricity.  Dinatural transformations
(Dubuc-Street), paranatural (strong dinatural)
transformations, and wedges have all been proposed.
These work in limited settings:

- **Dialgebra morphisms** (types of the form
  `∀X. F(X) → G(X)` where F, G are covariant):
  naturality is the right notion.
- **Paranatural transformations between
  dialgebras** (types of the form
  `∀X. (F(X) → G(X)) → (F'(X) → G'(X))`
  where F, F', G, G' are covariant):
  paranaturality agrees with parametricity.

But for types with more nesting of arrow types —
such as `∀X. ((X → X) → X) → X` — profunctors
inevitably fail.  We have proved this concretely:
`divApplyId` has this type, is parametric, but is
not paranatural (`divApplyId_not_paranatural`).
The gap is characterized by
`commuting_strictly_contains_factorizable`:
paranaturality tests for factorizable endomorphism
pairs, while parametricity tests for all commuting
pairs.

The failure is not in the choice of morphisms but
in the choice of objects: **profunctors are the
wrong objects for representing parametricity in
general**.  A profunctor `P : C^op × C → Set`
captures one level of mixed variance, but types
like `((X → X) → X) → X` have nested arrow
types that require representing the relational
content at each level.  No morphism notion between
profunctors can recover this information, because
the profunctor itself has already discarded it.

Relations are the right objects.  A relation
`R ⊆ P × Q` between presheaves retains enough
structure to compose freely via `arrowRel` and
`graphRel`, building up the relational
interpretation of any type expression to arbitrary
depth.  In a general categorical setting, relations
between sets are inadequate (since a general
category need not have enough global elements), so
we use presheaf relations `PshRel P Q` — subfunctors
of product presheaves.

To summarize: profunctors are used in this project
only to demonstrate (a) the special case where they
agree with parametricity (paranatural
transformations between dialgebras) and (b) the
points at which they inevitably fail (types with
more arrow nesting than dialgebra morphisms).
The relational framework (`PshRelEdge C` /
`PshRelDouble C`) replaces profunctors for the
general theory of parametricity.

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

- [x] **All small limits and colimits.**
  `pshRelEdgeHasLimitsOfSize`: limits inherited
  from the ambient presheaf topos (right adjoint
  inclusion creates limits).
  `pshRelEdgeHasColimitsOfSize`: colimits via
  the separation reflector applied to colimits
  in `[WalkingSpan, PSh(C)]` (reflective
  subcategory of cocomplete category is
  cocomplete).
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
  `ParametricCone G`: a parametric section of an
  endofunctor `G` on `PshRelEdge C` is a
  `Limits.Cone G` (mathlib) with vertex the
  terminal edge.  `ParametricCone.mk'` builds one
  from a family `s : ∀ e, ⊤ ⟶ G(e)` satisfying
  the cone condition `s e₁ ≫ G.map f = s e₂`.
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

- [x] **R1. Relation composition and edge morphisms.**
  Determine when an edge endofunctor `F` satisfies
  `F(R_1 ; R_2) ≅ F(R_1) ;_F F(R_2)`.
  Three theorems in `BarrLiftComposition` section of
  `PshRelDouble.lean`:
  (1) `pshProdOverToRel_comp`: pullback-based and
  existential-based compositions agree at the relation
  level.
  (2) `pshBarrLift_comp_le_barrLiftRel_comp`:
  `pshBarrLift G (R ×_Q S) ≤ pshBarrLiftRel G (R;S)`.
  (3) `pshBarrLift_comp_le_relComp_barrLiftRel`:
  `pshBarrLift G (R ×_Q S) ≤
  pshRelComp (pshBarrLiftRel G R) (pshBarrLiftRel G S)`.
  The "witnessed Barr lift" is a common refinement.
  Obstructions to full equality: reverse of (3) needs
  `G` to preserve the pullback over `Q`; reverse of (2)
  needs a section of the epi from `G(pullback)` to
  `G(R;S)`.

### Type-formers as adjoint functors

A "type-former" is a functor `G : PSh(C) → PSh(C)`
(or between categories built from `PSh(C)`) which has
a left or right adjoint.  The adjunction structure
resolves the composition questions identified in R1.

**Right adjoints preserve pullbacks.**
If `G` is a right adjoint, mathlib's
`Adjunction.rightAdjoint_preservesLimits` gives
`PreservesLimitsOfSize G`, hence
`PreservesLimitsOfShape WalkingCospan G` (pullbacks).
This resolves questions (1) from R1: given witnesses
`wR ∈ G(R.toFunctor)` and `wS ∈ G(S.toFunctor)`
matching over `G(Q)`, the pullback-preservation
universal property yields `z ∈ G(R ×_Q S)` mapping
to `(wR, wS)`.  Combined with theorem (3) from R1,
this gives:

```text
pshRelComp (pshBarrLiftRel G R) (pshBarrLiftRel G S)
  = pshBarrLiftRel G (pshRelComp R S)
```

**Left adjoints in a topos preserve finite limits.**
In `PSh(C)` (a presheaf topos), the product functor
`- × A` is left adjoint to the internal hom `[A, -]`.
Being a left adjoint in a cartesian closed category,
`- × A` preserves all colimits.  But `PSh(C)` is also
locally cartesian closed, so `- × A` preserves all
finite limits (including pullbacks).  Similarly,
coproduct functors `- + A` preserve pullbacks in a
topos (coproducts are universal/disjoint).  So the
standard left-adjoint type-formers also satisfy the
pullback-preservation condition.

**The double functor.**
When `G` preserves pullbacks, the Barr extension gives
a double functor `PshRelDouble → PshRelDouble`:

- Objects: `G.obj P`
- Horizontal morphisms: `G.map f`
- Vertical morphisms: `pshBarrLiftRel G R`
- 2-cells: `pshBarrLift_related G h` (line 1710)
- Vertical composition preserved (by pullback pres.)

**Double adjunction.**
An adjunction `F ⊣ G` where both `F` and `G` preserve
pullbacks (e.g., both are type-formers in a topos)
lifts to a double adjunction: the unit `η : Id → GF`
and counit `ε : FG → Id` are horizontal natural
transformations, and the Barr extensions provide the
vertical action with triangle identities inherited
from the original adjunction.

**Parametric right adjoints and polynomial functors.**
The pullback-preservation hypothesis in the Barr lift
composition results (`relComp_barrLiftRel_le_of_preservesPullbacks`,
`pshBarrLiftRel_comp_eq`) is weaker than right-adjointness.
Parametric right adjoints between presheaf categories —
a generalization of polynomial functors — preserve
connected limits (pullbacks, equalizers, wide pullbacks),
though not disconnected limits (products, terminal objects).
Since pullbacks are connected limits, parametric right
adjoints (and in particular polynomial functors) are
sufficient for the Barr lift composition equality.
Polynomial functors are also parametric left adjoints,
so they preserve connected colimits (including epis),
giving the reverse direction of
`pshBarrLiftRel_comp_functor_le` and hence equality
`pshBarrLiftRel (F ⋙ G) R = pshBarrLiftRel G (pshBarrLiftRel F R)`
for polynomial `G`.
This covers the typical type-forming functors in
dependent type theory (dependent sums, W-types, etc.)
without requiring them to be full right adjoints.

**Wadler correspondence.**
In Wadler's framework, the relational interpretation
of type constructors must compose correctly: `[[F(A)]]`
at relation `R` should agree with `F̂(R)`, and this
must be compatible with substitution (= composition).
The pullback-preservation theorem is the presheaf-level
formalization of this property.  For all standard
type-formers (products, coproducts, function spaces,
universal quantification), the Barr extension is a
double functor, and adjunctions between type-formers
lift to double adjunctions.

**Mathlib resources.**
Relevant declarations:

- `Adjunction.rightAdjoint_preservesLimits`
  (`Mathlib/CategoryTheory/Adjunction/Limits.lean:204`)
- `Adjunction.leftAdjoint_preservesColimits`
  (`Mathlib/CategoryTheory/Adjunction/Limits.lean:91`)
- `PreservesLimitsOfShape WalkingCospan`
  (`Mathlib/CategoryTheory/Limits/Preserves/Basic.lean`)
- `PreservesPullback.iso`
  (`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean:129`)
- `isLimitOfPreserves`
  (`Mathlib/CategoryTheory/Limits/Preserves/Basic.lean:116`)
- `Closed` and `MonoidalClosed`
  (`Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`)
- `Functor.IsRightAdjoint` (auto instance for
  `PreservesLimitsOfShape`)
  (`Mathlib/CategoryTheory/Adjunction/Limits.lean:352`)

**Tasks.**

- [x] **A1. Barr lift composition for pullback-preserving
  functors.**
  `relComp_barrLiftRel_le_of_preservesPullbacks`:
  if `[PreservesLimitsOfShape WalkingCospan G]`,
  then `pshRelComp (pshBarrLiftRel G R)
  (pshBarrLiftRel G S) ≤
  pshBarrLiftRel G (pshRelComp R S)`.
  Proof uses `cospanCompIso`,
  `IsLimit.postcomposeHomEquiv`, and the projection
  lemmas `pshProdOverComp_fst`/`_snd`.
  (`PshRelDouble.lean`)

- [x] **A2. Barr lift composition for right adjoints.**
  `relComp_barrLiftRel_le_of_rightAdjoint`:
  if `F ⊣ G`, derives
  `PreservesLimitsOfShape WalkingCospan G` from
  `Adjunction.rightAdjoint_preservesLimits` and
  applies A1.  (`PshRelDouble.lean`)

- [x] **A3. Barr lift composition chain.**
  `barrLiftRel_comp_chain`: for pullback-preserving
  `G`, the containment chain
  `pshProdOverToRel (pshBarrLift G (comp R S))
  ≤ pshRelComp (pshBarrLiftRel G R)
              (pshBarrLiftRel G S)
  ≤ pshBarrLiftRel G (pshRelComp R S)`.
  The reverse of the second containment (which would
  give full equality) requires `G` to preserve the
  epi `pullbackToRelCompFunctor`, which
  pullback-preserving functors do not do in general.
  (`PshRelDouble.lean`)

- [x] **A4. Barr extension as lax double functor.**
  `pshBarrLiftDoubleFunctorOps G` defines the four
  mapping components (objects, vertical relations,
  horizontal morphisms, squares).  Six of eight
  `DoubleFunctorLaws` hold strictly
  (`pshBarrLiftDF_preservesVId`,
  `pshBarrLiftDF_preservesHId`,
  `pshBarrLiftDF_preservesHComp`,
  `pshBarrLiftDF_preservesSqVertId`,
  `pshBarrLiftDF_preservesSqHorId`,
  `pshBarrLiftDF_preservesSqHComp`).
  Vertical composition is lax:
  `pshBarrLiftDF_laxVComp` gives
  `pshRelComp (pshBarrLiftRel G R)
    (pshBarrLiftRel G S)
    ≤ pshBarrLiftRel G (pshRelComp R S)`
  (when `G` preserves pullbacks).  Equality fails
  in general because the reverse containment needs
  `G` to preserve the epi
  `pullbackToRelCompFunctor`.
  (`PshRelDouble.lean`)

- [x] **A5. Double adjunction from adjunction.**
  Lifted adjunctions from `PSh(C)` to the edge
  category `PshRelEdge C`.  Results:
  - `pshBarrLiftRel_comp_functor_le`: composed
    Barr lift `pshBarrLiftRel (F ⋙ G) R` is
    contained in the iterated lift
    `pshBarrLiftRel G (pshBarrLiftRel F R)`,
    proved via `Subfunctor.range_comp_le`.
  - `pshBarrLiftEdgeNatTrans`: any `σ : F ⟶ G`
    lifts to a natural transformation between
    Barr extension edge functors, with
    functoriality (`_id`, `_comp`).
  - `pshBarrLiftEdgeCompComparison`: lax
    monoidal comparison from
    `pshBarrLiftEdgeFunctor (F ⋙ G)` to
    `pshBarrLiftEdgeFunctor F ⋙
    pshBarrLiftEdgeFunctor G`.
  - `adjEdgeUnit`/`adjEdgeCounit`: edge-level
    unit and counit for `F ⊣ G`.
  The adjunction is lax because the composition
  containment is strict only in the forward
  direction; the reverse needs `G` to preserve
  epis (automatic for left adjoints in a
  presheaf topos).
  (`PshRelDouble.lean`)

- [x] **A6. Right-adjoint type-formers in PshRelEdge.**
  The internal hom functor `pshIhomFunctor A`
  sends `B` to `A.functorHom B`.  Its Barr extension
  equals the arrow relation with identity domain:
  `pshBarrLiftRel_ihom_eq_arrowRel`.  Composition
  preservation (`pshBarrLiftRel_ihom_comp`) follows
  from `pshArrowRel_comp` and `pshRelComp_id_left`.
  (`PshRelDouble.lean`, section `IhomProdFunctors`)

- [x] **A7. Left-adjoint type-formers in presheaf topos.**
  The product functor `pshProdRightFunctor A`
  sends `B` to `B × A`.  Its Barr extension equals the
  product relation with identity on `A`:
  `pshBarrLiftRel_prod_eq_prodRel`.  Composition
  preservation (`pshBarrLiftRel_prod_comp`) follows
  from `pshProdRel_comp` and `pshRelComp_id_left`.
  (`PshRelDouble.lean`, section `IhomProdFunctors`)

### Comparison with paranaturality

- [x] **C1. Paranatural vs parametric in PshRelEdge.**
  Generic theorems in `RelDouble.lean`:
  `diagCompat_implies_profBarrLiftRel_graph`,
  `profBarrLiftRel_graph_iff_diagCompat` (Barr lift
  at graph relations iff DiagCompat).
  Counterexample in `ParanaturalTopos.lean`:
  `divApplyId_not_profBarrLift_preserving` (divApplyId
  does not preserve profBarrLiftRel at graphs).
  The hierarchy for `divApplyId`:
  - Paranaturality / profBarrLiftRel at graphs: fails
  - Graph parametricity (DivParametric): holds
  - Full relational parametricity: holds

- [x] **C2. Characterize the parametric-paranatural gap.**
  `CommutingEndoPair f h k` (f∘h = k∘f) vs
  `FactorizableEndoPair f h k` (∃ r, h=r∘f ∧ k=f∘r).
  Paranaturality tests factorizable pairs;
  parametricity tests all commuting pairs.
  `factorizable_implies_commuting`: every
  factorizable pair commutes.
  `constTrue_id_not_factorizable`: (constTrue, id, id)
  commutes but does not factor.
  `commuting_strictly_contains_factorizable`:
  factorizable pairs are a strict subset of commuting
  pairs.
  `divParanatural_tests_factorizable`,
  `divParametric_tests_commuting`: connect to the
  div-type definitions.
  File: `ParanaturalTopos.lean`.

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

Comprehensive mapping from Wadler's "Theorems for
free!" (1989) and the Reasonably Polymorphic blog
post to our presheaf-theoretic generalizations in
`PshRelEdge C` and `[WalkingSpan, PSh(C)]`.

Status legend: [done] = proved in Lean,
[partial] = defined but incomplete,
[open] = not yet formalized.

### Terminology: levels of morphism

Wadler works in `Set`, where "function" is
unambiguous.  Our generalization replaces `Set`
with a category `C` and then lifts to `PSh(C)`,
introducing several distinct levels of morphism
that must be distinguished.

**Wadler's concepts and their two-stage
generalization:**

| Wadler              | C-level             | PSh(C)-level                 |
|---------------------|---------------------|------------------------------|
| set                 | object of C         | presheaf P : C^op => Type    |
| monomorphic fn      | C-morphism f : X→Y  | presheaf morphism α : P ⟶ Q  |
| polymorphic type    | endofunctor on C    | endofunctor on PSh(C)        |
| parametric poly. fn | endo. nat. trans.   | endo. nat. trans. σ : F ⟶ G  |

Precise terminology used in this document:

- **C-morphism**: a morphism `f : X ⟶ Y` in the
  base category `C`.  Generalizes Wadler's
  monomorphic functions.
- **presheaf morphism**: a natural transformation
  `α : P ⟶ Q` between presheaves
  `P Q : C^op ⥤ Type`.  These are the morphisms of
  `PSh(C)`.  Each C-morphism `f` yields a presheaf
  morphism `yoneda.map f` between representables.
- **endofunctor**: a functor `G : PSh(C) ⥤ PSh(C)`.
  Generalizes Wadler's polymorphic type-formers
  (e.g. `List`).  An endofunctor `G₀` on `C` lifts
  to one on `PSh(C)` via Yoneda extension
  (`yonedaExtFunctor`).
- **endofunctor natural transformation**: a natural
  transformation `σ : F ⟶ G` between endofunctors
  `F G : PSh(C) ⥤ PSh(C)`.  Generalizes Wadler's
  parametrically polymorphic functions (e.g.
  `∀X. List(X) → List(X)`).  An endofunctor
  natural transformation on `C` lifts to one on
  `PSh(C)` via Yoneda extension.

These four levels are distinct.  In particular,
"presheaf morphism" and "endofunctor natural
transformation" are both natural transformations
in the technical sense, but between different
categories: the first is a morphism of `PSh(C)`,
while the second is a morphism in the functor
category `[PSh(C), PSh(C)]`.

### Why presheaves

The Yoneda lift from `C` to `PSh(C)` is necessary
because relations require _elements_ to express
relatedness, and a general category `C` need not
have global elements.  In `PSh(C)`, every object
has enough generalized elements (by the Yoneda
lemma: `Hom(y(X), P) ≅ P(X)`), so relations can
be defined as subfunctors of products.  The Yoneda
embedding `y : C ↪ PSh(C)` is fully faithful, so
`C` embeds without loss of information.

The generalization from Wadler proceeds in two
stages:

1. Replace `Set` with a category `C`: sets become
   objects, monomorphic functions become
   C-morphisms, type-formers become endofunctors,
   polymorphic functions become endofunctor natural
   transformations.
2. Yoneda-lift from `C` to `PSh(C)`: objects become
   representable presheaves (via `yoneda`),
   C-morphisms become presheaf morphisms between
   representables (via `yoneda.map`), endofunctors
   on `C` become endofunctors on `PSh(C)` (via
   `yonedaExtFunctor`), and endofunctor natural
   transformations lift accordingly.

Stage 2 is forced by the need for relations:
`PSh(C)` has enough elements to define `PshRel`
(subfunctors of products), while `C` in general
does not.

### Section 1: Introduction

Wadler's claim: from the type of a polymorphic
function, we can derive a theorem it satisfies.
Every function of the same type satisfies the same
theorem.  The running example is
`r : forall X. X* -> X*`, yielding the theorem
`a* . r_A = r_{A'} . a*` for all `a : A -> A'`.

Generalization: replace `Set` with `PSh(C)`,
monomorphic functions with presheaf morphisms,
polymorphic type-formers (e.g. `List`) with
endofunctors `G : PSh(C) ⥤ PSh(C)`, and
parametrically polymorphic functions (e.g.
`∀X. List(X) → List(X)`) with endofunctor natural
transformations `σ : F ⟶ G`.  Then `map a`
becomes `G.map α` for a presheaf morphism
`α : P ⟶ Q`, and the theorem becomes naturality
of `σ` with respect to `α`:
`F.map α ≫ σ_Q = σ_P ≫ G.map α`.

The Barr embedding `pshBarrEmbedding` lifts
endofunctors on `PSh(C)` to functors
`PSh(C) ⥤ PshRelEdge C`, and does so functorially
(`pshBarrEmbeddingFunctor`).  This functor is
fully faithful
(`pshBarrEmbeddingFunctor_fullyFaithful`):
endofunctor natural transformations `σ : F ⟶ G`
biject with natural transformations
`pshBarrEmbedding F ⟶ pshBarrEmbedding G`.

The specific instances in Figure 1 (head, tail,
fst, snd, zip, filter, sort, fold, I, K) become
instances of naturality for endofunctor natural
transformations between composed endofunctors on
`PSh(C)`.  Varying hypotheses (monotonicity for
sort, predicate-preservation for filter, algebra
homomorphism for fold) arise because those
endofunctor natural transformations are natural
only on subcategories of presheaf morphisms,
which `conditional_freeTheorem_graph` captures.
File: `PshRelEdgeGraphRestriction.lean`.
Status: [done] (via the general framework; see
Section 3 entries and Figure 1 entries below).

### Section 2: Types as relations

Wadler reads types as sets and as relations.
Our generalization replaces sets with presheaves
on an arbitrary category `C` (see "Why presheaves"
above), and relations with subfunctors of product
presheaves.  Monomorphic functions become presheaf
morphisms; graphs of functions become graphs of
presheaf morphisms.

**Type as set.**
Wadler: a type `A` is a set.
Generalization: a presheaf `P : C^op => Type`.
Status: [done] (foundational).

**Type as relation (identity extension).**
Wadler: each type `A` yields the identity
relation `I_A = {(x,x) | x in A}`.
Generalization: `pshRelId P` sends `P` to the
diagonal subfunctor of `P x P`.
`pshRelIdentFunctor` sends `P` to the edge
`(P, P, pshRelId P)`.
Lean: `pshRelId`, `pshRelIdentFunctor`.
File: `PshRelDouble.lean`.
Status: [done].

**Relation between types.**
Wadler: `A : A <=> A'` is `A ⊆ A x A'`.
Generalization: `PshRel P Q = Subfunctor(P x Q)`,
a sub-presheaf of the product presheaf.
Lean: `PshRel`.
File: `PshRelDouble.lean`.
Status: [done].

**Graph of a function.**
Wadler: function `a : A -> A'` yields relation
`{(x, a x) | x in A}`.
Generalization: `pshRelGraph α` for `α : P ⟶ Q`.
Lean: `pshRelGraph`.
File: `PshRelDouble.lean`.
Status: [done].

**Product relation `A x B`.**
Wadler: `((x,y),(x',y')) in A x B` iff
`(x,x') in A` and `(y,y') in B`.
Generalization: binary product in `PshRelEdge C`.
Lean: `pshRelEdgeProd`.
File: `PshRelEdgeLimits.lean`.
Status: [done].

**Coproduct relation.**
Not in Wadler (System F lacks coproducts), but a
natural extension.
Generalization: binary coproduct in `PshRelEdge C`.
Lean: `pshRelEdgeCoprod`.
File: `PshRelEdgeLimits.lean`.
Status: [done].

**List/functor relation `A*`.**
Wadler: `([x1,...,xn],[x1',...,xn']) in A*` iff
each `(xi,xi') in A`. Specialized to functions,
`a* = map a`.
Generalization: `pshBarrLiftRel G R` (covariant
Barr extension). For `G : PSh(C) => PSh(C)` and
`R : PshRel P Q`, produces `PshRel (G P) (G Q)`
via existential witnesses in `G(R.toFunctor)`.
Lean: `pshBarrLiftRel`, `pshBarrLiftEdgeFunctor`.
File: `PshRelDouble.lean`.
Status: [done].

**Function relation `A -> B`.**
Wadler: `(f,f') in A -> B` iff for all
`(x,x') in A`, `(f x, f' x') in B`.
Generalization: `pshArrowRel R₁ R₂` using the
internal hom of the presheaf category.
Lean: `pshArrowRel`.
File: `PshRelDouble.lean`.
Status: [done].

**Exponential edge.**
The edge `(FunctorHom A B, FunctorHom A' B',
pshArrowRel R_A R_B)` with the exponential
adjunction in `PshRelEdge C`.
Lean: `pshRelEdgeExp`, exponential adjunction.
File: `PshRelEdgeExp.lean`.
Status: [done].

**Universal quantification `forall X. F(X)`.**
Wadler: `(g,g') in forall X. F(X)` iff for all
relations `A`, `(g_A, g'_{A'}) in F(A)`.

Generalization: given a covariant endofunctor
`G : PSh(C) => PSh(C)`, its Barr lift
`pshBarrLiftEdgeFunctor G` is an endofunctor on
`PshRelEdge C`.  The universal type `∀X. G(X)` is
the limit of this endofunctor (treated as a
diagram `PshRelEdge C => PshRelEdge C`).

This limit has two components:

- **At identity edges** `(P, P, pshRelId P)`:
  `pshBarrLiftRel_id` gives
  `pshBarrLiftRel G (pshRelId P) = pshRelId (G P)`,
  so the limit projects to `G(P)` at each `P`.
  Thus the presheaf-level data is the limit
  `lim_P G(P)` in `PSh(C)` — an element of each
  `G(P)`, natural in `P`.

- **At general edges** `(P, Q, R)`: the limit
  condition requires the chosen elements to be
  related under `pshBarrLiftRel G R` for every
  relation `R`.  This is exactly Wadler's
  parametricity condition: "for all relations `A`,
  the two values are related under `F(A)`."

`ParametricCone G` is a `Limits.Cone G`
(mathlib) whose vertex is the terminal edge.
The cone's natural transformation `π` gives,
for each edge `e`, a morphism `⊤ ⟶ G(e)`
satisfying the cone condition (mathlib's
`Cone.w`).  `ParametricCone.mk'` builds one
from an explicit family and proof.  For
`G = pshBarrLiftEdgeFunctor H`, this is
the limit picture above.

`PshRelEdge C` has all small limits and colimits
(`pshRelEdgeHasLimitsOfSize`,
`pshRelEdgeHasColimitsOfSize`), inherited from
the ambient presheaf topos via the reflective
embedding: limits are created by the inclusion
(right adjoint), colimits by applying the
separation reflector to colimits in
`[WalkingSpan, PSh(C)]`.

Lean: `ParametricCone`,
`ParametricCone.mk'`,
`pshBarrLiftEdgeFunctor`,
`pshRelEdgeHasLimitsOfSize`,
`pshRelEdgeHasColimitsOfSize`.
Files: `PshRelEdgeGraphRestriction.lean`,
`PshRelDouble.lean`, `PshRelEdgeInclusion.lean`.

**Existential quantification `exists X. F(X)`.**
Wadler does not treat existential types, but they
arise naturally as the dual.  Given
`G : PSh(C) => PSh(C)`, the existential type
`∃X. G(X)` is the colimit of
`pshBarrLiftEdgeFunctor G` in `PshRelEdge C`.

- **At identity edges**: the colimit gives the
  colimit `colim_P G(P)` in `PSh(C)` — the
  "there exists a presheaf `P` and an element of
  `G(P)`" data.
- **At general edges**: the colimit condition
  requires that two elements are identified when
  they are related by some `pshBarrLiftRel G R`.
  This is the dual parametricity condition: an
  existential package is parametric when its
  witnesses can be connected by a relation.

`PshRelEdge C` has all small colimits
(`pshRelEdgeHasColimitsOfSize`), so these
existential types exist.
Status: [done].

**Identity extension lemma.**
Wadler (Section 2, implicit): the relational
interpretation of a type constructor applied to
the identity relation yields the identity
relation. (`F(I_A) = I_{F(A)}`)
Generalization: `pshRelIdentFunctor` preserves
products, coproducts, exponentials, equalizers,
coequalizers, terminal, and initial objects.
Lean: `pshRelIdentFunctor_preserves_exp`,
`pshRelIdentFunctor_preserves_prod`, etc.
File: `PshRelEdgeIdentPreservation.lean`.
Status: [done].

**Contravariant Barr extension.**
Not explicit in Wadler (the function-space
relation handles contravariance), but needed for
the general profunctor case.
Generalization: `pshContraBarrLiftRel F R` for
`F : PSh(C)^op => PSh(C)`.
Lean: `pshContraBarrLiftRel`,
`pshContraBarrLiftEdgeFunctor`.
File: `PshRelDouble.lean`.
Status: [done].

**Profunctor Barr extension.**
Wadler: the function-space relation `A -> B` is
the combined contravariant-covariant case.
Generalization: `pshProfBarrLiftRel G R` for
`G : PSh(C)^op x PSh(C) => PSh(C)`, with identity
preservation `pshProfBarrLiftRel_id`.
Lean: `pshProfBarrLiftRel`,
`pshProfBarrLiftRel_id`.
File: `PshRelDouble.lean`.
Status: [done].

**Parametricity proposition.**
Wadler: if `t : T` then `(t,t) in [[T]]`.
Generalization: every natural transformation
determines a parametric section (the condition is
tautological in `PshRelEdge C`).
Lean: `Cone.π` (mathlib).
File: `PshRelEdgeGraphRestriction.lean`.
Status: [done].

**Full parametricity (all relations).**
Wadler: the relational interpretation quantifies
over all relations, not just graphs of functions.
Generalization:
`natTrans_pshRelRelated_barrLiftRel` shows
naturality of `σ : G ⟶ G` implies relatedness at
every Barr-lifted relation (not just graphs).
`natTransToBarrLiftEdgeEndo` lifts `σ` to an
endomorphism of the full Barr lift edge functor.
Lean: `natTrans_pshRelRelated_barrLiftRel`,
`natTransToBarrLiftEdgeEndo`.
Files: `PshRelDouble.lean`,
`PshRelEdgeGraphRestriction.lean`.
Status: [done].

### Section 3: Parametricity applied

**3.1 Rearrangements.**
Wadler: for `r : forall X. X* -> X*`,
`a* . r_A = r_{A'} . a*`.
Generalization: `natTransToBarrMap` /
`barrMapToNatTrans` establish a bijection between
endofunctor natural transformations `F ⟶ G` and
natural transformations
`pshBarrEmbedding F ⟶ pshBarrEmbedding G`.
The endomorphism case `F = G` gives the
rearrangement theorem.
`pshBarrEmbeddingFunctor` packages this as a
fully faithful functor from endofunctors on
`PSh(C)` to functors `PSh(C) ⥤ PshRelEdge C`.
Lean: `natTransToBarrMap`, `barrMapToNatTrans`,
`pshBarrEmbeddingFunctor`,
`pshBarrEmbeddingFunctor_fullyFaithful`,
`natTransToBarrEndo` (endomorphism
specialization).
File: `PshRelEdgeGraphRestriction.lean`.
Task: W2.
Status: [done].

**3.2 Fold (catamorphism).**
Wadler: if `(a,b)` form a homomorphism of
algebras, then
`b . fold(oplus) u = fold(otimes) u' . a*`.
Generalization: `foldFreeTheorem_graph` shows the
catamorphism of an initial `F`-algebra commutes
with algebra homomorphisms.
`foldFreeTheorem_barrLift_graph` takes the
hypothesis in `pshRelRelated` form.
Lean: `foldFreeTheorem_graph`,
`foldFreeTheorem_pshRelRelated_graph`,
`foldFreeTheorem_barrLift_graph`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W4.
Status: [done].

**3.3 Sort/nub (conditional free theorems).**
Wadler: `sort` commutes with monotone maps; `nub`
commutes with injective maps.
Generalization: `conditional_freeTheorem_graph`
shows that a family natural on a subclass of
morphisms (determined by a predicate `P`) is
related at Barr-lifted graphs of `P`-morphisms.
`conditional_edge_freeTheorem` generalizes to
edge predicates.
Lean: `conditional_freeTheorem_graph`,
`conditional_graph_implies_nat`,
`conditional_edge_freeTheorem`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W5.
Status: [done].

**3.4 Polymorphic equality impossibility.**
Wadler: polymorphic equality
`(=) : forall X. X -> X -> Bool` cannot be defined
in pure System F, because parametricity forces it
to be constant.
Generalization: `parametric_constant` shows any
graph-natural family
`σ : forall P c, P.obj c -> P.obj c -> β`
satisfies `σ P c a b = σ P c a a`.
`no_parametric_equality` specializes to Bool.
Lean: `parametric_constant`,
`parametric_constant_value`,
`no_parametric_equality`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W7.
Status: [done].

**3.5 Map decomposition.**
Wadler: every function of type
`forall X Y. (X -> Y) -> X* -> Y*` is `map`
composed with a rearranging function.
Generalization: `MapFamily G` is a natural
transformation from `Arrow.leftFunc ⋙ G` to
`Arrow.rightFunc ⋙ G`.
`mapFamilyDecompLeft`/`mapFamilyDecompRight`
derive `m(α) = m(id) ≫ G.map α` and
`m(α) = G.map α ≫ m(id)`.
`mapFamilyToNatTrans`/`natTransToMapFamily` with
roundtrips give the bijection.
Lean: `MapFamily`, `mapFamilyDecompLeft`,
`mapFamilyDecompRight`, `mapFamilyToNatTrans`,
`natTransToMapFamily`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W3.
Status: [done].

**3.6 Fold decomposition.**
Wadler: every function of type
`forall X Y. (X -> Y -> Y) -> Y -> X* -> Y` can
be expressed as `fold` composed with a
rearranging function.
Generalization: covered by the fold free theorem
framework (W4). The decomposition follows from
the catamorphism's universal property.
Task: W4.
Status: [done] (via general framework).

**3.7 Filter.**
Wadler: `filter` commutes with maps that preserve
the predicate.
Generalization: covered by the conditional free
theorem framework (W5-W6), with `P` = "predicate-
preserving".
Task: W5-W6.
Status: [done] (via general framework).

**3.8 Yoneda isomorphism.**
Wadler: `forall X. (A -> X) -> X` is isomorphic
to `A`.
Generalization: `yoneda_via_parametricity` shows a
graph-natural family
`σ : forall P, (A ⟶ P) -> forall c, P.obj c`
satisfies `σ Q g c = g.app c (σ A (id_A) c)`,
hence is determined by `σ A (id_A)`.
Lean: `yoneda_via_parametricity`,
`yoneda_embedding_natural`,
`yoneda_parametricity_inverse`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W8.
Status: [done].

### Sections 4-5: Syntax and semantics

These sections define the polymorphic lambda
calculus (System F) and its frame model semantics.
They provide the specific model in which Wadler
proves the parametricity theorem.  Our
generalization replaces the syntactic and semantic
framework entirely with categorical structure.

**Section 4: Polymorphic lambda calculus.**
Wadler: types are `T ::= X | T -> U | forall X. T`;
terms include variables, lambda abstraction,
application, type abstraction `ΛX. t`, and type
application `t_U`.  Typing rules are given in
Figure 2.
Generalization: we do not replicate the syntax.
Our type constructors (product, coproduct,
exponential, Barr lift, arrow relation) operate
directly on objects and morphisms of `PSh(C)` and
`PshRelEdge C`.  The analogue of type abstraction
is a functor `F : PSh(C) -> PSh(C)` or
`F : PshRelEdge C -> PshRelEdge C`; the analogue
of type application is evaluation of `F` at a
particular presheaf or edge.
Status: [done] (subsumed by categorical structure).

**Section 5: Frame model semantics.**
Wadler: a frame consists of:

- a universe **U** of type values;
- `D_A` (values of type A) for each `A in U`;
- `[U -> U]` (functions from U to U);
- isomorphisms `φ/ψ` between `D_{A->B}` and
  `[D_A -> D_B]`;
- isomorphisms `Φ/Ψ` between `D_{forall F}` and
  `[forall A : U. D_{F(A)}]`.
Type environments map type variables to elements
of **U**.  `[[T]]Ā` is the type semantics; `[[t]]Ā σ̄`
is the term semantics.

Generalization:

| Wadler                    | Ours                                |
|---------------------------|-------------------------------------|
| **U** (type universe)     | `PSh(C)` (presheaf cat.)            |
| `D_A` (values)            | sections of presheaf `P`            |
| `A -> B`                  | `FunctorHom A B`                    |
| `forall X. F(X)`          | limit of `pshBarrLiftEdgeFunctor G` |
| frame (U,→,∀,D,φ,ψ,Φ,Ψ)   | cartesian closed `PSh(C)`           |
| type environment `Ā`      | functor from type vars              |
| `[[T]]Ā`                  | evaluation in functor cat           |
| `[[t]]Ā σ̄`                | internal language eval              |

The cartesian closed structure of `PSh(C)`
provides the isomorphisms `φ/ψ` (exponential
adjunction) and `Φ/Ψ` (end/limit universal
property) automatically.  The soundness
proposition ("if `X̄;x̄ ⊢ t : T` then
`X̄;x̄ ⊨ t : T`") becomes a property of the
internal language of the presheaf topos.
Status: [done] (subsumed by `PSh(C)` structure;
no separate Lean formalization needed since we
work directly in the categorical framework).

### Section 6: The parametricity theorem

**Formal parametricity theorem.**
Wadler: terms in related environments have related
values (induction on type derivations).
Generalization: in `PshRelEdge C`, parametricity
for an endofunctor `G` on `PshRelEdge C` is the
existence of a `ParametricCone G` — a
`Limits.Cone G` (mathlib) whose vertex is the
terminal edge.  The cone condition (`Cone.w`)
gives naturality; `ParametricCone.mk'`
constructs a cone from an explicit family.

For covariant endofunctors: the parametricity
condition for `∀X. G(X)` is equivalent to the
section forming a cone over the diagram
`pshBarrLiftEdgeFunctor G`.  At identity edges,
`pshBarrLiftRel_id` forces source = target
projections, recovering the presheaf-level
limit; at general edges, the cone condition
encodes that the chosen elements are
`pshBarrLiftRel G R`-related for all relations
`R`.  See the "Universal quantification" entry
in Section 2 above.

Lean: `ParametricCone`, `ParametricCone.mk'`,
`Limits.Cone` / `Cone.w` (mathlib),
`pshBarrLiftEdgeFunctor`.
Files: `PshRelEdgeGraphRestriction.lean`,
`PshRelDouble.lean`.
Task: W9.
Status: [done].

### Section 7: Fixpoints

Wadler: if `fix : forall X. (X -> X) -> X` is
added, parametricity holds only under additional
conditions:
(1) each type `A` carries domain structure (CPO
with bottom element ⊥);
(2) all functions are continuous;
(3) all relations are strict: `(⊥_A, ⊥_{A'}) in A`;
(4) all relations are continuous (preserve directed
joins).
Under these restrictions,
`fix_A f = ⊔ f^i ⊥_A` satisfies parametricity,
and the free theorems hold for strict functions
`a` (those with `a ⊥ = ⊥`).

Generalization: our constructive framework avoids
domain theory entirely.  The analogue of fixpoints
in `PSh(C)` is initial algebras and terminal
coalgebras of endofunctors:

- Accessible/finitary endofunctors on `PSh(C)` have
  initial algebras by Adamek's theorem (iterating
  the empty copresheaf through the functor).
- The Barr extension of such a functor preserves
  the initial algebra structure (the extension
  preserves the colimits used in the construction).
- Parametricity for initial-algebra-based recursion
  (catamorphisms) is exactly the fold free theorem
  (W4: `foldFreeTheorem_graph`), which we already
  have.
- The restriction to "strict" functions in Wadler
  corresponds to the restriction to algebra
  homomorphisms in the catamorphism setting.

The main difference: Wadler needs domain theory
because general recursion (fixpoint of an arbitrary
endofunction) is not structurally recursive.  In
our framework, recursion is always structured
(catamorphism / anamorphism), so the universal
property provides the free theorem directly.
Wadler's strictness condition (`a ⊥ = ⊥`) is the
analogue of requiring that the function be an
algebra homomorphism (preserving the initial
element).

Status: [done] (the constructive analogue is
the fold free theorem W4; no domain theory needed).

### Open: General parametric transformation

**Parametric transformation (general notion).**
Wadler: if `t : forall X. F(X) -> G(X)` then for
all relations `A`, `(t_A, t_{A'}) in F(A) -> G(A)`.

When the type-formers `F` and `G` are covariant
endofunctors, this is standard naturality and is
fully handled by `pshBarrEmbeddingFunctor`.

When the type involves mixed variance — e.g.
`∀X. (X → X) → (X → X)` where `X ↦ X → X` is
a profunctor — one might seek a notion of
"morphism between profunctors" (dinatural,
paranatural, etc.).  But as discussed in "Why
relations replace profunctors" above, profunctors
are the wrong objects for this purpose: they
capture one level of mixed variance, but types
with nested arrows (like `((X → X) → X) → X`)
require deeper structure that profunctors discard.

The right approach uses relations directly.
`TypeExpr.fullRelInterp` computes the correct
relational interpretation by structural induction
on a type expression, composing `arrowRel` and
`graphRel` at each level.  This works for any
type decomposable as a `TypeExpr`, but it is a
syntactic construction (it depends on the
expression tree, not just the resulting type).

**The limit/colimit picture.**
For covariant endofunctors, universal and
existential types are limits and colimits of
`pshBarrLiftEdgeFunctor G` in `PshRelEdge C`
(see "Universal quantification" and "Existential
quantification" above).  A parametric
transformation `t : ∀X. F(X) → G(X)` between
covariant endofunctors is then a morphism
between the limits of
`pshBarrLiftEdgeFunctor F` and
`pshBarrLiftEdgeFunctor G`.  Since
`pshBarrLiftEdgeNatTrans σ` gives a natural
transformation between these endofunctors for
each `σ : F ⟶ G`, it induces a morphism
between the limits automatically.

The open question is extending this picture to
mixed-variance type-formers.  For types built
from arrows, the relational interpretation
uses `arrowRel` rather than Barr lifting.
A general definition of "parametric
transformation" should be a property of a
family of presheaf morphisms, defined in terms
of `PshRelEdge C`.

Candidates:

- Natural transformations between endofunctors on
  `PshRelEdge C`.  Each type-former lifts to an
  edge endofunctor via `pshBarrLiftEdgeFunctor`
  (covariant case) or via `arrowRel`-based
  constructions (mixed-variance case); a
  parametric morphism would be a natural
  transformation between such lifted endofunctors.
- Limits / sections of diagrams in `PshRelEdge C`.
  The quasitopos structure provides all finite
  limits; parametricity of a family could be
  expressed as the family forming a cone or section
  of a suitable diagram in PshRelEdge.

A correct definition would satisfy:

(a) `arrowRel` / `pshArrowRel` preserves it
  (function type formation preserves parametricity);
(b) `pshBarrLiftRel` preserves it at covariant
  leaves;
(c) when source/target are built from a `TypeExpr`,
  it coincides with `fullRelInterp`;
(d) it does _not_ reduce to paranaturality in
  general (since paranaturality is strictly stronger
  than parametricity for types with deep arrow
  nesting).

Note: `profBarrLiftRel` preservation (Barr lift on
profunctors) equals paranaturality at graph
relations (`profBarrLiftRel_graph_iff_diagCompat`),
which is too strong.  This is another manifestation
of profunctors being the wrong objects: their Barr
lift captures factorizable endomorphism pairs
rather than all commuting pairs.

Status: [open].

**Equivalence of functors on relations.**
Wadler/blog: "Relations specialized to functions
become bifunctors." When a relation is the graph
of a function, the relational interpretation of a
type constructor reduces to its bifunctor action.
The blog conjectures a deeper equivalence: "all
Haskell laws are category laws in different
categories."
Partial answer: `pshBarrEmbeddingFunctor` is a
fully faithful functor from endofunctors on
`PSh(C)` to functors `PSh(C) ⥤ PshRelEdge C`.
This means the Barr embedding preserves and
reflects the structure of endofunctor natural
transformations (i.e. Wadler's parametrically
polymorphic functions).  Distinct endofunctor
natural transformations yield distinct natural
transformations between Barr embeddings, and every
natural transformation between Barr embeddings
arises from an endofunctor natural transformation.
Lean: `pshBarrEmbeddingFunctor`,
`pshBarrEmbeddingFunctor_fullyFaithful`.
File: `PshRelEdgeGraphRestriction.lean`.
Remaining open: what is the essential image of
`pshBarrEmbeddingFunctor`?  Not every functor
`PSh(C) ⥤ PshRelEdge C` arises as a Barr
embedding.  The characterization of the essential
image would complete the analogue of Wadler's
observation.
Status: [partial] (full faithfulness proved;
essential image characterization open).

### Blog post: "Review of Theorems for Free"

**Relations specialized to functions become
bifunctors.**
Blog: when relation `A` is the graph of a function
`a`, the product relation `A x B` becomes
`bimap a b`, the list relation `A*` becomes `map a`.
Generalization: `pshBarrLiftRel_graph` shows the
Barr extension of a graph relation equals the
graph of the mapped morphism. Graph restriction
`graphRestrictionFunctor` recovers the arrow
endofunctor.
Lean: `pshBarrLiftRel_graph`,
`pshBarrLiftEdge_graphNatIso`,
`graphRestrictionFunctor`.
File: `PshRelEdgeGraphRestriction.lean`.
Tasks: W1, G1-G3.
Status: [done].

**Function relation = naturality square.**
Blog: `(f,f') in A -> B` specialized to function
graphs gives `f' . g = h . f`.
Generalization:
`pshBarrLiftRel_graph_related_iff` shows
relatedness at graph edges is equivalent to the
naturality/commutativity square.
Lean: `pshBarrLiftRel_graph_related_iff`,
`pshBarrLiftRel_graph_related_hetero_iff`.
File: `PshRelEdgeGraphRestriction.lean`.
Task: W1.
Status: [done].

**"All Haskell laws are category laws."**
Blog conjecture: all Haskell laws are category
laws in different categories.
Generalization: `PshRelEdge C` is a quasitopos
with a reflective embedding into the presheaf
topos `[WalkingSpan, PSh(C)]`, and parametricity
conditions correspond to naturality in this
topos. The reflective embedding and exponential
ideal property formalize the sense in which
relational reasoning reduces to categorical
reasoning.
Lean: `pshRelEdgeInclusionFunctor`,
`pshRelEdgeSepAdjunction`,
`ExponentialIdeal`.
File: `PshRelEdgeInclusion.lean`.
Status: [done].

### Figure 1: Examples of theorems from types

All Figure 1 entries share the same categorical
content: they are naturality conditions for
natural transformations between composed
endofunctors on `PSh(C)`.  The varying hypotheses
(monotonicity for sort, predicate-preservation for
filter, algebra-homomorphism for fold) arise from
naturality restricted to subcategories of
morphisms.

**head, tail, (++), concat (list operations).**
Wadler: `a . head_A = head_{A'} . a*`, etc.
Generalization: instances of the rearrangement
theorem (W2) for the list endofunctor.
Status: [done] (via general framework).

**fst, snd (product projections).**
Wadler: `a . fst_{AB} = fst_{A'B'} . (a x b)`.
Generalization: instances of naturality of
product projections in `PshRelEdge C`.
Status: [done] (via limits in PshRelEdgeLimits).

**zip.**
Wadler: `(a x b)* . zip_{AB} = zip_{A'B'} .
(a* x b*)`.
Generalization: zip is a natural transformation
`G x H -> G_x_H` where `G, H` are endofunctors
(e.g. list) and `G_x_H` is their pointwise
product composed with list.  This is an instance
of the rearrangement theorem applied to a natural
transformation between composed endofunctors.
Not individually formalized, but follows from the
general framework: any such natural transformation
automatically satisfies the commutativity square
by `natTransToBarrEndo`.
Status: [open] (not formalized as a specific
instance, but follows from the general framework).

**filter, sort, fold.**
See Sections 3.2, 3.3, 3.7 above.

**I (identity), K (constant).**
Wadler: `a . I_A = I_{A'} . a`,
`a (K_{AB} x y) = K_{A'B'} (a x) (b y)`.
Generalization: instances of naturality of the
identity and constant natural transformations.
Status: [done] (via general framework; `I` is
literally `id`, `K` is the projection from the
product).

### Infrastructure (beyond Wadler)

**Double category of presheaf relations.**
`pshRelId`, `pshRelComp`, `pshRelGraph`,
`pshRelDagger`, `pshRelRelated`,
`pshRelGraphFunctor`, and all double-category
laws.
File: `PshRelDouble.lean`.
Status: [done].

**Yoneda relation double category.**
`YonedaRelDouble` with identity, composition,
graph functor, double-category laws, and
terminal specialization.
File: `YonedaRelDouble.lean`.
Status: [done].

**PshRelEdge category structure.**
Named instance `pshRelEdgeCategory`. Terminal,
initial, binary products, binary coproducts,
equalizers, coequalizers.
File: `PshRelEdgeLimits.lean`.
Status: [done].

**Subobject classifier.**
`pshRelEdgeSOClassifier = (Omega, Omega, full)`.
Classifying morphism, uniqueness, and pullback
characterization.
File: `PshRelEdgeSOClassifier.lean`.
Status: [done].

**Reflective embedding into presheaf topos.**
Fully faithful `pshRelEdgeInclusionFunctor`,
separation reflector `pshRelEdgeSepFunctor`,
adjunction, preservation of finite products,
exponential ideal, preservation of coproducts.
File: `PshRelEdgeInclusion.lean`.
Status: [done].

**Over Omega factorization.**
`pshRelIdentFunctor = pshTruthLabelFunctor >>
pshOverOmegaEdgeFunctor`.
File: `PshRelEdgeOverOmega.lean`.
Status: [done].

**Span bicategory.**
`pshSpanBicategory` with all 12 coherence axioms.
File: `PshSpanBicategory.lean`.
Status: [done].

**Barr embedding functoriality.**
`pshBarrEmbeddingFunctor` is a fully faithful
functor from endofunctors on `PSh(C)` to
functors `PSh(C) ⥤ PshRelEdge C`.  Endofunctor
natural transformations `σ : F ⟶ G` biject with
natural transformations between Barr embeddings.
Lean: `pshBarrEmbeddingFunctor`,
`pshBarrEmbeddingFunctor_fullyFaithful`,
`natTransToBarrMap`, `barrMapToNatTrans`.
File: `PshRelEdgeGraphRestriction.lean`.
Status: [done].

### Open directions

**Relation composition in PshRelEdge.**
When does `F(R_1 ; R_2) ≅ F(R_1) ;_F F(R_2)`?
Answer: when `G` preserves pullbacks (Barr's theorem).
This holds for right adjoints (all limits preserved)
and for left-adjoint type-formers in a presheaf topos
(finite limits preserved by cartesian closure).
Task: R1 [done], A1-A7 [done].
Status: [done].

**Type-formers as adjoint functors.**
Right adjoint type-formers (internal hom, dependent
products) preserve all limits, hence pullbacks; left
adjoint type-formers (products, coproducts, dependent
sums) preserve pullbacks in a presheaf topos.  Both
cases yield Barr extensions that preserve composition,
giving double functors on `PshRelDouble`.  Adjunctions
lift to double adjunctions.
Tasks: A1-A7.
Status: [done].

**Paranatural vs parametric in PshRelEdge.**
Edge-level example of parametric-but-not-
paranatural morphism, generalizing the type-level
divergence (`divApplyId`).
C1 [done]: `profBarrLiftRel_graph_iff_diagCompat`
(generic, in `RelDouble.lean`) shows that Barr lift
at graph relations is equivalent to DiagCompat
(paranaturality). `divApplyId_not_profBarrLift_preserving`
(in `ParanaturalTopos.lean`) shows `divApplyId` does
not preserve profBarrLiftRel at graphs.
C2 [done]: the gap is the gap between factorizable
endomorphism pairs (∃ r, h=r∘f ∧ k=f∘r) and
commuting pairs (f∘h=k∘f). Paranaturality tests
factorizable pairs; parametricity tests all
commuting pairs. Concrete non-factorizable witness:
(const true, id, id).
Tasks: C1 [done], C2 [done].

**Universal/existential types as limits/colimits.**
For covariant `G`, `∀X. G(X)` is the limit and
`∃X. G(X)` is the colimit of
`pshBarrLiftEdgeFunctor G` in `PshRelEdge C`.
`ParametricCone G` is a `Limits.Cone G` with
vertex the terminal edge; it corresponds to a
global element of `lim G` via
`ParametricCone G ≅ Hom(⊤, lim G)`.
`pshRelEdgeHasLimitsOfSize` and
`pshRelEdgeHasColimitsOfSize` guarantee
existence (via the reflective embedding into
`[WalkingSpan, PSh(C)]`).

The limit `lim G` as an edge `(L_src, L_tgt,
L_rel)` carries three pieces of data:

- `L_src ≅ lim_P H(P)`: the presheaf of
  "left-side parametric families"
- `L_tgt ≅ lim_P H(P)`: the presheaf of
  "right-side parametric families"
- `L_rel`: the relation on the universal type,
  which is Wadler's relatedness on `∀X. F(X)` —
  two families `g, g'` are related iff for every
  edge `(P, Q, R)`, the pair `(g_P, g'_Q)` is
  `pshBarrLiftRel H R`-related.

The relation on the universal type is not
defined separately; it emerges from computing
the limit in `PshRelEdge C`.

The two views of a polymorphic function
`t : ∀X. F(X) → G(X)` are equivalent:

- (a) Natural transformation `σ : F ⟶ G`
  (the "transformation" view)
- (b) Global element of
  `lim(pshBarrLiftEdgeFunctor H)` where
  `H(X) = FunctorHom(F(X), G(X))`
  (the "universal type" view)

The equivalence is the full faithfulness of
`pshBarrEmbeddingFunctor`:
`barrMapToNatTrans_natTransToBarrMap` and
`natTransToBarrMap_barrMapToNatTrans` give the
roundtrip.  The IEP
(`pshRelIdentFunctor_preserves_exp`) is the
mechanism: it ensures that at identity edges,
parametricity reduces to naturality.

Tasks: U1-U4.
Status: [done] All four completed.

- [x] **U1.** `parametricConeEquiv`: `ParametricCone G
  ≃ Hom(⊤, lim G)`.
  (`PshRelEdgeGraphRestriction.lean`)
- [x] **U2.** `limitSectionEquivPresheafSection`:
  `Hom(⊤, lim(pshBarrLiftEdgeFunctor G)) ≃
  PresheafSection G`.  Also
  `limitSectionToPresheafSection`,
  `presheafSectionToLimitSection`, roundtrips.
  (`PshRelEdgeGraphRestriction.lean`,
  section `LimitRecovery`)
- [x] **U3.** Wadler relatedness characterization.
  `parametricCone_ident_srcEqTgt` (src=tgt at
  identity edges),
  `parametricCone_wadlerRelated` (relatedness at
  all edges via cone projection),
  `presheafSection_wadlerRelated` (converse),
  `parametricCone_graph_naturality` (graph edges
  specialize to naturality).
  (`PshRelEdgeGraphRestriction.lean`,
  section `WadlerRelatedness`)
- [x] **U4.** Quantification hierarchy collapse.
  `hierarchyCollapse`: `ParametricCone ≃
  PresheafSection` shows the three levels (identity
  edges, graph edges, all edges) give the same
  type of sections for covariant endofunctors.
  `hierarchyCollapseLimit`: limit-level version.
  The hierarchy becomes genuinely stratified only
  for conditional quantification
  (`conditional_freeTheorem_graph`).
  (`PshRelEdgeGraphRestriction.lean`,
  section `QuantificationHierarchy`)

**General parametricity notion in PshRelEdge.**
Define parametric transformation for arbitrary
type-formers (not just covariant endofunctors)
purely in PshRelEdge terms.  Profunctors are the
wrong objects for this (see "Why relations replace
profunctors" above); the definition must use
presheaf relations directly.  For covariant
endofunctors, the answer is: a morphism between
limits of Barr-lifted edge endofunctors.  The
open question is extending this to mixed-variance
type-formers, where `arrowRel` replaces Barr
lifting at each arrow type.
Must be preserved by arrowRel and coincide with
`TypeExpr.fullRelInterp` on decomposable types,
while being strictly weaker than paranaturality
for types with nested arrow structure.
See "Open: General parametric transformation" in
the Wadler correspondence section above.
Status: [open].

**Internal parametricity statement.**
Formulate "every element of every type is
parametric" in the internal language of
`[WalkingSpan, PSh(C)]`.
Task: I1.
Status: [open].

**Sep_J equivalence.**
`PshRelEdge C ≅ Sep_J(C x I^op)`.
Task: S1.
Status: [open].

**Yoneda extension of sections.**
Extend sections from representable presheaves to
all presheaves via the density theorem.
Task: S2.
Status: [open].
