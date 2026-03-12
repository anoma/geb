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

- [ ] **W1. Graph restriction to naturality.** Formalize
  the reduction from parametricity to naturality when
  relations are restricted to graphs.  Given an edge
  morphism `(alpha, beta)` between identity edges
  `(P, P, Delta_P)` and `(Q, Q, Delta_Q)`, the
  relatedness square forces `alpha = beta`, recovering
  a single natural transformation.  More generally,
  for `pshBarrLiftEdgeFunctor G` applied to graph
  edges, the Barr extension of a graph is a graph
  (`pshBarrLiftRel_graph`), giving Wadler's "free
  theorem" reduction.
  Wadler: Section 3.1 (rearrangements commute with map).

- [ ] **W2. Rearrangement theorem.** For `r : ∀X. X* -> X*`
  (generalized: a section of the exponential edge
  `[(P, P, Delta_P), (G P, G P, Delta_{G P})]`), derive
  the commutativity `G(alpha) . r_P = r_Q . G(alpha)`
  for all `alpha : P => Q`.  This is the presheaf-level
  generalization of Wadler Section 3.1.

- [ ] **W3. Map decomposition.** For `m : ∀X.∀Y.(X -> Y)
  -> X* -> Y*`, derive `m(f) = f* . m(id)` (Wadler
  Section 3.5).  Generalized: sections of the
  exponential edge for the arrow-to-Barr-lift natural
  transformation type decompose as Barr lift composed
  with a rearrangement.

- [ ] **W4. Fold free theorem.** Formalize Wadler
  Section 3.2/3.6: fold commutes with algebra
  homomorphisms.  In our framework: the exponential
  edge for the fold type forces the fold parametricity
  condition.

- [ ] **W5. Sort/nub conditional free theorems.**
  Wadler Section 3.3: `sort` commutes with monotone
  maps, `nub` commutes with injective maps.  In our
  framework: the exponential edge for the sort type
  has a conditional relatedness square (the relation
  on the ordering/equality must preserve the relevant
  structure).

- [ ] **W6. Filter decomposition.** Wadler Section 3.7:
  filter commutes with maps that preserve the
  predicate.  Generalized in PshRelEdge.

- [ ] **W7. Polymorphic equality impossibility.** Wadler
  Section 3.4: no parametric inhabitant of
  `∀X. X -> X -> Bool` equals polymorphic equality.
  In PshRelEdge: the exponential edge for this type has
  no section with the equality property.

- [ ] **W8. Yoneda isomorphism.** Wadler Section 3.8:
  `∀X. (A -> X) -> X ≅ A`.  In PshRelEdge: the
  exponential edge from a constant-A edge to the
  identity edge has sections equivalent to elements of
  `A`.  The inverse direction uses parametricity (the
  section must be natural, hence determined by its
  value at `id_A`).

- [ ] **W9. Parametricity as tautology in PshRelEdge.**
  Make precise that Wadler's Parametricity Theorem
  (Section 6) is tautological in our framework: a
  section of a copresheaf on `PshRelEdge` satisfies
  parametricity by definition (it is the naturality
  condition for the section).  Formalize the comparison
  between Wadler's inductive proof and our definitional
  approach.

### Embedding endofunctors into PshRelEdge

Port the embeddings from PshRelSpanObj to PshRelEdge.

- [ ] **E1. Covariant Barr embedding into PshRelEdge.**
  Given `G : PSh(C) => PSh(C)`, construct a functor
  `PSh(C) => PshRelEdge C` sending `P` to
  `(G P, G P, pshBarrLiftRel G (pshRelId P))`.
  Show this factors through `pshRelIdentFunctor`
  composed with `pshBarrLiftEdgeFunctor G`.

- [ ] **E2. Contravariant Barr embedding into PshRelEdge.**
  Analogous for `F : PSh(C)^op => PSh(C)` using
  `pshContraBarrLiftRel`.

- [ ] **E3. Profunctor Barr embedding into PshRelEdge.**
  For `H : PSh(C)^op x PSh(C) => PSh(C)`, embed via
  `pshProfBarrLiftRel`.

- [ ] **E4. Sections of Barr-embedded edges.**
  Characterize sections of the edges from E1-E3.  For
  covariant `G`, sections should correspond to
  "parametric elements" of `G`.  At `C = Discrete PUnit`,
  these should specialize to type-level parametric
  families.

### Graph subcategory and naturality

- [ ] **G1. Graph subcategory of PshRelEdge.** Define the
  full subcategory of `PshRelEdge C` consisting of
  graph edges `(P, Q, pshRelGraph alpha)`.  Show this
  is equivalent to the arrow category `PSh(C)^{->}`.
  Copresheaves on graph edges impose only naturality,
  not full parametricity.

- [ ] **G2. Graph restriction functor.** Define the
  restriction from copresheaves on `PshRelEdge C` to
  copresheaves on the graph subcategory (G1).  Show
  this forgets parametricity data beyond naturality.

- [ ] **G3. Free theorem derivation via graphs.** For edges
  in the image of the covariant Barr embedding (E1),
  show that restricting to graph edges yields the
  naturality condition.  Uses `pshBarrLiftRel_graph`.

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
- **Free theorem**: graph restriction
  (tasks W1, G1-G3; planned)
- **Blog: relations to bifunctors**: reflective
  embedding (`PshRelEdgeInclusion.lean`)
- **Subobject classifier**: `pshRelEdgeSOClassifier`
  (`PshRelEdgeSOClassifier.lean`)
- **Over Omega factorization**:
  `pshRelIdentFunctor_factorization`
  (`PshRelEdgeOverOmega.lean`)
- **Fixpoints**: polynomial initial algebras
  (`PolyAlg*.lean`)
