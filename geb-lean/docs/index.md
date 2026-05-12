# Topological Index of GebLean Workstreams

A reader-oriented map of the major mathematical content
implemented in `GebLean/`. Each entry lists the workstream's
name, the source-tree paths it occupies, the central
mathematical concepts it formalises, the dependencies it has on
other entries below, and (where applicable) pointers into
`docs/research/` and `docs/superpowers/specs/`. The index is
adequate rather than exhaustive: every major area is reachable,
and gaps are filled in as workstreams complete.

## Quivers, semicategories, acyclic categories

- **Source-tree paths**: `GebLean/FiniteQuiver.lean`,
  `GebLean/Semicategory.lean`,
  `GebLean/AcyclicQuiver.lean`,
  `GebLean/AcyclicCat.lean`,
  `GebLean/AcyclicPresentation.lean`,
  `GebLean/CofreeCategory.lean`.
- **Central concepts**: directed graphs as quivers, free and
  cofree categories on a quiver, semicategories (categories
  without identities), acyclic quivers and the categories they
  freely generate, presentations of categories by generators
  and relations.
- **Dependencies**: foundational. Used by the
  [category-judgment encodings](#category-judgment-encodings)
  layer.

## Category-judgment encodings

- **Source-tree paths**: `GebLean/CategoryJudgments.lean`,
  `GebLean/DepCategoryJudgments.lean`,
  `GebLean/CatJudgmentAdjunction.lean`,
  `GebLean/DepCategoryAdjunction.lean`,
  `GebLean/DepCategoryCat.lean`,
  `GebLean/PLang/CatJudgment.lean`,
  `GebLean/PLang/CatJudgGrothendieck.lean`,
  `GebLean/PLang/CatJudgCoprAdjunction.lean`,
  `GebLean/PLang/CatJudgGrAdjunction.lean`,
  `GebLean/Utilities/Category.lean`,
  `GebLean/Utilities/OverCategoryEquiv.lean`,
  `docs/novelty-analysis.md`.
- **Central concepts**: judgment-style presentations of
  categories and dependent categories, the equivalence between
  judgmental and structural presentations, adjunctions
  relating coproduct and Grothendieck constructions on the
  judgmental side, the analysis of 2-categorical structure
  transported across the L ⊣ Φ adjunction, preservation of
  binary products by the L functor, the L ⊣ Φ adjunction
  between categories and copresheaves on `CategoryJudgments`
  with reflective right adjoint and fully faithful Φ.
- **Dependencies**:
  [quivers, semicategories, acyclic categories](#quivers-semicategories-acyclic-categories)
  for the underlying quiver layer.

## Polynomial / W- / M-types and PFunctors

- **Source-tree paths**: `GebLean/BarResolution.lean`,
  `GebLean/CopresheafCoverComonad.lean`,
  `GebLean/LawvereBT.lean`,
  `GebLean/LawvereBTInterp.lean`,
  `GebLean/LawvereBTQuot.lean`,
  `GebLean/LawvereBTEqCompletion.lean`,
  `GebLean/EqualizerCompletion.lean`,
  `GebLean/EqualizerCompletionLimits.lean`,
  `GebLean/EqualizerCompletionPBTO.lean`,
  `GebLean/FreeCoequalizerCompletion.lean`,
  `GebLean/Polynomial.lean`,
  `GebLean/PolyAlg.lean`,
  `GebLean/PolyAlgUMorph.lean`,
  `GebLean/PolyAlgColimits.lean`,
  `GebLean/PolyAdjunctions.lean`,
  `GebLean/PolyCover.lean`,
  `GebLean/PolyDistributiveLaw.lean`,
  `GebLean/PolyFilteredColimits.lean`,
  `GebLean/PolyGSOS.lean`,
  `GebLean/PolyLimits.lean`,
  `GebLean/PolyPresentation.lean`,
  `GebLean/PolyPresentationEquiv.lean`,
  `GebLean/PolyTwCoprType.lean`,
  `GebLean/PolyUMorph.lean`,
  `GebLean/ParamPoly.lean`,
  `GebLean/ParanatAlg.lean`,
  `GebLean/Paranatural.lean`,
  `GebLean/Utilities/PolyCombinators.lean`.
- **Central concepts**: polynomial endofunctors and their
  categories of algebras, universal-morphism characterisations
  including arbitrary-indexed products and coproducts, binary
  equalizers and coequalizers, exponential objects, and left
  Kan extensions for polynomial functors between slice
  categories, regular projective covers of presheaves and
  copresheaves by coproducts of representables yielding
  enough projectives,
  presentations and presentation-equivalences, distributive
  laws and GSOS rules with the lifted operational monad,
  paranatural transformations and the
  paranatural topos, polynomial combinator libraries used as
  computational scaffolding, the generic comonad bar
  resolution and its instantiation at the copresheaf-cover
  comonad to resolve a copresheaf by representables, the
  Lawvere theory of parameterized binary tree objects with
  faithful universe-polymorphic interpretation functor to
  `Type`, the cofree category of a polynomial endofunctor with its
  comonoid structure, the equivalence between polynomial
  coalgebras and copresheaves on that cofree category, the
  Bunge-Carboni free equalizer completion of a category with
  finite products applied to `LawvereBTQuotCat` (yielding
  `LawvereBTLexCat` with finite limits), and the free binary
  coequalizer completion via parallel-pair diagrams.
- **Dependencies**:
  [quivers, semicategories, acyclic categories](#quivers-semicategories-acyclic-categories)
  for underlying graph data; later entries
  ([profunctors and end machinery](#profunctors-and-end-machinery),
  [tree calculus phase 2](#tree-calculus-phase-2))
  build on this layer.

## Profunctors and end machinery

- **Source-tree paths**: `GebLean/ComprehensiveFactorization.lean`,
  `GebLean/ComprehensiveWeighted.lean`,
  `GebLean/Factorization.lean`,
  `GebLean/HexagonCat.lean`,
  `GebLean/ProfAlg.lean`,
  `GebLean/MendlerLambekEndPower.lean`,
  `GebLean/MendlerLambekPresheaf.lean`,
  `GebLean/Paranatural.lean`,
  `GebLean/RestrictedCoendAsColimit.lean`,
  `GebLean/ParanatAlg.lean`,
  `GebLean/Weighted.lean`,
  `GebLean/WeightedAlg.lean`,
  `GebLean/Utilities/Profunctors.lean`,
  `GebLean/Utilities/ConnectedComponents.lean`,
  `GebLean/Utilities/EndsAndCoends.lean`,
  `GebLean/Utilities/PowersAndCopowers.lean`,
  `GebLean/Utilities/TwArrPresheaf.lean`,
  `GebLean/Utilities/TwistedArrow.lean`.
- **Central concepts**: profunctors as functors `Cᵒᵖ × C ⥤ D`,
  their two left and right actions, the hexagon diagram for
  dialgebra-of-profunctor data, ends and coends presented as
  limits and colimits over the twisted-arrow category,
  Mendler-Lambek-style end powers, restricted coends, the
  identification of structural ends of `AlgProf G` with
  initial-algebra carriers via sections of the forgetful
  functor, weight pullback and diagram postcomposition
  bifunctoriality of weighted (co)wedges, the obstruction
  to terminality transfer across non-full weight-comparison
  functors, the Street-Walters comprehensive factorization
  of a functor through a discrete (op)fibration with the
  comprehensive (co)presheaf as a pointwise left Kan
  extension, the characterisation of paranatural
  transformations as ordinary natural transformations into a
  weighted limit, and the decorated factorisation category
  with `decFactFunctor : TwistedArrow C ⥤ Cat` generalising
  `factorisationFunctor` and the total-decorated Grothendieck
  equivalence, the reduction of restricted and strong-restricted
  (co)wedges to standard (co)wedges over power and copower
  profunctors with terminal / initial cases identified as
  structural ends and coends.
- **Dependencies**:
  [polynomial / W- / M-types and PFunctors](#polynomial--w---m-types-and-pfunctors)
  for the polynomial side of profunctorial constructions.

## Internal-presheaf Grothendieck equivalence

- **Source-tree paths**: `GebLean/PshInternalCat.lean`,
  `GebLean/PshInternalExternalize.lean`,
  `GebLean/PshInternalPresheaf.lean`,
  `GebLean/PshInternalGrothendieck.lean`,
  `GebLean/Utilities/Grothendieck.lean`,
  `GebLean/Utilities/ConnectedGrothendieck.lean`,
  `GebLean/Utilities/Elements.lean`.
- **Central concepts**: internal categories in a presheaf
  topos, externalisation to a `Cᵒᵖ ⥤ Cat` functor, the
  comparison functor from internal-presheaves to presheaves on
  the Grothendieck construction, and the equivalence
  `PSh(C_int) ≃ PSh(Gr(ext(C_int)))`.
- **Dependencies**:
  [profunctors and end machinery](#profunctors-and-end-machinery)
  for the underlying ends used in pointwise extraction;
  [polynomial / W- / M-types and PFunctors](#polynomial--w---m-types-and-pfunctors)
  for the presheaf-PRA layer.

## PshRelEdge and edge-of-presheaf machinery

- **Source-tree paths**: `GebLean/PshRelDouble.lean`,
  `GebLean/PshRelEdgeExp.lean`,
  `GebLean/PshRelEdgeFunctionalize.lean`,
  `GebLean/PshRelEdgeGraphRestriction.lean`,
  `GebLean/PshRelEdgeIdentPreservation.lean`,
  `GebLean/PshRelEdgeInclusion.lean`,
  `GebLean/PshRelEdgeLimits.lean`,
  `GebLean/PshRelEdgeOverOmega.lean`,
  `GebLean/PshRelEdgeReflectiveChain.lean`,
  `GebLean/PshRelEdgeSOClassifier.lean`,
  `GebLean/PshRelEdgeSeparation.lean`,
  `GebLean/PshRelSpanDiagram.lean`,
  `GebLean/PshSpanBicategory.lean`,
  `GebLean/YonedaRelDouble.lean`,
  `GebLean/PshTypeExpr.lean`,
  `GebLean/Utilities/ArrowSpanAdjunction.lean`,
  `GebLean/Utilities/ReflexiveGraph.lean`,
  `GebLean/Utilities/SpanFamily.lean`.
- **Central concepts**: the edge-of-presheaf double category
  `PshRelEdge(C)`, its cartesian-closed structure on
  endofunctors, separation properties, the reflective chain
  `PSh(C) ⊣ Arr(PSh(C)) ⊣ PshRelEdge(C) ⊣ PshSpanCat`,
  the arrow-span reflective adjunction factoring the chain
  through pushouts of presheaf spans, Yoneda extensions and
  the right Kan extension presented functorially, subobject
  classifiers in the edge category, the Hermida-Reddy-Robinson
  reflexive graph category with identity-extension property
  and jointly monic span projections distinguishing parametric
  functors from merely natural ones.
- **Dependencies**:
  [profunctors and end machinery](#profunctors-and-end-machinery)
  for ends used in CCC structure;
  [internal-presheaf Grothendieck equivalence](#internal-presheaf-grothendieck-equivalence)
  shares the presheaf-of-spans setting.

## Tree calculus Phase 2

- **Source-tree paths**: `GebLean/PLang/Syntax.lean`,
  `GebLean/PLang/TreeCalcPrograms.lean`,
  `GebLean/PLang/TreeCalcPoly.lean`,
  `GebLean/PLang/TreeCalcReduction.lean`,
  `GebLean/PLang/TreeCalcMeta.lean`,
  `GebLean/PLang/BTPair.lean`,
  `GebLean/PLang/IndexedEAT.lean`,
  `GebLean/PLang/JudgmentUniverse.lean`,
  `GebLean/PLang/TermCat.lean`,
  `GebLean/Utilities/PolyCombinators.lean`,
  `GebLean/Utilities/GSOSRule.lean`,
  `GebLean/Utilities/LambdaBialgebra.lean`,
  `docs/tree-calculus.md`.
- **Central concepts**: Barendregt-style tree calculus over a
  binary-tree base, polynomial combinators presenting the
  computation polynomial as a two-sorted construction, value
  polynomial and behaviour polynomial as reduction coalgebra,
  partial combinatory algebra structure, confluence, derived
  combinators, primitive-recursive fragment. Reference
  material from Jay's *Reflective Programs in Tree Calculus*
  (2021), Jay's *Typed Program Analysis without Encodings*
  (PEPM '25), and the associated Coq formalisation is
  consolidated in `docs/tree-calculus.md` (type system,
  programs and verified theorems, by-chapter coverage of the
  book, by-file coverage of the Coq files).
- **Dependencies**:
  [polynomial / W- / M-types and PFunctors](#polynomial--w---m-types-and-pfunctors)
  for the polynomial-functor base;
  [profunctors and end machinery](#profunctors-and-end-machinery)
  for the bialgebraic GSOS layer. Spec:
  `docs/superpowers/specs/2026-03-22-tree-calculus-phase2-design.md`.

## K^sim hierarchy and ER ↔ K^sim_2 equivalence

- **Source-tree paths**: `GebLean/LawvereKSim.lean`,
  `GebLean/LawvereKSimDCatInterp.lean`,
  `GebLean/LawvereKSimER.lean`,
  `GebLean/LawvereKSimERDirect.lean`,
  `GebLean/LawvereKSimInterp.lean`,
  `GebLean/LawvereKSimMajorization.lean`,
  `GebLean/LawvereKSimPolynomialBound.lean`,
  `GebLean/LawvereKSimQuot.lean`,
  `GebLean/LawvereER.lean`,
  `GebLean/LawvereERArith.lean`,
  `GebLean/LawvereERBound.lean`,
  `GebLean/LawvereERBoundComputable.lean`,
  `GebLean/LawvereERPolynomialBound.lean`,
  `GebLean/Utilities/KArith.lean`,
  `GebLean/Utilities/ERArith.lean`,
  `GebLean/Utilities/ERTreeArith.lean`,
  `GebLean/Utilities/ERAMajorants.lean`,
  `GebLean/Utilities/ERPackedBound.lean`,
  `GebLean/Utilities/ERSimultaneousBoundedRec.lean`,
  `GebLean/Utilities/ERTupling.lean`,
  `GebLean/Utilities/SimRec.lean`,
  `GebLean/Utilities/Tower.lean`,
  `GebLean/Utilities/Tupling.lean`,
  `GebLean/Utilities/SzudzikSeq.lean`,
  `GebLean/Utilities/KSimSzudzikSimrec.lean`,
  `GebLean/Utilities/RegisterMachine.lean`,
  `GebLean/Utilities/ComputationalComplexity.lean`,
  `GebLean/NatElegantPair.lean`.
- **Central concepts**: Tourlakis's K^sim hierarchy presented
  as a Lawvere category with simultaneous-recursion
  constructors, the elementary-recursive Lawvere category
  `LawvereERCat`, the `kToER` functor witnessing
  `K^sim_2 ⊆ ER`, polynomial bound infrastructure and
  Tourlakis A-majorants establishing tower-bounded growth,
  Szudzik-pair packing of multi-output simrec, the KArith
  library of K-side arithmetic. Citations: Tourlakis 2018,
  Wagner-Wong on URM simulation, the Wikipedia
  elementary-recursive article (see
  `docs/research/2026-04-30-ksim-polynomial-bound-references.md`,
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
  Specs:
  `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`,
  `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`,
  `docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`,
  `docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`,
  `docs/superpowers/specs/2026-05-03-step-5-ksim-to-er-functor-design.md`,
  `docs/superpowers/specs/2026-05-05-karith-design.md`.
- **Dependencies**:
  [polynomial / W- / M-types and PFunctors](#polynomial--w---m-types-and-pfunctors)
  for the Lawvere-categorical setting;
  [tree calculus phase 2](#tree-calculus-phase-2) shares the
  primitive-recursive layer via
  `GebLean/LawvereTreeER.lean` and friends.

## CSLib integration

- **Source-tree paths**: `lakefile.toml`,
  `lake-manifest.json`, `.claude/rules/lean-coding.md`,
  `CLAUDE.md` (CSLib usage discipline).
- **Central concepts**: CSLib peer dependency providing
  computability and concurrency formalisations (URM, automata,
  process calculi), pinned by tagged release tracking the
  Lean toolchain RC. Usage discipline: prefer CSLib
  typeclasses (`LTS`, `HasFresh`) over reaching into concrete
  instances; verify `#print axioms` for transitive
  `Classical.choice` exposure when constructive code depends
  on CSLib lemmas.
- **Dependencies**: orthogonal infrastructure consumed by
  [K^sim hierarchy and ER ↔ K^sim_2 equivalence](#ksim-hierarchy-and-er--ksim_2-equivalence)
  (URM simulation lemmas) and
  [tree calculus phase 2](#tree-calculus-phase-2) (LTS
  layer for reduction). Spec:
  `docs/superpowers/specs/2026-05-06-cslib-integration-design.md`.
