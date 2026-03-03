# Workstream: Parametricity and Free Theorems

## Status

Active

## Context

Formalize Wadler's "Theorems for free!" (1989) and the Reasonably
Polymorphic blog post's observations in a generalized categorical
setting. The project has two parallel tracks:

1. **Type-level** (`ParanaturalTopos.lean`, `RelSpanDiagram.lean`,
   etc.): Wadler's original System F / `Type` setting.
2. **Presheaf-level** (`PshRelDouble.lean`, `YonedaRelDouble.lean`,
   `PshRelSpanDiagram.lean`, `PshTypeExpr.lean`): Generalization
   to presheaf categories `PSh(C)` over an arbitrary category `C`.

The goal is to recover all of Wadler's results as special cases
of the generalized presheaf theory (with `C = Discrete PUnit`),
and to prove new results that only make sense in the generalized
setting (embeddings, weight functors, Yoneda extension).

## Consolidation note

This workstream unifies the former:

- `parametric-generalization.md`
- `yoneda-rel-parametricity.md`
- `psh-parametric-free-theorems.md`
- `paranatural-topos.md` (parametricity-relevant portions)

## Completed infrastructure

### Type-level (`ParanaturalTopos.lean`)

- `TypeExpr` inductive type with `.var`, `.app F T`, `.arrow T₁ T₂`
- `TypeExpr.toProfunctor`, `.interp`, `.profMap`
- `TypeExpr.relInterp` (at graph of morphism) and
  `TypeExpr.fullRelInterp` (at arbitrary relation)
- `ParametricFamily T` structure with `app` and `parametric`
- `TypeAbs T`, `typeAbsRel`, `ParametricFamily.ofTypeAbsRel`
- `TypeExprWedge`, `TypeExprCone`, `typeExprWedgeConeIso`
- `TypeExprCat` (category of type expressions with parametric
  families as morphisms)
- `typeExprHomUnitEquiv T : (typeExprUnit ⟶ ⟨T⟩) ≃
  ParametricFamily T`
- `relSpanDiagram T`, `parametricFamilyIsLimit T`
- `relSpanDiagramFunctor : TypeExprCat ⥤ (RelSpanObj ⥤ Type 1)`
  (fully faithful)
- Divergence analysis: `divApplyId_parametric`,
  `divApplyId_not_paranatural`,
  `divParametric_not_implies_divParanatural`
- `relInterp_of_offDiag`, `relInterp_implies_wedge`,
  `ParametricFamily.wedge`
- `RelInterpComposition.lean`: arrow-free composition,
  `hasRelInterpComp`, counterexample
  `relInterp_decomp_homTypeExpr_fails`

### Type-level free theorems (Wadler correspondences)

- `homParametricEquivUnit :
  ParametricFamily homTypeExpr ≃ Unit`
- `dialgebraParametricEquivNatTrans F G :
  ParametricFamily (dialgebraTypeExpr F G) ≃ (F ⟶ G)`
- `algebraParametricEquivParanat F :
  ParametricFamily (algebraTypeExpr F) ≃
  Paranat (AlgProf F) IdProf`
- `initialAlgebraParametricEquiv F μF hμF :
  μF.a ≃ ParametricFamily (algebraTypeExpr F)`
- `dinaturalParametricEquivParanat :
  ParametricFamily dinaturalTypeExpr ≃
  Paranat HomProf HomProf`
- `dinaturalNumbersParametricEquiv :
  ℕ ≃ ParametricFamily dinaturalTypeExpr`
- `terminalCoalgebraStructuralCoendEquiv νF hνF :
  νF.V ≃ StructuralCoend (CoalgProf F)`

### Type-level embeddings (`RelSpanDiagram.lean`)

- `relSpanProfunctor`, `relSpanCollageIso`
- `graphRel`, `graphRelEquiv`, `graphRelInj`, `functorRelLift`
- `covariantEmbedding` (fully faithful)
- `contravariantEmbedding` (fully faithful)
- `profunctorEmbedding` (neither full nor faithful)
- `paranaturalProfEmbedding` (faithful)

### Presheaf-level infrastructure

- `PshRelDouble.lean`: `PshRel` (subfunctor), `pshRelId`,
  `pshRelComp`, `pshRelGraph`, `pshRelDagger`,
  `pshRelRelated`, double category structure,
  `pshBarrLift`/`pshBarrLiftSkel` (Barr extension),
  `pshArrowRel`/`pshArrowRelSkel` (arrow relation),
  `pshIhomProfMap` (internal hom profunctor)
- `YonedaRelDouble.lean`: `YonedaRel` (via representables),
  `YonedaRelCat`, double category structure,
  `terminalYonedaRelDoubleData`
- `PshRelSpanDiagram.lean`: `PshRelSpanObj C`,
  `PshRelSpanHom`, category instance,
  `PshParametricFunctor`, `PshParametricPresheaf`,
  `relSpanPshRelSpanIso :
  RelSpanObj ≅Cat PshRelSpanObj (Discrete PUnit)`,
  `parametricFunctorEquiv`, `parametricCopresheafEquiv`,
  `pshRelSpanProfunctor`, `pshRelSpanCollageIso`,
  `pshCovariantEmbedding` (fully faithful),
  `pshContravariantEmbedding` (fully faithful),
  `pshProfunctorEmbedding`,
  `pshRelSpanDiagramFunctor` (fully faithful)
- `PshTypeExpr.lean`: `PshTypeExpr` (`.var`, `.app`, `.arrow`),
  `.interp`, `.relInterp`, `.fullRelInterp`, `.toProfunctor`,
  `PshProdOver.sectionsRelated`, `pshRelSectionsRelated`,
  `PshTypeAbs`, `pshTypeAbsRel`,
  `TypeExpr.toPshTypeExpr` with interp isomorphism,
  `yonedaULiftRel`, bridge infrastructure,
  `fullRelInterp_pshRep_eq`,
  `PshTypeExprHom`, `PshTypeExprCat` (category of type
  expressions with parametric morphisms),
  `pshRelInterp_of_offDiag`, `pshRelInterp_implies_wedge`,
  `PshParametricFamily.wedge`

### Paranatural topos results (relevant here)

- `wedgeWeight H`, `wedgeWeightFunctor C`
- `wedgeWeightIdentityMap_injective`
- `assemblyFunctor`, `IsDiagDetermined`
- `lanDiagFunctor`, `lanDiagCounit`, `lanDiagUnit`
- `lanDiag_isPointwiseLan`,
  `lanDiagUnitApp_bijective`
- `IsLanDiagFixed`, `isLanDiagFixed_iff`
- `lanDiagProdComparison_surj_common_fact`
  (left-exactness fails)
- `unitEndoProf`, `prodEndoProf`,
  `endoProfBinaryFan_isLimit`
- `IsDiagDeterminedProf`, `DiagDetProf`

## Tasks

### Phase 1: Port embeddings to presheaf level

Port the embedding infrastructure from `RelSpanDiagram.lean`
(which works over `Type`) to `PshRelSpanDiagram.lean` (which
works over `PSh(C)` for arbitrary `C`).

- [x] **P1a. Presheaf collage isomorphism.** Define
  `pshRelSpanProfunctor` and prove `PshRelSpanObj C` is
  isomorphic to the collage of this profunctor, generalizing
  `relSpanCollageIso`.

- [x] **P1b. Presheaf graph/relation infrastructure.**
  Already present: `pshRelGraph` = `graphRel`,
  `pshRelGraph_ι_fst_iso` = `graphRelEquiv`,
  `pshBarrLiftSkel` = `functorRelLift`,
  `pshBarrLiftSkel_graph` = `functorRelLift_graphRel`.

- [x] **P1c. Presheaf covariant embedding.** Define
  `pshCovariantEmbedding : (PSh(C) ⥤ PSh(C)) ⥤
  PshParametricPresheaf C` and prove it fully faithful,
  generalizing `covariantEmbedding`.

- [x] **P1d. Presheaf contravariant embedding.** Define
  `pshContravariantEmbedding` and prove it fully faithful,
  generalizing `contravariantEmbedding`.

- [x] **P1e. Presheaf profunctor embedding.** Define
  `pshProfunctorEmbedding` generalizing `profunctorEmbedding`.

- [x] **P1f. Presheaf paranatural embedding.** Define
  `pshParanaturalProfEmbedding` and prove it faithful,
  generalizing `paranaturalProfEmbedding`.

- [x] **P1g. Presheaf relSpanDiagram functor.** Define
  `pshRelSpanDiagramFunctor` (analogous to
  `relSpanDiagramFunctor`) and prove it fully faithful.

### Phase 2: Complete presheaf-level parametricity bridge

- [x] **P2a. Reverse bridge: PshParametricFamily →
  ParametricFamily.** Restrict a `PshParametricFamily
  T.toPshTypeExpr` to representable presheaves to recover
  `ParametricFamily T`. Requires a `choice` parameter
  (for Barr lift witnesses in the `app`/`arrow`
  interaction); not choice-free as originally expected.
  Implemented via specialization at `op PUnit` using
  the stage-level bridge (`pointwise_bridge`).
  Includes `yonedaULiftSectionEquiv`,
  `TypeExpr.interpSectionEquiv`, `yonRelSpanEmbed`,
  `TypeExpr.fullRelInterp_bridge_rev`,
  `yonRelSpanEmbed_typeNode_sections`, and
  projection compatibility theorems. (Former F1.)

- [x] **P2b. PshParametricFamily.wedge.** Prove every
  `PshParametricFamily` satisfies the presheaf profunctor
  wedge condition. Includes presheaf-level analogues of
  `relInterp_of_offDiag` and `relInterp_implies_wedge`.
  (Former F2.)

- [x] **P2c. Complete fullRelInterp_bridge induction.**
  The `app` and `arrow` induction cases of
  `fullRelInterp_bridge` (connecting Type-level and
  presheaf-level relational interpretations) are
  complete. `relInterp_bridges` in `PshTypeExpr.lean`
  handles all three cases (`var`, `app`, `arrow`)
  in a single mutual induction.

### Phase 3: Additional Wadler free theorems

Results from Wadler's paper not yet formalized at any level.
These can be done at the Type level first, then generalized.

- [ ] **P3a. Constant-type free theorem.** Prove
  `ParametricFamily (.arrow .var (.arrow .var .var)) ≃
  Bool` (or `Fin 2`). The only inhabitants are the two
  projections. (Former F5.)

- [ ] **P3b. Yoneda/representability isomorphism.** Prove
  `∀X. (A → X) → X ≅ A` (Wadler Section 3.8). This
  requires extending `TypeExpr` to handle constant types
  (types containing a fixed type `A`), or encoding the
  result using the existing infrastructure with appropriate
  specialization.

- [ ] **P3c. Multi-variable type expressions.** Extend
  `TypeExpr` (and `PshTypeExpr`) to support multiple type
  variables (needed for fst, snd, K, fold, filter, zip,
  and other multi-variable free theorems from Wadler).

- [ ] **P3d. Product type constructor.** Add products to
  `TypeExpr` / `PshTypeExpr` (needed for K combinator,
  zip, and multi-argument results).

- [ ] **P3e. Fold/filter free theorems.** Formalize
  Wadler Sections 3.2 (fold), 3.3 (sort/nub), 3.5 (map
  decomposition), 3.6 (fold decomposition), 3.7 (filter
  decomposition). These require list-type functors,
  multi-variable type expressions, and products.

- [ ] **P3f. Polymorphic equality impossibility.** Formalize
  Wadler Section 3.4: no parametric inhabitant of
  `∀X. X → X → Bool` can be polymorphic equality.

### Phase 4: Weight functors and twisted-arrow connection

Connect parametricity to the twisted-arrow copresheaf topos
via weight functors.

- [ ] **P4a. typeExprWeight functor.** Define
  `typeExprWeight : TypeExpr → (TwistedArrow Type ⥤ Type)`
  recursively from `relInterp` data. (Former F8.)

- [ ] **P4b. Comparison with wedgeWeight.** Construct a
  natural transformation
  `typeExprWeight T → wedgeWeight (T.toProfunctor)`.
  Show it is an isomorphism for algebra/coalgebra/dinatural
  types and not for the divergence type.

- [ ] **P4c. WedgeWeightFactorization.** Formalize the
  factorization characterization of `wedgeWeight`. (Former
  W2a remaining item.)

- [ ] **P4d. Parametric weight characterization.** Find the
  weight `W` such that `ParametricFamily T` is the weighted
  end with weight `W` over `T.toProfunctor`. (Former W2b.)

- [ ] **P4e. Weight comparison.** Compare the parametric weight
  (P4d) with `wedgeWeight` and `typeExprWeight`.
  (Former W2c.)

### Phase 5: Identity Extension Property (IEP)

Characterize which functors in `PshParametricFunctor` are
"parametric" using the Identity Extension Property from
the Hermida/Reddy/Robinson paper. See
`identity-extension-property.md` for details.

- [x] **P5-IEP1. Define IEP.** Define `HasIdentityExtension`
  for `SpanFamilyData`.
- [x] **P5-IEP2. PshTypeExpr satisfies IEP.** Prove
  `pshRelSpanDiagramFunctor.obj T` satisfies IEP.
- [x] **P5-IEP3. Non-IEP counterexample.** Construct a
  functor that does not satisfy IEP.
- [x] **P5-IEP4. Embeddings satisfy IEP.** Show
  `pshCovariantEmbedding` and `pshContravariantEmbedding`
  produce IEP-satisfying functors.
- [x] **P5-IEP5. Subsumptivity.** Show `pshRelGraph` is
  full and faithful.
- [x] **P5-IEP6. Parametricity subsumes naturality.** For
  IEP functors, nat trans determined by typeNode
  components (Hermida Fact 6.6).
- [x] **P5-IEP7. Fibration structure.** Boundary functor
  `PshRelEdge C ⥤ PSh(C) × PSh(C)` is pre-fibered
  (Cartesian lifts via preimage).
- [x] **P5-IEP8. Reflexive graph category.** Define
  `ReflexiveGraphData` and instantiate for `PshRelEdge C`
  with source, target, and identity functors.

### Phase 6: Generalized theory

- [ ] **P6a. Parametric cofamilies and terminal coalgebras.**
  Define `ParametricCofamily` (dual of `ParametricFamily`)
  and prove equivalence with terminal coalgebra carrier.
  (Former F9, W3.)

- [ ] **P6b. Yoneda extension of ParametricFamily.** Extend
  a `ParametricFamily T` to all presheaves via colimit of
  representables / density theorem, yielding
  `PshParametricFamily T.toPshTypeExpr` without `choice`.
  (Former F7.)

- [x] **P6c. relInterp composition at PshRel level.**
  Extended the `RelInterpComposition.lean` analysis to
  presheaves. (Former F6.)
  In `PshRelDouble.lean`: `pshArrowRel_comp` (arrow
  relations compose from domain decomposition and
  codomain composition witnesses).
  In `PshTypeExpr.lean`:
  `PshTypeExpr.isArrowFree`, `arrowFreeMap`,
  `fullRelInterp_eq_pshRelGraph` (arrow-free expressions
  map graph relations to graph relations),
  `arrowFreeMap_comp` (functoriality),
  `relInterp_comp_of_isArrowFree` (arrow-free equality),
  `hasRelInterpComp` (syntactic composability check),
  `relInterp_comp_of_hasComp` (composition for
  expressions satisfying `hasRelInterpComp`),
  `relInterp_comp_le` (subfunctor inclusion form),
  `relInterp_comp_eq` (equality for arrow-free).
  Examples: `pshDialgebraTypeExpr_hasComp` (positive),
  `pshDinaturalTypeExpr_not_hasComp` and
  `pshAlgebraTypeExpr_not_hasComp` (negative).
  For general (non-graph) relations, `pshBarrLiftRel`
  does not preserve `pshRelComp`; the composition
  analysis applies to graph relations only.

- [~] **P6d. Presheaf-level free theorem equivalences.**
  Generalize `dialgebraParametricEquivNatTrans`,
  `initialAlgebraParametricEquiv`, and
  `dinaturalNumbersParametricEquiv` to `PSh(C)`.
  Done: `pshDialgebraParametricEquivNatTrans`,
  `pshAlgebraParametricEquivParanat`,
  `pshDinaturalParametricEquivParanat` in
  `PshTypeExpr.lean`.
  Infrastructure for Church numerals:
  `homObjIterateN`, `homObjIterateN_comm`,
  `homObjIterateN_map`, `homObjIterateNNatTrans`,
  `pshNatToDinaturalParanat`,
  `pshDinaturalParanatToNat`,
  `pshDinaturalParanatToNat_pshNatTo`
  (forward-backward round trip).
  Remaining: `pshDinaturalNumbersParametricEquiv`,
  `pshInitialAlgebraParametricEquiv`.
  Both face a shared obstacle: the backward-forward
  round trip (and for initial algebras, the forward
  direction itself) requires converting stage-local
  algebra/endomorphism elements into global nat
  trans (to apply fold/catamorphism). At the Type
  level there is only one stage, so local = global.
  For general `C`, `PshDinaturalParanat ≅ ℕ` requires
  `C` to be connected (for a discrete 2-object
  category, `PshDinaturalParanat ≅ ℕ × ℕ`).
  Approaches requiring infrastructure not yet
  available: colimit/density argument, NNO in the
  presheaf topos, connectivity hypothesis with
  `IsConnected C`.

- [ ] **P6e. Twisted-arrow parametric embedding.**
  (Former W6.) Investigate whether `ParametricCopresheaf`
  embeds into or relates to the twisted-arrow copresheaf
  topos `[TwArr(C)ᵒᵖ, Type]`.

## Notes

### Parametricity vs. paranaturality

Parametricity (Reynolds/Wadler) tests ALL commuting pairs
`(h, k)` with `f ∘ h = k ∘ f`. Paranaturality tests only
pairs arising from off-diagonal profunctor elements. These
coincide for "shallow" type expressions (dialgebras, algebras,
Church numerals) but diverge for nested arrows. The divergence
type `∀X. ((X → X) → X) → X` separates them:
`divApplyId` is parametric but not paranatural.

### Topos-theoretic context

`PshParametricPresheaf C` (= `PshRelSpanObj C ⥤ Type`)
is a copresheaf category and therefore a Grothendieck topos.
This resolves the former search for a topos of profunctors
with paranatural morphisms: rather than restricting
profunctors to a subcategory, the parametric copresheaf
category provides a topos that receives fully faithful
embeddings from covariant functors, contravariant functors,
and type expressions (at the Type level; presheaf-level
embeddings are Phase 1 tasks).

Earlier negative results on other candidate toposes remain
as context:

- `DiagDetProf` (profunctors determined by their diagonal)
  is NOT a Grothendieck topos: it lacks binary products
  (counterexample on the walking arrow category), and the
  diagonalization monad `Lan_ι ∘ ι*` is not left-exact
  (`lanDiagProdComparison_surj_common_fact`).
- The paranatural category is not Cartesian closed
  (Uustalu 2010).
- Neumann's di-Yoneda lemma (arXiv:2307.09289) has an
  error and is not true; hom-objects derived from it do
  not work. The standard Yoneda lemma via reduction to
  natural transformations on `[Tw(C)ᵒᵖ, Type v]` applies
  instead.

### ParametricFamily as an end or equalizer

`ParametricFamily T` requires `T.relInterp f (app I₀)
(app I₁)` for all `f : I₀ → I₁`. The end of
`Functor.uncurry.obj T.toProfunctor` requires the wedge
condition `T.profMap id f (app I₀) =
T.profMap f id (app I₁)`.

`relInterp_implies_wedge` gives parametricity => wedge.
The converse holds for type expressions without nested
arrows but fails for nested arrows.

For specific type expressions, `ParametricFamily T` is
equivalent to `Paranat P Q` (see
`algebraParametricEquivParanat`,
`dinaturalParametricEquivParanat`,
`dialgebraParametricEquivNatTrans`), and
`Paranat P Q ≃ StructureIntegral P Q` which is an
equalizer.

Open questions (connected to Phase 4 tasks):

1. Is there a general construction producing profunctors
   `P(T)`, `Q(T)` such that
   `ParametricFamily T ≃ Paranat P(T) Q(T)` for all `T`?
2. Can `relInterp` be expressed as an equalizer of the
   lmap and rmap of some profunctor derived from
   `T.toProfunctor`?
3. Can the parametricity condition be understood as an
   end taken in a Rel-enriched category (where morphisms
   are relations rather than functions)?

### Blog post observation

Relations specialized to functions yield naturality squares.
The blog post conjectures that "all Haskell laws are category
laws in different categories." Our generalization to arbitrary
`C` makes this precise: the double-categorical structure of
`PshRelDouble` provides the ambient framework in which
"category laws" live.

### Literature

- Paranaturals compose (Mulry 1992, Pare-Roman 1998)
- Not Cartesian closed (Uustalu 2010)
- Tambara modules = presheaves on "double" (Pastro-Street
  2008)
- Neumann-Licata POPL 2026: directed type theory via
  dinaturality
- `connectedComponents : Cat ⥤ Type` exists in mathlib
  (`Mathlib.CategoryTheory.Category.Cat.Adjunction`)

### Reference documents

- `docs/.claude/wadler89-theorems-for-free.pdf`: Original
  paper
- `docs/ParametricityViaYonedaRelations.md`: Mathematical
  analysis of the Reynolds/Wadler → YonedaRel connection
- `docs/parametric-functor-embeddings.md`: Embedding
  analysis
- `docs/parametric-functor-universal-property.md`: Universal
  property investigation
- `docs/paranatural-topos-research.md`: Topos structure
  investigation
- `docs/weighted-vs-paranatural-algebra.md`: Weighted
  (co)ends vs. paranaturality
