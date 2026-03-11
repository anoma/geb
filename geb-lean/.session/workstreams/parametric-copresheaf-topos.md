# Workstream: Parametric Copresheaf Topos

## Status

Active

## Context

Develop the general theory of parametric polymorphism via the
copresheaf topos `PshParametricPresheaf C = PshRelSpanObj C => Type`.
This workstream concerns the category-theoretically generic
constructions only (PshRelDouble, YonedaRel, PshRelSpanObj,
and the copresheaf topos), not the exploratory inductive
constructions (TypeExpr, PshTypeExpr, fullRelInterp).

See `docs/parametric-copresheaf-topos.md` for the conceptual
framework.

## Completed

- [x] **Double category of presheaf relations.** `PshRelDouble`
  with identity, composition, dagger, graph functor, and all
  double category laws. (`PshRelDouble.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 1.

- [x] **Yoneda relation double category.** `YonedaRelDouble`
  with identity, composition, graph functor, and double
  category laws. Terminal specialization to `Discrete PUnit`.
  (`YonedaRelDouble.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 2.

- [x] **Relational span category.** `PshRelSpanObj C` with
  category instance, collage characterization
  (`pshRelSpanCollageIso`), and terminal specialization
  (`relSpanPshRelSpanIso`). (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 3.

- [x] **Covariant embedding (fully faithful).**
  `pshCovariantEmbedding` with `pshCovariantEmbedding_fullyFaithful`.
  (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.1.

- [x] **Contravariant embedding (fully faithful).**
  `pshContravariantEmbedding` with
  `pshContravariantEmbedding_fullyFaithful`.
  (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.2.

- [x] **Profunctor embedding.**
  `pshProfunctorEmbedding`.
  (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.3.

- [x] **Paranatural embedding (faithful).**
  `pshParanaturalProfEmbedding` with
  `pshParanaturalProfEmbedding_faithful`.
  (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.4.

- [x] **Barr extension infrastructure.** Covariant
  (`pshBarrLiftSkel`), contravariant
  (`pshContraBarrLiftSkel`), profunctor
  (`pshProfBarrLiftSkel`), with graph preservation
  (`pshBarrLiftSkel_graph`). (`PshRelDouble.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 1.3.

- [x] **Arrow relation.** `pshArrowRelSkel` with
  relatedness preservation (`pshArrowRelSkel_related`).
  (`PshRelDouble.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 1.4.

- [x] **Parametricity-paranaturality separation.**
  `divApplyId_parametric`, `divApplyId_not_paranatural`,
  `divParametric_not_implies_divParanatural`.
  (`ParanaturalTopos.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 7.

- [x] **Fully faithful diagram functor.**
  `pshRelSpanDiagramFunctor` with full faithfulness, for
  PshTypeExpr. (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.

- [x] **Type-level equivalences.** `relSpanPshRelSpanIso`,
  `parametricFunctorEquiv`, `parametricCopresheafEquiv`.
  (`PshRelSpanDiagram.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 5.5.

## Tasks

### Topos structure

- [ ] **T1. Exponential description.** Compute the concrete
  form of the exponential `[F, G]` in the copresheaf topos.
  Determine `[F, G](.typeNode P)` and
  `[F, G](.relNode P Q R)` explicitly. Relate to
  `pshArrowRelSkel` and `pshIhomProfMap`.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.1.

- [ ] **T2. Subobject classifier description.** Compute the
  subobject classifier `Omega` of the copresheaf topos
  concretely. `Omega(.typeNode P)` should be the set of
  sieves on `.typeNode P` in `PshRelSpanObj C`.
  Characterize what a "parametric predicate" looks like.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.3.

- [ ] **T3. Sections of exponentials.** Show that sections
  (global elements) of `[F, G]` correspond to natural
  transformations `F => G` in the copresheaf topos, i.e.,
  parametric morphisms. This is standard for presheaf
  toposes but worth verifying concretely.

### Identity extension

- [ ] **T4. Identity extension for embedded copresheaves.**
  For a copresheaf `F` in the image of
  `pshCovariantEmbedding`, show that `F(.relNode P P (pshRelId P))`
  is (equivalent to, or embeds into) the diagonal of
  `F(.typeNode P)`. This is the copresheaf-topos analogue
  of Wadler's Identity Extension Lemma. Determine whether
  this holds for all copresheaves or only embedded ones.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.2.

- [ ] **T5. Identity extension for arbitrary copresheaves.**
  Characterize which copresheaves satisfy
  `F(pshRelId P) ~= diagonal of F(P)`. Is this a
  property of a reflective subcategory? Does it hold for
  all copresheaves arising from the embeddings?

### Graph restriction and free theorems

- [ ] **T6. Graph subcategory.** Define the subcategory of
  `PshRelSpanObj C` generated by graph relations
  `pshRelGraph alpha` for natural transformations
  `alpha : P => Q`. Copresheaves on this subcategory
  impose only the wedge/naturality condition, not full
  parametricity.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.4.

- [ ] **T7. Graph restriction functor.** Define the
  restriction functor from `PshParametricPresheaf C` to
  copresheaves on the graph subcategory (T6). Show that
  this forgets the "extra" parametricity data beyond
  naturality.

- [ ] **T8. Free theorem derivation.** For copresheaves in
  the image of `pshCovariantEmbedding`, show that
  restricting to graph relations yields the naturality
  condition. Connect to `pshBarrLiftSkel_graph`.
  Ref: `docs/parametric-copresheaf-topos.md` Section 6.

### Sections of specific copresheaves

- [ ] **T9. Sections of covariant copresheaves.** Show that
  sections of `pshCovariantEmbedding.obj G` correspond to
  (some known mathematical object -- likely "parametric
  elements" of `G` in a suitable sense). At
  `C = Discrete PUnit`, these should specialize to
  sections of `covariantEmbedding.obj G` which are
  natural-transformation-like.

- [ ] **T10. Sections of contravariant copresheaves.** Same
  for `pshContravariantEmbedding.obj F`.

- [ ] **T11. Sections of profunctor copresheaves.** Same
  for `pshProfunctorEmbedding.obj G`. At the type level,
  these should relate to extranatural transformations or
  wedge elements.

### Relation composition

- [ ] **T12. Relation composition and copresheaves.**
  Determine when a copresheaf `F` satisfies
  `F(R_1 ; R_2) ~= F(R_1) ;_F F(R_2)` (composition of
  the induced relations). This is the copresheaf-level
  analogue of the question studied in
  `RelInterpComposition.lean`. Characterize which
  copresheaves have this property.

### Comparison with paranaturality

- [ ] **T13. Paranatural embedding non-fullness.** Give a
  concrete presheaf-level example of a parametric morphism
  that is not paranatural (generalizing the type-level
  divergence examples). This would demonstrate the
  non-fullness of `pshParanaturalProfEmbedding` at the
  presheaf level.

- [ ] **T14. Characterize the gap.** For a profunctor
  `G : PSh(C)^op x PSh(C) => PSh(C)`, characterize the
  difference between `Hom(pshProfunctorEmbedding.obj G, F)`
  and `Paranat G (diagonal of F)`. The kernel of the
  forgetful map from parametric to paranatural morphisms
  measures the additional content of parametricity.

### Internal language

- [ ] **T15. Internal parametricity statement.** Formulate
  the statement "every element of every type is parametric"
  in the internal language of the copresheaf topos and
  verify it holds. This is the topos-internal version of
  Wadler's Parametricity Theorem.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.5.

- [ ] **T16. Directed type theory connection.** Investigate
  the connection between the internal language of the
  copresheaf topos and the directed type theory of
  Neumann-Licata (POPL 2026). The copresheaf topos may
  provide a semantic model.
  Ref: `docs/parametric-copresheaf-topos.md` Section 10.5.

### Yoneda extension

- [ ] **T17. Yoneda extension of sections.** Given a section
  of a copresheaf restricted to representable presheaves
  (via `yonedaULift`), extend it to all presheaves via
  the Yoneda extension / density theorem. This would give
  a choice-free forward bridge from type-level parametric
  families to presheaf-level ones. (Connects to former
  task P5b in `parametricity-free-theorems.md`.)

### Edge category quasitopos

- [x] **T20. Name the category instance.** Give the
  `Category` instance on `PshRelEdge C` the explicit
  name `pshRelEdgeCategory`. (`PshRelDouble.lean`)

- [x] **T21. Exponential in PshRelEdge C.** Show the
  exponential equals
  `(FunctorHom, FunctorHom, pshArrowRel)`.
  Verify the exponential adjunction directly.
  (`PshRelEdgeExp.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.5.

- [x] **T21b. Finite limits and colimits in PshRelEdge C.**
  Terminal, initial, binary coproducts, equalizers,
  coequalizers. (`PshRelEdgeLimits.lean`)

- [x] **T22. Identity extension as functor property.**
  Show `pshRelIdentFunctor` preserves exponentials
  (the IEP as a cartesian closed functor property).
  (`PshRelEdgeIdentPreservation.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.6.

- [x] **T23. pshRelIdentFunctor preserves limits.**
  Show `pshRelIdentFunctor` preserves products,
  terminal object, and equalizers.
  (`PshRelEdgeIdentPreservation.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.6.

- [x] **T23b. pshRelIdentFunctor preserves colimits.**
  Show `pshRelIdentFunctor` preserves coproducts,
  initial object, and coequalizers.
  (`PshRelEdgeIdentPreservation.lean`)

- [x] **T23c. pshBarrLiftRel as endofunctor.**
  `pshBarrLiftEdgeFunctor G : PshRelEdge C ⥤ PshRelEdge C`.
  (`PshRelDouble.lean`)

- [x] **T24. Inclusion into PSh(C x I^op).** Construct
  the fully faithful inclusion
  `PshRelEdge C -> [WalkingSpan, PSh(C)]`.
  `pshRelEdgeInclusionFunctor` with
  `pshRelEdgeInclusionFullyFaithful`.
  Separation reflector `pshRelEdgeSepFunctor` with
  adjunction `pshRelEdgeSepAdjunction`.
  (`PshRelEdgeInclusion.lean`)
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.10.

- [ ] **T25. Evaluation functors.** For each
  relation `(P, Q, R)`, construct the evaluation functor
  `eval_{P,Q,R} : PshParametricFunctor C E -> Spans(E)`
  sending `F` to `(F(.typeNode P), F(.typeNode Q),
  F(.relNode P Q R))` with projections `F(fstProj)`,
  `F(sndProj)`. Investigate the profunctor assembling
  these: `PshRelEdge(C)^op x PshParametricFunctor(C, E)
  -> E`. Note: there is no single functor
  `PshParametricPresheaf C -> PshRelEdge C` without
  fixing a relation.
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.8.

### Lattice-enriched sites

- [ ] **T26. Lattice-enriched span site.** Investigate
  adding Heyting algebra structure (inclusions R <= S)
  to `PshRelSpanObj C` as morphisms between relation
  nodes. Determine whether embedded copresheaves
  satisfy monotonicity.
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.10.

- [ ] **T27. Yoneda-restricted subobject site.** Define
  the small site using `YonedaRel X Y` with lattice
  and base-change structure. Investigate whether Kan
  extension along Yoneda recovers parametric structure.
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.10.

- [ ] **T28. Sep_J equivalence.** Construct the
  equivalence `PshRelEdge C ~= Sep_J(C x I^op)`
  explicitly (walking span I, topology J, separation).
  Ref: `docs/parametric-copresheaf-topos.md` Section 11.2.

### Documentation

- [ ] **T18. Annotate PshRelSpanDiagram.lean.** Add
  comments explaining the conceptual role of each
  definition, referencing
  `docs/parametric-copresheaf-topos.md`.

- [ ] **T19. Annotate PshRelDouble.lean.** Same for the
  double category infrastructure.
