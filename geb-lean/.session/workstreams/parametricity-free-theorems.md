# Workstream: Parametricity and Free Theorems

## Status

Active (being refocused on PshRelEdge)

## Context

Formalize Wadler's "Theorems for free!" (1989) and the
Reasonably Polymorphic blog post's observations in a
generalized categorical setting.

The primary framework is now `PshRelEdge C` (the edge
category of presheaf relations) and its reflective
embedding into `[WalkingSpan, PSh(C)]`.  The former
approach via `PshRelSpanObj` copresheaves is being
superseded.

The project has two tracks:

1. **Type-level** (`ParanaturalTopos.lean`,
   `RelSpanDiagram.lean`, etc.): Wadler's original
   System F / `Type` setting.  These results remain
   valid and serve as the `C = Discrete PUnit`
   specialization.
2. **Presheaf-level** (`PshRelDouble.lean`,
   `PshRelEdge*.lean`, `PshRelEdgeInclusion.lean`):
   Generalization to `PSh(C)` using `PshRelEdge C`.

## Completed infrastructure

### Type-level (ParanaturalTopos.lean, RelSpanDiagram.lean)

- `TypeExpr` inductive type with `.var`, `.app F T`,
  `.arrow T1 T2`
- `TypeExpr.toProfunctor`, `.interp`, `.profMap`
- `TypeExpr.relInterp` and `TypeExpr.fullRelInterp`
- `ParametricFamily T` structure
- Type-level embeddings: `covariantEmbedding` (fully
  faithful), `contravariantEmbedding` (fully faithful),
  `profunctorEmbedding`, `paranaturalProfEmbedding`
  (faithful)
- Divergence: `divApplyId_parametric`,
  `divApplyId_not_paranatural`

### Type-level free theorems (Wadler correspondences)

- `homParametricEquivUnit`
- `dialgebraParametricEquivNatTrans F G`
- `algebraParametricEquivParanat F`
- `initialAlgebraParametricEquiv F muF hmuF`
- `dinaturalParametricEquivParanat`
- `dinaturalNumbersParametricEquiv`
- `terminalCoalgebraStructuralCoendEquiv`

### Presheaf-level infrastructure (PshRelEdge-based)

- `PshRel` as `Subfunctor (pshProdPresheaf P Q)`
  (`PshRelDouble.lean:208`)
- `pshRelId` (`PshRelDouble.lean:214`),
  `pshRelComp`, `pshRelGraph` (`PshRelDouble.lean:418`),
  `pshRelDagger`, `pshRelRelated`,
  `pshRelGraphFunctor` (`PshRelDouble.lean:488`)
- `pshBarrLiftRel` (`PshRelDouble.lean:1382`),
  `pshContraBarrLiftRel` (`PshRelDouble.lean:1953`),
  `pshProfBarrLiftRel` (`PshRelDouble.lean:2189`)
- `pshBarrLiftRel_graph` (`PshRelDouble.lean:1580`)
- `pshArrowRel` (`PshRelDouble.lean:2633`)
- `pshBarrLiftEdgeFunctor` (`PshRelDouble.lean:1920`)
- `pshRelIdentFunctor` (`PshRelDouble.lean:1126`)
- `PshRelEdge C` with category instance, exponentials,
  finite limits/colimits, strong subobject classifier
- `pshRelIdentFunctor` preserves products,
  exponentials, coproducts, terminal, initial,
  equalizers, coequalizers
- `pshRelEdgeInclusionFunctor`
  (`PshRelEdgeInclusion.lean:132`), fully faithful
- `pshRelEdgeSepFunctor`
  (`PshRelEdgeInclusion.lean:302`) with adjunction
  (`PshRelEdgeInclusion.lean:470`)
- Reflector preserves finite products;
  inclusion is exponential ideal
- `pshOverOmegaEdgeFunctor`, `pshTruthLabelFunctor`,
  `pshRelIdentFunctor_factorization`
  (`PshRelEdgeOverOmega.lean`)

### Old-framework presheaf results (PshRelSpanObj-based)

These exist in `PshRelSpanDiagram.lean` and
`PshTypeExpr.lean` but target the old `PshRelSpanObj`
framework:

- `PshRelSpanObj C`, `pshRelSpanCollageIso`
- `pshCovariantEmbedding`,
  `pshContravariantEmbedding`,
  `pshProfunctorEmbedding`,
  `pshParanaturalProfEmbedding` (all target
  `PshRelSpanObj`, not `PshRelEdge`)
- `PshTypeExpr`, `PshParametricFamily` (inductive,
  not standard category theory)
- `HasIdentityExtension` for `SpanFamilyData`

## Tasks

### Wadler free theorems in PshRelEdge

See `parametric-copresheaf-topos.md` tasks W1-W9 for
the detailed Wadler correspondence tasks.  The tasks
below concern additional free theorem results.

- [ ] **P3a. Constant-type free theorem.** Prove
  `ParametricFamily (.arrow .var (.arrow .var .var)) ≅
  Bool` (or `Fin 2`).  Can be done at type level first.

- [ ] **P3b. Yoneda/representability isomorphism.** Prove
  `∀X. (A -> X) -> X ≅ A` (Wadler Section 3.8).
  See task W8 in `parametric-copresheaf-topos.md`.

- [ ] **P3c. Multi-variable type expressions.** Extend
  `TypeExpr` to support multiple type variables (needed
  for fst, snd, K, fold, filter, zip from Wadler).
  Note: in the PshRelEdge framework, multi-variable
  types correspond to edges with different source and
  target presheaves.

- [ ] **P3d. Product type constructor.** Add products to
  `TypeExpr` (needed for K combinator, zip, and
  multi-argument results).

- [ ] **P3e. Fold/filter free theorems.** Formalize
  Wadler Sections 3.2 (fold), 3.3 (sort/nub),
  3.5 (map decomposition), 3.6 (fold decomposition),
  3.7 (filter decomposition).
  See tasks W4-W6 in `parametric-copresheaf-topos.md`.

- [ ] **P3f. Polymorphic equality impossibility.**
  Wadler Section 3.4.
  See task W7 in `parametric-copresheaf-topos.md`.

### Weight functors and twisted-arrow connection

- [ ] **P4a. typeExprWeight functor.** Define
  `typeExprWeight : TypeExpr -> (TwistedArrow Type => Type)`
  recursively from `relInterp` data.

- [ ] **P4b. Comparison with wedgeWeight.** Construct a
  natural transformation
  `typeExprWeight T -> wedgeWeight (T.toProfunctor)`.

- [ ] **P4c. WedgeWeightFactorization.** Formalize the
  factorization characterization of `wedgeWeight`.

- [ ] **P4d. Parametric weight characterization.** Find
  the weight `W` such that `ParametricFamily T` is the
  weighted end with weight `W`.

### Generalized theory

- [ ] **P6a. Parametric cofamilies.** Define
  `ParametricCofamily` (dual) and prove equivalence
  with terminal coalgebra carrier.

- [ ] **P6b. Yoneda extension.** Extend a
  `ParametricFamily T` to all presheaves via the
  density theorem.
  See task S2 in `parametric-copresheaf-topos.md`.

- [x] **P6c. relInterp composition at PshRel level.**
  `pshArrowRel_comp` in `PshRelDouble.lean`.

- [~] **P6d. Presheaf-level free theorem equivalences.**
  Done: `pshDialgebraParametricEquivNatTrans`,
  `pshAlgebraParametricEquivParanat`,
  `pshDinaturalParametricEquivParanat`.
  Remaining: `pshDinaturalNumbersParametricEquiv`,
  `pshInitialAlgebraParametricEquiv` (both face
  local-to-global obstacle for general `C`).

## Notes

### Parametricity vs. paranaturality

Parametricity tests ALL commuting pairs `(h, k)` with
`f . h = k . f`.  Paranaturality tests only pairs arising
from off-diagonal profunctor elements.  These coincide for
shallow type expressions but diverge for nested arrows.
The divergence type `∀X. ((X -> X) -> X) -> X` separates
them: `divApplyId` is parametric but not paranatural.

### Blog post observation

The blog post conjectures "all Haskell laws are category
laws in different categories."  This is made precise by
the reflective embedding
`PshRelEdge C <-> [WalkingSpan, PSh(C)]`:
Wadler's constructions live naturally in the edge category,
which sits inside a presheaf topos.  Specializing relations
to graphs recovers naturality conditions (the "category
laws").

### Literature

- Paranaturals compose (Mulry 1992, Pare-Roman 1998)
- Not Cartesian closed (Uustalu 2010)
- Tambara modules = presheaves on "double"
  (Pastro-Street 2008)
- Neumann-Licata POPL 2026: directed type theory
- Wadler, "Theorems for free!" (1989):
  `docs/.claude/wadler89-theorems-for-free.pdf`
- Blog: `https://reasonablypolymorphic.com/blog/theorems-for-free/`
