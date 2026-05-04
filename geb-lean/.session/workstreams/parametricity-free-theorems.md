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
the detailed Wadler correspondence tasks.  All
Wadler free theorems (W1-W9) are now formalized at
the PshRelEdge level.

### Completed generalized theory

- [x] **P6a. Parametric cocones.** `ParametricCocone`
  (dual of `ParametricCone`) for existential types.
  `parametricCoconeEquiv`, `parametricCoconeInject`,
  `barrCoconeToPresheafCocone`, `PresheafCosection`.
  Terminal coalgebra connection deferred (Q11).

- [x] **P6b. Yoneda extension.** Done as S2 in
  `parametric-copresheaf-topos.md`.

- [x] **P6c. relInterp composition at PshRel level.**
  `pshArrowRel_comp` in `PshRelDouble.lean`.

### Retired (TypeExpr/PshTypeExpr-specific)

The following tasks are specific to the `TypeExpr` /
`PshTypeExpr` inductive syntax layer, which is a
potential front-end but not part of the categorical
foundations (`PshRelEdge`, `ParametricCone`,
`PresheafSection`, etc.).  They are retained here
for reference but are not on the active task list.

- **P3a.** `ParametricFamily (.arrow .var
  (.arrow .var .var)) ≅ Bool`.
- **P3c.** Multi-variable `TypeExpr`.
- **P3d.** Product type constructor for `TypeExpr`.
- **P4a.** `typeExprWeight` functor.
- **P4b.** Comparison with `wedgeWeight`.
- **P4c.** `WedgeWeightFactorization`.
- **P4d.** Parametric weight characterization.
- **P6d.** Remaining presheaf-level free theorem
  equivalences (`pshDinaturalNumbersParametricEquiv`,
  `pshInitialAlgebraParametricEquiv`). These face a
  local-to-global obstacle for general `C`.

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
