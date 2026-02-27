# Workstream: Coalgebra-Copresheaf Equivalence

## Status

Active

## Context

Proving that for a polynomial endofunctor P on Over X,
the category of P-coalgebras is equivalent to the
category of copresheaves on the cofree category:
`PolyCoalg P ≌ PolyCofreeCat P ⥤ Type u`.

## Mathematical Background

See `.session/docs/coalgebra-copresheaf-math.md` for
detailed mathematical findings from the literature.

## Tasks

### Phase 1: Functor-Coalg ≌ Comonad-Coalg

- [x] Check mathlib for comonadicity infrastructure
  - Mathlib has `Comonad.comparison`,
    `Comonad.Coalgebra`, Beck's theorem
    (`comonadicOfHasPreserves...`)
- [x] `polyCoalgToComonadCoalg` functor
  (via `Comonad.comparison`)
- [x] `polyComonadCoalgToCoalg` functor
  (structure: `k ≫ cofreeStr ≫ P.map(counit)`)
- [x] Forward roundtrip `K⁻¹(K(α)).str = α.str`
  (`polyCoalgComonad_forward_str`)
- [x] Backward roundtrip `K(K⁻¹(c)).a = c.a`
  (`polyCoalgComonad_backward`)
  Proven coinductively using self-consistency
  (`comonadCoalgSelfconsistent`) derived from
  coassociativity.
- [x] `polyCoalgComonadEquiv`

### Phase 1b: Functor-Alg ≌ Monad-Alg (dual)

- [x] `polyAlgToMonadAlg` functor
- [x] `polyMonadAlgToAlg` functor
- [x] Roundtrip isomorphisms
- [x] `polyAlgMonadEquiv`

### Phase 2: Copresheaf Functor

- [x] `coalgCopresheafShapeAt` : transported shape
- [x] `coalgCopresheafTarget` : target cofree object
- [x] `coalgCopresheafObj` : copresheaf value type
- [x] `coalgCopresheafShapeAt_heq` : HEq to raw shape
- [x] `coalgCopresheafCastPos` : position cast helper
- [x] `coalgCopresheafExtractVal` : annotation extraction
- [x] `coalgCopresheafExtractVal_fiber` : fiber lemma
- [x] `coalgCopresheafChild` : depth-1 child annotation
- [x] `coalgCopresheafChild_consistent` : self-consistency
- [x] `coalgCopresheafChild_fiber` : child fiber
- [x] `coalgCopresheafChild_mtype` : child M-type HEq
- [x] `coalgCopresheafChild_shape_heq` : child shape HEq
- [x] `coalgCopresheafChild_rawTarget`
- [x] `coalgCopresheafChild_target_sigma`
- [x] `coalgCopresheafChild_target_fiber`
- [x] `coalgCopresheafChild_target_shape`
- [x] `coalgCopresheafChild_rawShape_heq`
- [x] `coalgCopresheafShapeAt_children_heq`
- [x] `coalgCopresheafChild_rawToShape`
- [x] `coalgCopresheafChild_shapeToTransported`
- [x] `coalgCopresheafTargetRaw` / `_eq`
- [x] `coalgCopresheafCastPos1_collapse`
- [x] `coalgCopresheafChild_depth1_target`
- [x] `coalgCopresheafMapByDepth`
- [x] `coalgCopresheafMap`
- [ ] `coalgCopresheafMap_comp` : composition law.
      Base case (depth 0) done. Succ case requires
      induction on f.depth, showing extraction at
      concatenated position = sequential extraction.
      Both sides step into the child at the same
      edge; by IH at depth fn, they agree.
- [ ] `coalgCopresheafMap` : morphism action
- [ ] `coalgCopresheaf_map_id` : identity pres.
- [ ] `coalgCopresheaf_map_comp` : composition pres.
- [ ] `coalgCopresheaf` : the copresheaf functor
- [ ] `coalgCopresheafFunctor` : functorial in c

### Phase 3: Comonad-Coalg ≌ Copresheaves

- [ ] `comonadCoalgToCopresheaf` (Phi)
- [ ] `copresheafToComonadCoalg` (Psi)
- [ ] Roundtrip isomorphisms
- [ ] `comonadCoalgCopresheafEquiv`

### Phase 4: Compose

- [ ] `polyCoalgCopresheafEquiv`
