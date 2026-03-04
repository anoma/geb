# GSOS Distributive Law

## Status: Morphism complete, coherence proofs pending

## Completed

### PolyGSOSRule structure (PolyGSOS.lean)

- `PolyGSOSRule P Q`: a GSOS rule as a polynomial morphism
  `P . (Id x Q) --> Q . T_P`
- `polyIdBehaviorPoly Q`: the identity-behavior product polynomial

### Fold algebra (PolyGSOS.lean)

- `polyGSOSFoldLeafAt`: leaf handler mapping cofree elements
  to product pairs via eta and Q(eta)(str)
- `polyGSOSFoldNodeAt`: node handler applying the GSOS rule
  pipeline: prodComp -> comp_eval -> rho -> comp_eval -> Q(join)
- `polyGSOSFoldCataWithFiber`: recursive catamorphism with fiber
  preservation proof
- `polyGSOSFoldCata`: fold as an Over X morphism

### Distributive law morphism (PolyGSOS.lean)

- `polyGSOSScaleCoalgStrAt`: polyScale(T_P(A), Q)-coalgebra
  combining T_P(epsilon_Q) annotation with fold's Q-structure
- `polyGSOSDistLawMor`: the distributive law T_P(D_Q(A)) -> D_Q(T_P(A))
  via polyCofixUnfold of the scale coalgebra

## Pending

### Coherence axioms

Four axioms from DistributiveLaw structure:

1. **unit**: `eta_{D_Q(A)} ; dist = D_Q(eta_A)`
2. **mul**: `mu_{D_Q(A)} ; dist = T_P(dist) ; dist_{T_P(A)} ; D_Q(mu_A)`
3. **counit**: `dist ; epsilon_{T_P(A)} = T_P(epsilon_A)`
4. **comul**: `T_P(delta_A) ; dist_{D_Q(A)} ; D_Q(dist) = dist ; delta_{T_P(A)}`

The existing P=Q case (PolyDistributiveLaw.lean, 2567 lines) provides
a template.  Counit is typically the easiest; multiplication is the
hardest.

### Packaging

- Natural transformation wrapping `polyGSOSDistLawMor`
- `DistributiveLaw` instance
- Operational monad via `liftedMonad`

## Design notes

The node handler pipeline in `polyGSOSFoldNodeAt`:

1. `prodComp`: convert overPullback to product polynomial evaluation
2. `polyBetweenComp_eval_fiberEquiv.invFun`: to composite evaluation
3. `polyBetweenMorphEvalAt rho.rule`: apply GSOS rule
4. `polyBetweenComp_eval_fiberEquiv.toFun`: from composite evaluation
5. `ccrEvalMap join`: flatten via free monad multiplication

The `join` morphism uses `polyFreeMPolyEval_to_polyFreeM` followed by
`polyFreeMBind` to flatten tree-of-trees.

The `prodComp` morphism constructs product polynomial evaluation from
a pullback pair by:

- Identity component: maps to the first projection element
- Q component: maps to the Q-evaluation child morphism
