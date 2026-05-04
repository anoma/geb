# GSOS Coherence Proofs and Packaging

## Status: Phases 1-3 complete; Phases 4-6 pending

## Context

`GebLean/PolyGSOS.lean` contains the GSOS distributive law
morphism `polyGSOSDistLawMor : T_P(D_Q(A)) -> D_Q(T_P(A))`.
This document plans the remaining work to package it as a
`DistributiveLaw` instance.

The existing P=Q case in `GebLean/PolyDistributiveLaw.lean`
(2567 lines) provides the template.  All proofs there follow
the same architecture:

1. `Over.OverMorphism.ext` + `funext` for pointwise equality
2. `Sigma.ext` for fiber components
3. `PolyCofix.ext` + `intro n` for depth-indexed approximation
4. Induction on `n` with case analysis on tree structure

The GSOS case differs from P=Q in:

- The fold uses a GSOS rule `rho : P . (Id x Q) -> Q . T_P`
- The join uses `polyFreeMBind` (not a simpler self-join)
- Separate polynomials P (signature) and Q (behavior)
- Existing monad/comonad helper lemmas
  (`polyFreeMonad_eta_eq`, `polyCofreeComonad_eps_eq`, etc.)
  are parametric and reusable with different P/Q arguments

## Implementation order

### Phase 1: Counit (done)

**Statement**: `dist . eps_{T_P(A)} = T_P(eps_A)`

Proved via `polyGSOSDistLawMor_head_fst` and
`polyGSOSDistLaw_counit`.

### Phase 2: Unit (done)

**Statement**: `eta_{D_Q(A)} . dist = D_Q(eta_A)`

Proved via `polyGSOSDistLaw_unit_approx` (depth-indexed
induction) and `polyGSOSDistLaw_unit`.

### Phase 3: Naturality (done)

**Statement**: `T_P(D_Q(f)) . dist_B = dist_A . D_Q(T_P(f))`

Proved via a pipeline of sub-lemmas:

- `polyGSOSDistLaw_annot_natural`: annotation naturality
- `polyGSOSFoldCata_snd_fst_eq`: fold-annotation identity
- `polyGSOSFoldQIndex`, `polyGSOSFoldQIndex_leaf`,
  `polyGSOSFoldQIndex_eq`: Q-index naturality
- `polyGSOSFoldFst_natural`: fold fst naturality
- `polyGSOSFoldLeafAt_snd_natural`: leaf Q-eval naturality
- `polyGSOSFoldNodeAt_snd_natural`: node Q-eval naturality
  (7-step pipeline through `overPullbackToIdQEval`,
  `polyFreeMJoinEval`, `polyBetweenComp_eval_invFun`,
  `polyBetweenComp_eval_toFun`, rho, compose, join)
- `polyGSOSFoldQeval_natural`: full Q-eval naturality
- `polyBetweenEvalMap_mor_apply`: sigma extraction utility
- `polyGSOSScaleCoalg_morphism_h`: coalgebra morphism
  (leaf and node cases)
- `polyGSOSDistLaw_naturality`: assembled via
  `polyCofixUnfold_precomp`

NatTrans packaging not yet written (pending as part of
Phase 6).

### Phase 4: Comultiplication

**Statement**:
`T_P(delta_A) . dist_{D_Q(A)} . D_Q(dist) = dist . delta_{T_P(A)}`

**Estimated size**: ~400 lines

**Strategy**: Comonad comultiplication.  Both sides are
maps into `D_Q(D_Q(T_P(A)))`.  Use the same depth-indexed
approximation approach.

**Lemmas**:

- `polyGSOSDistLaw_comul_annot_eq`: annotation equality
- `polyGSOSDistLaw_comul_approx_leaf`: leaf case
- `polyGSOSDistLaw_comul_approx_node`: node case
- `polyGSOSDistLaw_comul_approx`: main induction

### Phase 5: Multiplication

**Statement**:
`mu_{D_Q(A)} . dist = T_P(dist) . dist_{T_P(A)} . D_Q(mu_A)`

**Estimated size**: ~600 lines

**Strategy**: This is the hardest proof.  The P=Q proof
uses `polyCofixUnfold_precomp` to express both sides as
anamorphisms and then shows both sides satisfy the same
coalgebra condition.

**Lemmas**:

- `polyGSOSDistLaw_mu_hom_h`: coalgebra condition for
  monad multiplication fold (the LHS coalgebra structure)
- `polyGSOSDistLaw_tdist_hom_h`: coalgebra condition
  for `T_P(dist) . dist_{T_P(A)} . D_Q(mu)` (the RHS)
- Main proof via `polyCofixUnfold_precomp` equality

### Phase 6: Packaging

**Estimated size**: ~50 lines

**Definitions**:

- `polyGSOSDistributiveLaw`: the `DistributiveLaw`
  instance, using `polyFreeMonad X P` and
  `polyCofreeComonad X Q`
- Each field delegates to its corresponding lemma after
  `simp` unfolding of monad/comonad component equalities

## Notes

The existing helper lemmas in `PolyDistributiveLaw.lean`
are parametric:

- `polyFreeMonad_eta_eq` works for any `P`
- `polyCofreeComonad_eps_eq` works for any polynomial
  (instantiate with `Q`)
- `polyFreeMonad_mu_eq`, `polyCofreeComonad_delta_eq`
  similarly parametric

These can be used directly in the GSOS packaging without
needing GSOS-specific versions.
