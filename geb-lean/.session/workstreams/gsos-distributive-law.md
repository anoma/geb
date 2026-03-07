# GSOS Distributive Law

## Status: Naturality complete; coherence proofs pending

## Current build state

File: `GebLean/PolyGSOS.lean` (~1560 lines, compiles
cleanly with zero warnings)

## Completed

### PolyGSOSRule structure

- `PolyGSOSRule P Q`: GSOS rule as polynomial morphism
  `P . (Id x Q) --> Q . T_P`
- `polyIdBehaviorPoly Q`: identity-behavior product

### Fold algebra

- `polyGSOSFoldLeafAt`: leaf handler
- `polyGSOSFoldNodeAt`: node handler (5-step pipeline)
- `polyGSOSFoldCataWithFiber`: catamorphism with fiber
- `polyGSOSFoldCata`: fold as Over X morphism
- `overPullbackToIdQEval`: factored-out prodComp utility
- `polyFreeMJoinEval`: factored-out join utility

### Distributive law morphism

- `polyGSOSScaleCoalgStrAt`: scale coalgebra structure
- `polyGSOSDistLawMor`: dist law via polyCofixUnfold

### Counit coherence (done)

- `polyGSOSDistLawMor_head_fst`
- `polyGSOSDistLaw_counit`

### Unit coherence (done)

- `polyGSOSDistLaw_unit_approx`
- `polyGSOSDistLaw_unit`

### Naturality (done)

- `polyGSOSDistLaw_annot_natural`
- `polyGSOSFoldCata_snd_fst_eq`
- `polyGSOSNodeQIdx`, `polyGSOSFoldQIndex`
- `polyGSOSFoldQIndex_leaf`, `_node_unfold`, `_eq_node`,
  `_eq`
- `polyGSOSFoldFst_natural`: fold fst naturality
- `polyGSOSFoldLeafAt_snd_natural`: leaf Q-eval nat
- `polyGSOSFoldNodeAt_snd_natural`: node Q-eval nat
  (pipeline chain through 7 rewrite steps)
- `polyGSOSFoldQeval_natural`: full Q-eval naturality
- `polyBetweenEvalMap_mor_apply`: sigma extraction utility
- `polyGSOSScaleCoalg_morphism_h`: coalgebra morphism
  (both leaf and node cases)
- `polyGSOSDistLaw_naturality`: assembled via
  `polyCofixUnfold_precomp`

Pipeline naturality sub-lemmas:

- `overPullbackToIdQEval_comm`: prodComp naturality
- `polyFreeMJoinEval_natural`: join naturality
- `polyBetweenComp_eval_invFun_natural`: invFun naturality
- `polyBetweenComp_eval_toFun_natural`: toFun naturality
- `morphEvalAt_ccrEvalMap_comm`: rho naturality

## Remaining phases

### Phase N-pack: NatTrans packaging (~30 lines)

Statement:

```text
T_P(delta_A) ≫ dist_{D_Q(A)} ≫ D_Q(dist_A) =
  dist_A ≫ delta_{T_P(A)}
```

Architecture: Both sides map
`T_P(D_Q(A)) → D_Q(D_Q(T_P(A)))`. Reduce to
depth-indexed approximation via `PolyCofix.ext`, induct
on depth with node/leaf case analysis.

Template: `polyDistLaw_comul` in PolyDistributiveLaw.lean
(lines 959-1500).

#### CM-1: `polyGSOSDistLaw_comul_annot_eq` (~20 lines)

**Statement**: The annotation component of the LHS
(which applies `T_P(eps_Q . D_Q(eps_Q) . delta_Q)`)
equals the annotation of the RHS
(which applies `T_P(eps_Q)`).

**Proof**: Use comonad law `eps . delta = id`
(`polyCofree_left_triangle`) composed with
`polyFreeMapAt_comp`.

**Dependencies**: None.

#### CM-2: `polyGSOSDistLaw_comul_approx_leaf` (~170 lines)

**Statement**: At depth n+1, the leaf case (pure leaf
`eta(d)` where `d : PolyCofreeM A Q x`) holds.

**Proof sketch**:

- LHS: `T_P(delta)(eta(d))` = `eta(delta(d))`, then
  `dist(eta(delta(d)))` by unit coherence =
  `D_Q(eta)(delta(d))`, then `D_Q(dist)(...)` =
  `D_Q(dist . eta)(delta(d))` =
  `D_Q(D_Q(eta))(delta(d))`.
- RHS: `dist(eta(d))` by unit coherence =
  `D_Q(eta)(d)`, then `delta(D_Q(eta)(d))` by comonad
  comultiplication naturality.
- Show these match at depth n+1 using IH on children.
- Uses `polyGSOSDistLaw_unit_approx`,
  `polyCofreeMapApprox` properties, and comonad laws.

**Dependencies**: Unit coherence (done).

#### CM-3: `polyGSOSDistLaw_comul_approx_node` (~110 lines)

**Statement**: At depth n+1, the node case
(P-node with children) holds.

**Proof sketch**:

- Annotation equality from CM-1.
- Q-index equality: both sides produce the same Q-index
  because the fold's Q-index is carrier-independent
  (by `polyGSOSFoldQIndex` properties extended to the
  comultiplication setting).
- Q-children: by IH on each Q-direction.
- Uses `polyCofixApprox_intro_polyScale_congr`.

**Dependencies**: CM-1.

#### CM-4: `polyGSOSDistLaw_comul_approx` (~30 lines)

**Statement**: Depth-indexed equality for all n and all
trees t.

**Proof**: Induction on n. Base case trivial. Inductive
case matches on tree structure, dispatching to CM-2
(leaf) and CM-3 (node).

**Dependencies**: CM-2, CM-3.

#### CM-5: `polyGSOSDistLaw_comul` (~40 lines)

**Statement**: The full morphism equality.

**Proof**: `Over.OverMorphism.ext`, `funext ⟨x, t⟩`,
`Sigma.ext` (fiber `rfl`), `PolyCofix.ext`, `intro n`,
apply CM-4.

**Dependencies**: CM-4.

Commit: "GSOS comultiplication coherence proof"

### Phase MU: Multiplication coherence (~650 lines)

Statement:

```text
mu_{D_Q(A)} ≫ dist_A =
  T_P(dist_A) ≫ dist_{T_P(A)} ≫ D_Q(mu_A)
```

Architecture: Express both sides as anamorphisms from
`polyScale(T_P(A), Q)`-coalgebras on
`T_P(T_P(D_Q(A)))`, then show they are the unique
coalgebra morphism using `polyCofixUnfold_precomp`.

Template: `polyDistLaw_mul` in PolyDistributiveLaw.lean
(lines 1630-2410).

#### MU-1: Source coalgebra definition (~80 lines)

**`polyGSOSDistLaw_mul_srcCoalgStrAt`** (~20 lines):
The `polyScale(T_P(A), Q)`-coalgebra structure on
`T_P(T_P(D_Q(A)))`. Combines:

- Annotation: `T_P(eps_Q)(mu(t))` where mu =
  `polyFreeMJoin` or `polyFreeCounitFold`
- Q-index: from `polyGSOSFoldCata` applied to mu(t)
- Q-children: `eta ≫ (polyGSOSFoldCata(mu(t))).Q-children`
  --- embed fold's Q-children into T_P(T_P(D_Q(A))) via
  the free monad unit, so that `Scale.map(mu)` recovers
  them via `mu . eta = id`

**Packaging** (~60 lines):

- `polyGSOSDistLaw_mul_srcCoalgStrLeft`
- `polyGSOSDistLaw_mul_srcCoalgStr_comm`
- `polyGSOSDistLaw_mul_srcCoalgStr`
- `polyGSOSDistLaw_mul_srcCoalg`

Template: lines 1755-1842.

**Dependencies**: polyGSOSFoldCata.

#### MU-2: RHS coalgebra definition (~10 lines)

**`polyGSOSDistLaw_mul_rhsCoalg`**: The
`polyScale(T_P(A), Q)`-coalgebra on `D_Q(T_P(A))`
obtained by reindexing the GSOS scale coalgebra at
`T_P(A)` by `polyFreeCounitFold P (polyFreeAlg A P)`
(monad mu).

Uses `polyScaleReindexCoalg`.

Template: line 1630.

**Dependencies**: polyGSOSScaleCoalg.

#### MU-3: LHS coalgebra morphism (`mu_hom_h`) (~180 lines)

**Statement**: mu is a coalgebra morphism from srcCoalg
to the GSOS scale coalgebra.

**Proof approach**:

1. `Over.OverMorphism.ext`, `funext`, induction on tree
2. **Node case** (t = node(pIdx, children)):
   - `mu(node) = node(pIdx, mu ∘ children)`
   - srcCoalgStr computes fold(mu(node))
   - fold(mu(node)) = fold(node(pIdx, mu∘children))
     = nodeHandler(pIdx, fold(mu(children_e)))
   - After Scale.map(mu), Q-children become
     `mu(eta(fold-child)) = fold-child`
   - RHS: scaleCoalgStr(node(pIdx, mu∘children)) computes
     fold on the same tree, giving same result
   - Close via IH on children
3. **Leaf case** (t = leaf(a)):
   - `mu(leaf(a)) = a.val.2` (inner tree, transported)
   - srcCoalgStr computes fold(a.val.2)
   - After Scale.map(mu), Q-children become
     `mu(eta(fold-child)) = fold-child`
   - RHS: scaleCoalgStr(a.val.2) computes fold(a.val.2)
   - Same result, close directly

**Sub-lemmas to factor out**:

- mu_hom_h_node_annot: annotation equality at nodes
- mu_hom_h_node_qidx: Q-index equality at nodes
- mu_hom_h_leaf: full leaf case
- mu_hom_h_node_qchildren: Q-children after mu.eta=id

Template: lines 1868-2047.

**Dependencies**: MU-1, polyGSOSScaleCoalg.

#### MU-4: RHS coalgebra morphism (`tdist_hom_h`) (~300 lines)

**Statement**: `T_P(dist)` is a coalgebra morphism from
srcCoalg to rhsCoalg.

**Proof approach**:

1. `Over.OverMorphism.ext`, `funext`, induction on tree
2. **Node case**: Annotation equality uses counit
   coherence (`polyGSOSDistLaw_counit`) and mu naturality.
   Q-structure uses `polyCofixUnfold_coalg_comm` relating
   dist's output structure to the scale coalgebra.
3. **Leaf case**: Show dist applied to pure leaf matches
   the expected structure.

**Sub-lemmas to factor out**:

- tdist_hom_h_node_annot: annotation at nodes
- tdist_hom_h_node_qstructure: Q-structure at nodes
- tdist_hom_h_leaf: full leaf case

Template: lines 2048-2353.

**Dependencies**: MU-1, MU-2, counit coherence (done).

#### MU-5: Assembly (`polyGSOSDistLaw_mul`) (~60 lines)

With `mu_hom_h` and `tdist_hom_h`, apply
`polyCofixUnfold_precomp` twice:

1. `lhs_eq`: `mu ≫ dist = polyCofixUnfold srcCoalg`
   (via `polyCofixUnfold_precomp` with mu_hom_h)
2. `rhs_eq1`: `dist_{TA} ≫ D_Q(mu) =
   polyCofixUnfold rhsCoalg`
   (via `polyScaleReindex`)
3. `rhs_eq2`: `T(dist) ≫ polyCofixUnfold rhsCoalg =
   polyCofixUnfold srcCoalg`
   (via `polyCofixUnfold_precomp` with tdist_hom_h)
4. `rw [lhs_eq, rhs_eq1, rhs_eq2]`

Template: lines 2354-2410.

**Dependencies**: MU-3, MU-4.

Commit: "GSOS multiplication coherence proof"

### Phase PK: Final packaging (~60 lines)

#### PK-1: `polyGSOSDistributiveLaw` (~40 lines)

```lean
def polyGSOSDistributiveLaw
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    DistributiveLaw
      (polyFreeMonad X P)
      (polyCofreeComonad X Q) where
  dist := polyGSOSDistLawNat P Q rho
  unit := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyFreeMonad_eta_eq,
      polyCofreeComonad_map_eq]
    exact polyGSOSDistLaw_unit A P Q rho
  counit := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyCofreeComonad_eps_eq,
      polyFreeMonad_map_eq]
    exact polyGSOSDistLaw_counit A P Q rho
  mul := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyFreeMonad_mu_eq,
      polyFreeMonad_map_eq,
      polyCofreeComonad_map_eq]
    exact polyGSOSDistLaw_mul A P Q rho
  comul := fun A => by
    simp only [polyGSOSDistLawNat,
      polyGSOSDistLawNatApp,
      polyCofreeComonad_delta_eq,
      polyCofreeComonad_map_eq,
      polyFreeMonad_map_eq]
    exact polyGSOSDistLaw_comul A P Q rho
```

Template: PolyDistributiveLaw.lean lines 2510-2567.

#### PK-2: `polyGSOSOperationalMonad` (~5 lines)

```lean
def polyGSOSOperationalMonad
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    Monad (polyCofreeComonad X Q).Coalgebra :=
  liftedMonad (polyGSOSDistributiveLaw P Q rho)
```

#### PK-3: Full build and test

```bash
lake build && lake test
```

Commit: "GSOS distributive law and operational monad"

#### PK-4: Update session documents

Mark completed in
`polynomial-algebra-coalgebra-combinators.md`.
Update this file to reflect completion.

## Resumption guide

When resuming after compaction/restart:

1. Run `lake build GebLean.PolyGSOS 2>&1 | head -20` to
   see current errors
2. Check `git log --oneline -5` for last commit
3. Find the next uncompleted step in this document
4. For each step, use the underscore technique:
   write signature with `_` body, build, check goal,
   fill in
5. After completing a phase, commit and update this doc

## Template references

All proofs follow patterns from
`PolyDistributiveLaw.lean`:

| GSOS proof | Template | Lines | Est. |
| ---------- | -------- | ----- | ---- |
| counit | `polyDistLaw_counit` | 280-294 | done |
| unit | `polyDistLaw_unit` | 334-480 | done |
| naturality | `polyDistLaw_nat` | 474-940 | ~250 |
| comul | `polyDistLaw_comul` | 959-1500 | ~450 |
| mul | `polyDistLaw_mul` | 1630-2410 | ~650 |
| packaging | final section | 2463-2567 | ~60 |
