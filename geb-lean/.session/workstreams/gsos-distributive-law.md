# GSOS Distributive Law

## Status: Comultiplication coherence in progress

## Current build state

File: `GebLean/PolyGSOS.lean` (~2070 lines, four
underscore holes for comultiplication sub-lemmas)

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

### NatTrans packaging (done)

- `polyGSOSDistLawNatApp`: type alias
- `polyGSOSDistLawNat_naturality`: naturality proof
- `polyGSOSDistLawNat`: NatTrans definition

### Comultiplication coherence infrastructure (done)

- `polyGSOSDistLaw_comul_annot_eq`: T_P(eps o delta) = id
- `polyGSOSDistLaw_comul_lhsCoalg`: reindexed coalgebra
- `polyCoalgToScaleCoalgStrLeft`,
  `polyCoalgToScaleCoalgStr_comm`,
  `polyCoalgToScaleCoalgStr`,
  `polyCoalgToScaleCoalg`: convert Q-coalgebra to
  polyScale coalgebra
- `polyCoalgUnit_eq_polyCofixUnfold_approx`,
  `polyCoalgUnit_eq_polyCofixUnfold`: bridge lemma
  (delta = polyCofixUnfold of scale coalgebra)
- `polyGSOSDistLaw_comul_srcCoalgStrAt`,
  `polyGSOSDistLaw_comul_srcCoalgStrLeft`,
  `polyGSOSDistLaw_comul_srcCoalgStr`,
  `polyGSOSDistLaw_comul_srcCoalg`: source coalgebra
  from which both sides are anamorphisms
- `polyGSOSDistLaw_comul_rhs_hom`: lambda_A is
  coalgebra morphism from srcCoalg to
  polyCoalgToScaleCoalg (RHS path)
- `polyGSOSFoldQIndex_eq_delta`: Q-index invariance
  under T_P(delta)
- `GSOSDeltaFreeMap`, `GSOSDeltaQMap`: type aliases

## Remaining phases

### Phase CM: Comultiplication coherence (in progress)

#### Strategy: `polyCofixUnfold_precomp` at morphism level

The previous approximation-level induction strategy
(from the P=Q template) was abandoned because the
induction hypothesis does not match the Q-children
structure when P != Q. The GSOS fold at DQ(A) applied
to T_P(delta)(t) produces Q-children in T_P(DQ(DQA)),
which are NOT of the form T_P(delta)(something) that
the IH requires.

The new strategy expresses both sides of the
comultiplication equation as `polyCofixUnfold(srcCoalg)`:

**RHS path** (done):

```text
lambda_A >> delta_{TA}
= lambda_A >> polyCofixUnfold(polyCoalgToScaleCoalg)
    [by polyCoalgUnit_eq_polyCofixUnfold]
= polyCofixUnfold(srcCoalg)
    [by polyCofixUnfold_precomp with rhs_hom]
```

**LHS path** (in progress):

```text
T_P(delta_A) >> lambda_{DQA} >> DQ(lambda_A)
= T_P(delta_A) >> polyCofixUnfold(lhsCoalg)
    [by polyScaleReindex]
= polyCofixUnfold(srcCoalg)
    [by polyCofixUnfold_precomp with lhs_hom]
```

Both sides = `polyCofixUnfold(srcCoalg)`. QED.

#### Current underscore holes (four)

All four have correct type signatures; see line numbers
in PolyGSOS.lean.

##### CM-A: `polyGSOSFoldLeafAt_snd_natural_delta`

Statement: Q-eval of the GSOS fold leaf case is
natural under delta (polyCoalgUnit).

```text
Q.map(T_P(delta)).left
  (polyGSOSFoldLeafAt A P Q d).val.2 =
(polyGSOSFoldLeafAt DQA P Q (delta(d))).val.2
```

Proof approach: Analogous to
`polyGSOSFoldLeafAt_snd_natural` but with delta
replacing polyCofreeMap. Requires showing:

1. Q-index: `head(d).snd = head(delta(d)).snd`.
   Uses `polyCoalgUnit_head_snd` (PolyAlg:6868).
2. Q-children: `T_P(delta)(polyFreeMPure(child_d_e))`
   = `polyFreeMPure(delta(child_d_e))`.
   Since polyFreeMPure is natural (leaf of T_P),
   this is `polyFreeMPure(delta(child_e))`. Need
   `child_{delta(d)}(e) = delta(child_d(e))` from
   the anamorphism equation for polyCoalgUnit.

Helper lemmas needed:

- `polyCoalgUnit_head_snd` (exists, PolyAlg:6868)
- `polyCoalgUnit_children_heq` or
  `polyCoalgUnitAt_children_heq` (may exist at
  PolyAlg:7170)

Estimated size: ~60 lines.

##### CM-B: `polyGSOSFoldQeval_natural_delta`

Statement: Full Q-eval naturality under delta.

```text
Q.map(T_P(delta)).left
  (polyGSOSFoldCataWithFiber A P Q rho t).val.val.2 =
(polyGSOSFoldCataWithFiber DQA P Q rho
  (T_P(delta)(t))).val.val.2
```

Proof approach: By induction on tree `t`:

- Leaf case: dispatch to CM-A.
- Node case: Same pipeline chain as
  `polyGSOSFoldNodeAt_snd_natural`. The pipeline
  sub-lemmas (`polyFreeMJoinEval_natural`,
  `polyBetweenComp_eval_toFun_natural`,
  `polyBetweenComp_eval_invFun_natural`,
  `morphEvalAt_ccrEvalMap_comm`,
  `overPullbackToIdQEval_comm`) are all stated for
  generic morphisms and work for T_P(delta) =
  GSOSDeltaFreeMap.

  Sub-lemma needed for Step 6 (children):
  `polyGSOSFoldFst_natural` analog for delta.

Estimated size: ~120 lines (leaf ~5, node ~115).

##### CM-C: `polyGSOSDistLaw_comul_lhs_hom`

Statement: T_P(delta_A) is a coalgebra morphism from
srcCoalg to lhsCoalg.

```text
srcCoalg.str >> Scale.map(T_P(delta_A))
= T_P(delta_A) >> lhsCoalg.str
```

Proof approach: `Over.OverMorphism.ext`, `funext`,
then induction on tree `t`. At each element `(x, t)`,
the equation decomposes via `Sigma.ext` into:

1. Annotation: `lambda_A(t) = lambda_A(t)`.
   Uses `polyGSOSDistLaw_comul_annot_eq` to show
   T_P(eps)(T_P(delta)(t)) = t.
2. Q-index: `polyGSOSFoldQIndex(A, t) =
   polyGSOSFoldQIndex(DQA, T_P(delta)(t))`.
   Uses `polyGSOSFoldQIndex_eq_delta`.
3. Q-children: `T_P(delta)(qChildren_A(t, e)) =
   qChildren_DQA(T_P(delta)(t), e')`.
   Uses `polyGSOSFoldQeval_natural_delta` (CM-B)
   via `polyBetweenEvalMap_mor_apply`.

Structure follows `polyGSOSScaleCoalg_morphism_h`
(lines 1440-1596, used for naturality).

Estimated size: ~150 lines.

##### CM-D: `polyGSOSDistLaw_comul`

Statement: Full comultiplication coherence.

Proof approach (assembly via polyCofixUnfold_precomp):

```lean
have lhs_eq1 :=
  polyScaleReindex
    (polyFreeMCarrier DQA P) (DQ(TA)) Q
    lambda_A
    (polyGSOSScaleCoalg DQA P Q rho)
-- gives: lambda_{DQA} >> DQ(lambda_A)
--      = polyCofixUnfold(lhsCoalg)

have lhs_eq2 :=
  polyCofixUnfold_precomp
    (polyScale (DQ(TA)) Q)
    srcCoalg lhsCoalg
    ⟨T_P(delta_A), lhs_hom⟩
-- gives: T_P(delta) >> polyCofixUnfold(lhsCoalg)
--      = polyCofixUnfold(srcCoalg)

have rhs_eq1 :=
  polyCoalgUnit_eq_polyCofixUnfold Q
    (polyCofreeCoalg TA Q)
-- gives: delta_{TA}
--      = polyCofixUnfold(polyCoalgToScaleCoalg)

have rhs_eq2 :=
  polyCofixUnfold_precomp
    (polyScale (DQ(TA)) Q)
    srcCoalg
    (polyCoalgToScaleCoalg Q (polyCofreeCoalg TA Q))
    ⟨lambda_A, rhs_hom⟩
-- gives: lambda_A >> polyCofixUnfold(polyCoalgToSC)
--      = polyCofixUnfold(srcCoalg)

simp only [polyGSOSDistLawMor]
rw [lhs_eq1, lhs_eq2, rhs_eq1, rhs_eq2]
```

Estimated size: ~35 lines.

#### Execution plan

1. Fill CM-D first (assembly) to verify the overall
   structure, assuming CM-A/B/C as underscores.
2. Fill CM-A (leaf Q-eval under delta).
3. Fill CM-B (full Q-eval under delta), dispatching
   leaf to CM-A and using pipeline sub-lemmas for
   node.
4. Fill CM-C (coalgebra morphism), using CM-B.
5. Build and verify: `lake build GebLean.PolyGSOS`.

For each sub-lemma, use the factoring-out-lemmas
technique:

1. Replace remaining body with underscore
2. Examine context and goal
3. Factor out named intermediate lemmas (OUTSIDE
   the main proof) with underscore bodies
4. Complete the main proof using the lemmas
5. Then fill in the lemmas one at a time
6. Recurse if any sub-lemma exceeds ~30 lines

---

### Phase MU: Multiplication coherence (~550 lines)

Statement:

```text
mu_{D_Q(A)} >> dist_A =
  T_P(dist_A) >> dist_{T_P(A)} >> D_Q(mu_A)
```

Both sides map `T_P(T_P(D_Q(A))) -> D_Q(T_P(A))`.

Architecture: Express both sides as anamorphisms from
`polyScale(T_P(A), Q)`-coalgebras on
`T_P(T_P(D_Q(A)))`, then show they are the unique
coalgebra morphism using `polyCofixUnfold_precomp`.

The source coalgebra embeds fold Q-children via
`polyFreeUnit` (eta) so that `Scale.map(mu)` recovers
them via `mu o eta = id` (monad left unit law). This is
the design choice from the P=Q template.

Template: `polyDistLaw_mul` in PolyDistributiveLaw.lean
(lines 1630-2410).

#### MU-1: Source coalgebra definition (~80 lines)

##### MU-1a: `polyGSOSDistLaw_mul_srcCoalgStrAt`

Given `t : PolyFreeM (polyFreeMCarrier DQ P) P x`
(a tree in `T_P(T_P(D_Q(A)))`), produce a
`polyBetweenEvalFamily X X (polyScale TA Q) TTDQ x`:

```text
let mu_t := polyFreeMJoinMor DQ P t
let foldResult := polyGSOSFoldCataWithFiber A P Q
  rho mu_t
let annot := polyFreeMapAt DQ A P eps_Q x mu_t
let qIdx := foldResult.val.val.2.1
let qChildren := fun e =>
    polyFreeMPure ... (foldResult.val.val.2.2.left e)
return ((annot, qIdx), qChildren_mor)
```

##### MU-1b through MU-1e

Package as `PolyCoalg (polyScale TA Q)`.

**Dependencies**: `polyGSOSFoldCataWithFiber`,
`polyFreeMJoinMor`, `polyFreeMapAt`.

#### MU-2: RHS coalgebra (~10 lines)

```text
polyGSOSDistLaw_mul_rhsCoalg :=
  polyScaleReindexCoalg TTA TA Q mu_A
    (polyGSOSScaleCoalg TA P Q rho)
```

#### MU-H: mu naturality at eps_Q (~25 lines)

`T_P(eps_Q)(mu_{DQ}(t)) =
  mu_A(T_P(T_P(eps_Q))(t))`

Check whether `polyFreeMJoinMor_nat`
(PolyDistributiveLaw:1708) already provides this.

#### MU-3: mu coalgebra morphism (~150 lines)

mu is coalgebra morphism from srcCoalg to the GSOS
scale coalgebra at A. Uses monad left unit
`mu(eta(child)) = child` for Q-children.

#### MU-4: T_P(dist) coalgebra morphism (~250 lines)

T_P(dist) is coalgebra morphism from srcCoalg to
rhsCoalg. Uses `polyCofixUnfold_coalg_comm` and
counit coherence.

#### MU-5: Assembly (~50 lines)

```lean
have lhs := polyCofixUnfold_precomp _ src dst
  ⟨mu, mu_hom⟩
have rhs1 := polyScaleReindex ...
have rhs2 := polyCofixUnfold_precomp _ src rhs
  ⟨T(dist), tdist_hom⟩
rw [lhs, rhs1, rhs2]
```

Template: lines 2354-2410.

---

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
  unit := ... polyGSOSDistLaw_unit ...
  counit := ... polyGSOSDistLaw_counit ...
  mul := ... polyGSOSDistLaw_mul ...
  comul := ... polyGSOSDistLaw_comul ...
```

#### PK-2: `polyGSOSOperationalMonad` (~5 lines)

```lean
def polyGSOSOperationalMonad ... :=
  liftedMonad (polyGSOSDistributiveLaw P Q rho)
```

#### PK-3: Full build and test

```bash
lake build && lake test
```

---

## Implementation order summary

| Phase | Lemma | Lines | Status |
| ----- | ----- | ----- | ------ |
| N | NatTrans packaging | ~30 | done |
| CM-inf | Comul infrastructure | ~400 | done |
| CM-A | Leaf Q-eval delta | ~60 | stub |
| CM-B | Full Q-eval delta | ~120 | stub |
| CM-C | lhs coalg morphism | ~150 | stub |
| CM-D | Comul assembly | ~35 | stub |
| MU-1 | Src coalgebra | ~80 | pending |
| MU-2 | RHS coalgebra | ~10 | pending |
| MU-H | mu nat at eps | ~25 | pending |
| MU-3 | mu_hom_h | ~150 | pending |
| MU-4 | tdist_hom_h | ~250 | pending |
| MU-5 | Assembly | ~50 | pending |
| PK-1 | DistributiveLaw | ~40 | pending |
| PK-2 | Operational monad | ~5 | pending |
| | **Total remaining** | **~975** | |

## Resumption guide

When resuming after compaction/restart:

1. Run `lake build GebLean.PolyGSOS 2>&1 | head -20`
   to see current errors
2. Check `git log --oneline -5` for last commit
3. Find the next uncompleted step in this document
4. For each step, use the underscore technique:
   write signature with `_` body, build, check goal,
   fill in
5. After completing a phase, commit and update this doc

### Current state (for resumption)

The file has four underscore holes at:

- `polyGSOSFoldLeafAt_snd_natural_delta` (CM-A)
- `polyGSOSFoldQeval_natural_delta` (CM-B)
- `polyGSOSDistLaw_comul_lhs_hom` (CM-C)
- `polyGSOSDistLaw_comul` (CM-D)

All four have correct type signatures (confirmed by
build producing only "don't know how to synthesize
placeholder" errors).

The execution order is: CM-D first (assembly, to
verify structure), then CM-A, CM-B, CM-C.

The old approximation-level approach (induction on
depth n, case-split on tree structure) was ABANDONED
because the IH for the node case does not apply to
Q-children. The Q-children from the GSOS fold at
DQ(A) applied to T_P(delta)(t) live in
T_P(DQ(DQA)), which are not of the form
T_P(delta)(something) that the IH needs.

## Techniques

### Factoring-out-lemmas (from CLAUDE.md)

For any proof > ~30 lines:

1. Identify a good intermediate goal
2. Factor out two lemmas: (a) current state implies
   intermediate, (b) intermediate implies final goal
3. Implement both as underscores
4. Dispatch overall goal by combining with transitivity
5. Prove each lemma separately
6. Recurse if still too large

### polyCofixUnfold_precomp assembly pattern

```lean
have lhs := polyCofixUnfold_precomp _ src dst
  ⟨f, hom_h⟩
have rhs1 := polyScaleReindex ...
have rhs2 := polyCofixUnfold_precomp _ src rhs
  ⟨g, hom_h'⟩
simp only [polyGSOSDistLawMor]
rw [lhs, rhs1, rhs2]
```

### Coalgebra morphism proof pattern

For `polyGSOSDistLaw_comul_lhs_hom` and similar:

```lean
apply Over.OverMorphism.ext
funext ⟨x, t⟩
simp only [Over.comp_left, types_comp_apply]
induction t with
| mk y idx children ih =>
  match idx with
  | Sum.inl leaf => [leaf case]
  | Sum.inr p => [node case]
```

Each case decomposes via:

```lean
congr 1; congr 1
· [annotation equality]
· apply polyBetweenFamily_mor_heq ...
  [Q-children HEq]
```

### Sigma extraction pattern

```lean
obtain ⟨rfl, h2⟩ := Sigma.mk.inj h
obtain ⟨rfl, h3⟩ := Sigma.mk.inj (eq_of_heq h2)
```

## Template references

All proofs follow patterns from
`PolyDistributiveLaw.lean`:

| GSOS proof | Template | Lines | Est. |
| ---------- | -------- | ----- | ---- |
| counit | `polyDistLaw_counit` | 280-294 | done |
| unit | `polyDistLaw_unit` | 334-480 | done |
| naturality | `polyDistLaw_nat` | 474-940 | done |
| comul | `polyDistLaw_comul` | 959-1500 | ~350 |
| mul | `polyDistLaw_mul` | 1630-2410 | ~550 |
| packaging | final section | 2463-2567 | ~60 |

## Helper lemma reference

### From PolyAlg.lean

| Lemma | Line | Use |
| ----- | ---- | --- |
| `polyCofixApprox_intro_polyScale_congr` | 514 | -- |
| `polyCofixUnfoldApprox_input_heq` | 498 | -- |
| `polyCofixUnfold_coalg_comm` | 2085 | MU-4 |
| `polyCofixUnfold_coalg_comm_child_fst_eq` | 1646 | -- |
| `polyCofixUnfoldAt_children_heq` | 1824 | CM-C |
| `polyCofreeMapApprox` | 6175 | -- |
| `polyCoalgUnitApprox` | 6695 | -- |
| `polyCoalgUnit_head` | 6849 | CM-A |
| `polyCoalgUnit_head_snd` | 6868 | CM-A |
| `polyCoalgUnit_family_eq` | 6888 | CM-A |
| `polyCoalgUnitAt_children_heq` | 7170 | CM-A |
| `polyCofreeCounit_naturality` | 6658 | MU-4a |

### From PolyDistributiveLaw.lean

| Lemma | Line | Use |
| ----- | ---- | --- |
| `polyScaleReindex_approx` | 851 | -- |
| `polyScaleReindex` | 880 | CM-D, MU-5 |
| `polyCofixUnfold_precomp` | 1688 | CM-D, MU-5 |
| `polyFreeMJoinMor` | 1542 | MU-1 |
| `polyFreeMJoinMor_nat` | 1708 | MU-H |

### From PolyGSOS.lean (existing)

| Lemma | Use |
| ----- | --- |
| `polyGSOSDistLaw_counit` | MU-4a |
| `polyGSOSDistLaw_unit_approx` | -- |
| `polyGSOSDistLaw_comul_annot_eq` | CM-C |
| `polyGSOSFoldQIndex_eq` | MU-3 |
| `polyGSOSFoldQIndex_eq_delta` | CM-C |
| `polyGSOSFoldQeval_natural` | MU-4 |
| `polyBetweenEvalMap_mor_apply` | CM-C, MU-4 |
| `polyGSOSFoldCata_snd_fst_eq` | MU-3 |
| `polyGSOSScaleCoalg_morphism_h` | template |
| `polyGSOSDistLaw_comul_rhs_hom` | CM-D |
| `polyCoalgUnit_eq_polyCofixUnfold` | CM-D |
