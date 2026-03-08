# GSOS Distributive Law

## Status: Multiplication coherence pending

## Current build state

File: `GebLean/PolyGSOS.lean` (~2640 lines, compiles
cleanly with no warnings)

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

### Phase CM: Comultiplication coherence (done)

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

**LHS path** (done):

```text
T_P(delta_A) >> lambda_{DQA} >> DQ(lambda_A)
= T_P(delta_A) >> polyCofixUnfold(lhsCoalg)
    [by polyScaleReindex]
= polyCofixUnfold(srcCoalg)
    [by polyCofixUnfold_precomp with lhs_hom]
```

Both sides = `polyCofixUnfold(srcCoalg)`. QED.

#### Completed sub-lemmas

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

### Phase MU: Multiplication coherence (~400 lines)

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
them via `mu o eta = id` (monad left unit law).

Template: `polyDistLaw_mul` in PolyDistributiveLaw.lean
(lines 1630-2410).

Lessons from comul coherence:

- The polyCofixUnfold_precomp assembly pattern is
  straightforward (~35 lines).
- Coalgebra morphism proofs decompose into annotation +
  qIdx + qChildren via Sigma.ext + Prod.ext.
- For nodes, polyGSOSFoldCata_snd_fst_eq gives rfl, so
  polyGSOSFoldQIndex is definitionally equal to the raw
  .2.snd.fst, simplifying qIdx proofs.
- The pipeline naturality sub-lemmas are generic in the
  morphism and can be reused.

#### MU-1: Source coalgebra definition (~80 lines)

##### MU-1a: `polyGSOSDistLaw_mul_srcCoalgStrAt` (done)

At `t : T_P(T_P(D_Q(A)))`, produces
`polyScale(T_P(A), Q)` element:

- annotation: `T_P(eps_Q)(mu(t))`
- Q-eval: from `polyGSOSFoldCataWithFiber A P Q rho
  (mu(t))`, with fiber transport
- Q-children: fold Q-children composed with eta
  (`polyFreeUnit TDQ P`)

##### MU-1b through MU-1e

Package as `PolyCoalg (polyScale TA Q)`:
`srcCoalgStrLeft`, `srcCoalgStr_comm`, `srcCoalgStr`,
`srcCoalg`.

#### MU-2: RHS coalgebra (~10 lines)

```lean
polyGSOSDistLaw_mul_rhsCoalg :=
  polyScaleReindexCoalg ... mu_A
    (polyGSOSScaleCoalg TA P Q rho)
```

where `mu_A = polyFreeCounitFold P (polyFreeAlg A P)`.

#### MU-H: Monad left unit (~15 lines)

`polyFreeMJoinMor DQ P (polyFreeMPure TDQ P v) = v`

This is `mu(eta(v)) = v`, needed for mu_hom_h.
Might exist as `polyFreeM_pure_bind` or similar.

#### MU-3: mu coalgebra morphism (~50 lines)

mu is coalgebra morphism from srcCoalg to
`polyGSOSScaleCoalg A P Q rho`.

Revised estimate: much simpler than originally planned.
Both sides compute fold(mu(t)) for annotation and
Q-eval. The only difference is Q-children:

- LHS: `fold.qChildren >> eta >> mu`
- RHS: `fold.qChildren`

By monad left unit `eta >> mu = id`, these are equal.
No induction on tree structure needed — the proof
works for all t uniformly.

#### MU-4: T_P(dist) coalgebra morphism (~200 lines)

T_P(dist_A) is coalgebra morphism from srcCoalg to
rhsCoalg. This is the hardest sub-lemma.

Goal: `srcCoalg.str >> Scale.map(T_P(lambda_A)) =
  T_P(lambda_A) >> rhsCoalg.str`

Requires relating `fold_A(mu(t))` to
`fold_{TA}(T_P(lambda_A)(t))` at the Q-eval level.

Current status: The proof decomposes into leaf + node.
Leaf case is done. Node case decomposes via `congr`
into annotation + qidx + qchildren. Annotation is
done. The qidx and qchildren branches are factored
into separate lemmas with underscore bodies:

- `polyGSOSDistLaw_mul_tdist_node_qidx`
- `polyGSOSDistLaw_mul_tdist_node_qchildren`

##### MU-4 qidx plan

Goal (readable):

```lean
srcQEvalAt(node(p, children)).fst =
  polyGSOSFoldNodeAt(TA, pbefMk p rhsChildMor)
    .val.2.snd.fst
```

Both sides run the `polyGSOSFoldNodeAtGen` pipeline
with `pbefMk p childMor` and extract the Q-index.
The Q-index is:

```lean
((rho.rule x).base ⟨p, pf'⟩).fst
```

where `pf'(eg)` is a function mapping each P-direction
to the child Q-index at that direction. The function
`pf'` differs between LHS and RHS:

- LHS: child Q-index from `srcQEvalAt(children eg)`
- RHS: child Q-index from
  `polyGSOSFoldCataWithFiber(polyFreeMapAt(lam, eg))`

These agree by `ih`. The Q-index reduction chain is:

1. `.val.2.snd.fst` on `polyGSOSFoldNodeAtGen` =
   `qAtTb.fst` (by Subtype/Prod/Sigma projections)
2. `qAtTb.fst = qAtTpTb.fst` (by ccrEvalMap def)
3. `qAtTpTb.fst = rhoResult.1.1`
   (by fiberEquiv_toFun def)
4. `rhoResult.1 = ccrReindex(rho.rule x, compInput)`
   (by polyBetweenMorphEvalAt def)
5. The `.1` of ccrReindex result is the Q-index

Steps 1-5 are all definitional (Sigma/Subtype fst on
constructors), so Lean should reduce them via `dsimp`.

Proof steps:

1. Unfold `srcQEvalAt` and `polyGSOSFoldNodeAt` to
   expose `polyGSOSFoldNodeAtGen` on both sides
2. Use `dsimp` or `simp` selectively on index-
   extraction definitions (ccrEvalMap, fiberEquiv_toFun,
   polyBetweenMorphEvalAt, fiberEquiv_invFun,
   overPullbackToIdQEval) to reduce `.fst` chain
3. After reduction, both sides should be
   `((rho.rule x).base ⟨p, pf'⟩).fst`
4. `congr 1` + `funext eg` to get per-child qidx
5. Use `ih(eg)` (extracting .fst component) to close

If step 2 makes the goal unreadable, factor out a
helper `polyGSOSFoldNodeAtGen_qidx_eq` that states
the Q-index in terms of the child Q-indices.

##### MU-4 qchildren plan (revised)

Goal (readable):

```lean
srcQEvalAt(node).snd ≫ Over.homMk(T(lam)) ≍
  polyGSOSFoldNodeAt(TA, pbefMk p rhsChildMor)
    .val.2.snd.snd
```

HEq between Q-children morphisms. Source types
agree by qidx.

Strategy: 6-step pipeline push (generalized version
of `polyGSOSFoldNodeAt_snd_natural`), with a new
"fold preserves tree" lemma for the children step.

###### Lemma A: polyGSOSFoldCata_fst_eq (~20 lines)

Location: after polyGSOSFoldCataWithFiber (~line 490)

Statement: `fold(A, t).val.val.1 = ⟨x, t⟩`

Proof: induction on t.

- Leaf: fst = `⟨x, polyFreeMPure(leaf)⟩`. The
  original tree t is `PolyFix.mk x (Sum.inl ...) ch`.
  polyFreeMPure creates a PolyFix.mk with the same
  index and an empty-family children function. Since
  the family at Sum.inl is empty, `ch` and the
  pure's children are equal by funext over the empty
  type. So fst.2 = t.
- Node: fst = `⟨x, node(p, d ↦ fold(ch d).fst.2)⟩`.
  By IH, `fold(ch d).fst = ⟨x_d, ch d⟩`, so
  `fold(ch d).fst.2 = ch d`. Hence fst = ⟨x, t⟩.

###### Lemma B: polyGSOSFoldNodeAtGen_snd_natural (~80 lines)

Location: near polyGSOSFoldNodeAt_snd_natural

Statement: For `g : B1 ⟶ B2`, if per-P-dir:
`overPullbackMap(T(g), Q(T(g)))(childMor1 d) =
  childMor2 d`
then:
`Q(T(g)).left(polyGSOSFoldNodeAtGen(B1, ...).val.2) =
  polyGSOSFoldNodeAtGen(B2, ...).val.2`

Proof: same 6-step pipeline push as
polyGSOSFoldNodeAt_snd_natural:

1. Join: polyFreeMJoinEval_natural
2. toFun: polyBetweenComp_eval_toFun_natural
3. rho: morphEvalAt_ccrEvalMap_comm
4. invFun: polyBetweenComp_eval_invFun_natural
5. prodComp: overPullbackToIdQEval_comm
6. Children: congr + Over.OverMorphism.ext + funext +
   hypothesis

###### Lemma C: polyGSOSFoldMul_child_pullback_eq (~30 lines)

Location: near qchildren lemma

Statement: per-P-dir d,
`overPullbackMap(T(lam), Q(T(lam)))
  (childMor_LHS d) = childMor_RHS d`

Proof: Subtype.ext + Prod.ext

- fst: polyGSOSFoldCata_fst_eq (Lemma A)
- snd: extract Q-eval from ih(d) via Scale
  component projections

###### Closing qchildren (~15 lines)

Apply Lemma B with B1=TDQ, B2=DQTA, g=lam,
children condition from Lemma C. Get full .2
equality. Extract .snd (Q-children) using hqidx
for type agreement.

#### MU-5: Assembly (~40 lines)

```lean
have lhs := polyCofixUnfold_precomp _ src
  (polyGSOSScaleCoalg A) ⟨mu, mu_hom⟩
have rhs1 := polyScaleReindex ... mu_A
  (polyGSOSScaleCoalg TA)
have rhs2 := polyCofixUnfold_precomp _ src rhs
  ⟨T(dist), tdist_hom⟩
simp only [polyGSOSDistLawMor]
exact (lhs.trans rhs2.symm).trans
  (congrArg ... rhs1)
```

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
| CM-A | Leaf Q-eval delta | ~60 | done |
| CM-B | Full Q-eval delta | ~120 | done |
| CM-C | lhs coalg morphism | ~150 | done |
| CM-D | Comul assembly | ~35 | done |
| MU-1a | Src coalg StrAt | ~30 | done |
| MU-1b | Src coalg packaging | ~50 | pending |
| MU-2 | RHS coalgebra | ~10 | pending |
| MU-H | Monad left unit | ~15 | pending |
| MU-3 | mu_hom_h | ~50 | pending |
| MU-4 | tdist_hom_h | ~200 | in progress |
| MU-5 | Assembly | ~40 | pending |
| PK-1 | DistributiveLaw | ~40 | pending |
| PK-2 | Operational monad | ~5 | pending |
| | **Total remaining** | **~465** | |

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

Phase MU (multiplication coherence) is in progress.
MU-1 through MU-3 are done. MU-4 (tdist coalgebra
morphism) is partially done:

- Leaf case: done
- Node annotation branch: done
- Node qidx branch: done
  (`polyGSOSDistLaw_mul_tdist_node_qidx`, compiling)
- Node qchildren branch: in progress
  (`polyGSOSDistLaw_mul_tdist_node_qchildren`).
  Partial proof reduces to per-element goal via
  heq_of_cast_eq + Over.OverMorphism.ext + funext.
  Requires: polyGSOSFoldCata_fst_eq (new),
  polyGSOSFoldNodeAtGen_snd_natural (new),
  polyGSOSFoldMul_child_pullback_eq (new).
  See "MU-4 qchildren plan (revised)" above.

The main proof `polyGSOSDistLaw_mul_tdist_node` is
clean (no warnings) — it dispatches to the three
factored lemmas.

File: `GebLean/PolyGSOS.lean` (~4200 lines, 2 errors
from `_` placeholders in qidx and qchildren lemmas).

## Structural observations

### polyScaleFamily ignores annotation

`polyScaleFamily A Q x (annotation, qi) =
  polyBetweenFamily X X Q x qi`

The Scale family depends only on the Q-index `qi`, NOT
on the annotation.  This means a projection
`⟨(a, qi), qmor⟩ ↦ ⟨qi, qmor⟩` from Scale evaluations
to Q evaluations is well-typed.  Use `congrArg` with
this projection on a Scale equality from `ih` to extract
Q-eval equalities needed for children conditions.

### polyFreeMap_comm is rfl

`polyFreeMap_comm A B P f = rfl`, so
`polyFreeMap = Over.homMk polyFreeMapLeft rfl`
definitionally.  This simplifies goals involving
`polyFreeMap` since the commutativity proof disappears.

### ccrEvalMap preserves index

`ccrEvalMap f ⟨i, h⟩ = ⟨i, h ≫ f⟩` — preserves
the sigma index, only post-composes the morphism.

### polyGSOSFoldNodeAtGen_qeval_natural

The generalized pipeline Q-eval naturality lemma
(Lemma B at ~line 1657) works for any carrier morphism
`g : B1 ⟶ B2`.  It requires a children condition:
per-P-dir, `overPullbackMap(T(g), Q(T(g)))(node1 d) =
  node2 d`.

To close qchildren: apply Lemma B with g = lam,
then supply the children condition (Lemma C) which
decomposes into:

- fst (tree): polyGSOSFoldCata_fst_eq (Lemma A)
- snd (Q-eval): extract from ih via Scale→Q projection

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
