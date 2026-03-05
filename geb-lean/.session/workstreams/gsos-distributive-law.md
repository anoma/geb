# GSOS Distributive Law

## Status: Naturality coalgebra morphism proof in progress

## Current build state

File: `GebLean/PolyGSOS.lean` (883 lines)

Architecture change: replaced depth-indexed
`polyGSOSDistLaw_naturality_approx` with a coalgebra
morphism approach using `polyCofixUnfold_precomp` and
`polyScaleReindex`.

`polyGSOSDistLaw_naturality` compiles given the coalgebra
morphism lemma `polyGSOSScaleCoalg_morphism_h`.

Two unsolved goals in `polyGSOSScaleCoalg_morphism_h`:

1. Leaf case (line 842, `Sum.inl` branch): the scale
   coalgebra structure on a pure leaf (wrapping cofree
   element d) must commute with mapping.  The goal is
   an equality of Scale evaluations (nested Sigma pairs
   `⟨y, ((annot, qidx), qchildren)⟩`).

   Annotation: `polyCofreeExtract_mapAt_val`
   (use `congrArg (Sigma.mk y)` then
   `congrArg (polyFreeMPure _ P ·)` then
   `Subtype.ext`).

   Q-index: `polyCofreeMapAt_head_snd`.

   Q-children: the A-side children composed with
   `polyFreeMap(polyCofreeMap f)` vs B-side children.
   Use `polyBetweenFamily_mor_heq`, `funext_heq`,
   then per-direction: the LHS is `polyFreeMPure` of
   `polyCofreeMapLeft f (cofreeChild A e1)` and the
   RHS is `polyFreeMPure` of `cofreeChild B e2`.
   Close with `polyCofreeMapAt_children_heq` +
   `polyFreeMPure_proof_irrel`.

2. Node case (line 843, `Sum.inr p` branch): the scale
   coalgebra structure on a P-node must commute with
   mapping.  The IH gives the coalgebra morphism
   condition for each P-child direction.  Needs:

   Annotation: `polyGSOSDistLaw_annot_natural`.

   Q-index: `polyGSOSFoldQIndex_eq`.

   Q-children: the GSOS pipeline (prodComp ->
   comp\_eval -> rho.rule -> comp\_eval -> join) must
   commute with mapping given per-P-child fold
   naturality (from IH).  This is the hardest part.

## Completed

### PolyGSOSRule structure (PolyGSOS.lean)

- `PolyGSOSRule P Q`: a GSOS rule as a polynomial morphism
  `P . (Id x Q) --> Q . T_P`
- `polyIdBehaviorPoly Q`: the identity-behavior product polynomial

### Fold algebra (PolyGSOS.lean)

- `polyGSOSFoldLeafAt`: leaf handler mapping cofree elements
  to product pairs via eta and Q(eta)(str)
- `polyGSOSFoldNodeAt`: node handler applying the GSOS rule
  pipeline: prodComp -> comp\_eval -> rho -> comp\_eval -> Q(join)
- `polyGSOSFoldCataWithFiber`: recursive catamorphism with fiber
  preservation proof
- `polyGSOSFoldCata`: fold as an Over X morphism

### Distributive law morphism (PolyGSOS.lean)

- `polyGSOSScaleCoalgStrAt`: polyScale(T\_P(A), Q)-coalgebra
  combining T\_P(epsilon\_Q) annotation with fold's Q-structure
- `polyGSOSDistLawMor`: the distributive law
  T\_P(D\_Q(A)) -> D\_Q(T\_P(A)) via polyCofixUnfold of the
  scale coalgebra

### Counit coherence (PolyGSOS.lean)

- `polyGSOSDistLawMor_head_fst`: head annotation equals
  T\_P(eps\_Q) applied to input
- `polyGSOSDistLaw_counit`: dist . eps\_{T\_P(A)} = T\_P(eps\_A)

### Unit coherence (PolyGSOS.lean)

- `polyGSOSDistLaw_unit_approx`: depth-indexed unit proof
- `polyGSOSDistLaw_unit`: eta\_{D\_Q(A)} . dist = D\_Q(eta\_A)

### Naturality helpers (PolyGSOS.lean)

- `polyGSOSDistLaw_annot_natural`: annotation naturality
- `polyGSOSFoldCata_snd_fst_eq`: fold Q-fiber equals input fiber
- `polyGSOSNodeQIdx`: carrier-independent Q-index computation
- `polyGSOSFoldQIndex`: Q-index of fold result
- `polyGSOSFoldQIndex_leaf`, `polyGSOSFoldQIndex_node_unfold`,
  `polyGSOSFoldQIndex_eq_node`, `polyGSOSFoldQIndex_eq`:
  Q-index is carrier-independent
- `polyGSOSFoldCata_natural` (incomplete: Prod.snd node case)
- `polyGSOSDistLaw_naturality_approx` (written but not verified
  due to compilation blocked by line 1021)

## Current state (2026-03-05)

### What compiles

- `polyGSOSFoldNodeAt_snd_natural` (line 913): Type
  signature compiles. Inner `rho_nat` helper compiles.
  Main body has underscore at line 1005.
- `polyGSOSFoldQeval_natural` (line 1026): Uses
  `polyGSOSFoldNodeAt_snd_natural` in node case.
  Leaf case proved.
- `polyGSOSScaleCoalg_morphism_h` (line 1080): Leaf
  case proved. Node case has underscore at line 1217 for
  Q-children.
- `polyGSOSDistLaw_naturality` (line 1219): Compiles
  given `polyGSOSScaleCoalg_morphism_h`.

### The Q-children pipeline naturality problem

File `GebLean/PolyGSOS.lean`, lemma
`polyGSOSFoldNodeAt_snd_natural` at line 913.

Goal (at the underscore, line 1005, after `congr 1`):

```
ccrEvalMap freeMap (pipeline_A node_A) = pipeline_B node_B
```

where `pipeline = ccrEvalMap join . toFun . rhoEval .
invFun . ccrEvalMap prodComp` and:

- `node_A = pbefMk p childMor_A` with
  `childMor_A.left e = catA_e.val`
- `node_B = pbefMk p childMor_B` with
  `childMor_B.left e = catB_e.val`
- `catA_e = polyGSOSFoldCataWithFiber A ... (children e)`
- `catB_e = polyGSOSFoldCataWithFiber B ...
  (polyFreeMapAt ... (children e))`

Available hypotheses:

- `ih`: `GSOSQMap.left catA_e.val.val.2 =
  catB_e.val.val.2` (Q-eval naturality per child)
- `h_fst` (to be proved via `polyGSOSFoldFst_natural`):
  `catB_e.val.val.1 = freeMap.left catA_e.val.val.1`
  (fst naturality per child)
- `rho_nat`: `ccrEvalMap freeMap (rhoEval_A ev) =
  rhoEval_B (ccrEvalMap freeMap ev)` (rho naturality)

### Proof plan: push freeMap through the pipeline

The chain of equalities (all at `ccrEval` level):

```
ccrEvalMap freeMap (ccrEvalMap join_A (toFun_A
  (rhoEval_A (invFun_A (ccrEvalMap prodComp_A node_A)))))

= ccrEvalMap (join_A >> freeMap) (toFun_A (...))
  [by ccrEvalMap_comp]

= ccrEvalMap join_B (ccrEvalMap (TP.map freeMap)
    (toFun_A (...)))
  [by join_nat + ccrEvalMap_comp]

= ccrEvalMap join_B (toFun_B (ccrEvalMap freeMap
    (rhoEval_A (...))))
  [by toFun_nat]

= ccrEvalMap join_B (toFun_B (rhoEval_B
    (ccrEvalMap freeMap (invFun_A (...)))))
  [by rho_nat]

= ccrEvalMap join_B (toFun_B (rhoEval_B (invFun_B
    (ccrEvalMap (IQ.map freeMap) (...)))))
  [by invFun_nat]

= ccrEvalMap join_B (toFun_B (rhoEval_B (invFun_B
    (ccrEvalMap prodComp_B node_B))))
  [by children_nat + prodComp_nat]
```

### Sub-lemmas needed

#### S1. children\_nat: childMor\_A >> pullbackMap = childMor\_B

`pullbackMap = overPullbackMap freeMap (Q.map freeMap)`

Proof: `Over.OverMorphism.ext; funext e; Sigma.ext`.
For `.1`: use `polyGSOSFoldFst_natural`.
For `.2`: use `ih`.
The proof of the subtype condition follows from
the Over-morphism `w` properties.

Location in code: inline `have` in proof.

#### S2. prodComp\_nat: prodComp\_A >> IQ.map freeMap = pullbackMap >> prodComp\_B

This is a morphism equation in `Over X`. Prove by
`Over.OverMorphism.ext; funext elem; simp`.

For each pullback element `elem = ((t, qeval), prop)`:
- The y-coordinate matches
- The IQ-index: `(fun | inl _ => PUnit.unit | inr _ =>
  q_idx)` is the same on both sides because
  `ccrEvalMap freeMap` preserves ccrEval indices
- The IQ-morphism: on `inl`, both give `freeMap.left t`;
  on `inr`, both give `freeMap.left (q_mor.left dir)`

Location in code: inline `have` in proof or separate
private lemma.

#### S3. invFun\_nat: ccrEvalMap freeMap . invFun\_A = invFun\_B . ccrEvalMap (IQ.map freeMap)

`invFun = polyBetweenComp_eval_fiberEquiv_invFun`

This holds because `invFun` restructures indices/fibers
without touching the morphism target. Post-composing
with `freeMap` distributes through the restructuring:

- Index: `mor_to_pbe_fiber_index (h >> IQ.map freeMap) eg
  = mor_to_pbe_fiber_index h eg`
  (IQ.map preserves indices)
- Morphism: `(mor_to_pbe_fiber_mor (h >> IQ.map freeMap)
  eg).left ef = freeMap.left
  ((mor_to_pbe_fiber_mor h eg).left ef)`
  (IQ.map post-composes with freeMap)

Proof: `funext ev; obtain ⟨ig, h⟩ := ev; Sigma.ext`
then `Over.OverMorphism.ext; funext`.

Location: separate private lemma (or inline `have`).

#### S4. rho\_nat (already proved)

Existing `have rho_nat` in the proof context.

#### S5. toFun\_nat: ccrEvalMap (TP.map freeMap) . toFun\_A = toFun\_B . ccrEvalMap freeMap

`toFun = polyBetweenComp_eval_fiberEquiv_toFun`

Symmetric to S3. `toFun` restructures composite eval
to factored eval. Post-composing distributes:

- Outer g-index: preserved (same `ig`)
- For each `eg`: f-eval index = `pf eg` (same)
- f-eval morphism: `Over.homMk (fun ef =>
  (mor >> freeMap).left (eg, ef))` on the LHS
  vs `Over.homMk (fun ef => mor.left (eg, ef))
  >> freeMap` on the RHS. Both give
  `freeMap.left (mor.left (eg, ef))`.

Proof: `funext ev; obtain ⟨⟨ig, pf⟩, mor⟩ := ev;
Sigma.ext` then `Over.OverMorphism.ext; funext`.

Location: separate private lemma (or inline `have`).

#### S6. join\_nat: join\_A >> freeMap = TP.map freeMap >> join\_B

`join = Over.homMk (fun (x', evalElem) =>
  (x', polyFreeMBind TDQ DQ P
    (polyFreeMPolyEval_to_polyFreeM TDQ P evalElem)
    (fun _ a => a.prop >> a.val.2))) rfl`

Proof uses two existing lemmas:

1. `polyFreeMPolyEval_to_M_natural` (PolyAlg.lean:8423):
   `polyFreeMapAt TDQ_A TDQ_B P freeMap x'
   (polyFreeMPolyEval_to_polyFreeM TDQ_A P evalElem)
   = polyFreeMPolyEval_to_polyFreeM TDQ_B P
   (ccrEvalMap freeMap evalElem)`

2. Monad multiplication naturality:
   `polyFreeMapAt DQ_A DQ_B P cofreeMap x'
   (polyFreeMBind TDQ_A DQ_A P tree sub_A)
   = polyFreeMBind TDQ_B DQ_B P
   (polyFreeMapAt TDQ_A TDQ_B P freeMap x' tree) sub_B`

   Derivation via monad laws:
   - LHS = `bind tree sub_A >>= pure_cofreeMap`
     [by `polyFreeMapAt_as_bind`]
   - = `bind tree (sub_A >>> pure_cofreeMap)`
     [by `polyFreeM_bind_assoc`]
   - = `bind tree (fun y a =>
     polyFreeMapAt ... cofreeMap _ (sub_A y a))`
     [by `polyFreeMapAt_as_bind` backwards]
   - RHS = `bind (bind tree pure_freeMap) sub_B`
     [by `polyFreeMapAt_as_bind` on tree_B]
   - = `bind tree (pure_freeMap >>> sub_B)`
     [by `polyFreeM_bind_assoc`]
   - = `bind tree (fun y a =>
     sub_B _ (freeMap.left a, ...))`
     [by `polyFreeM_pure_bind`]
   - Both leaf functions produce
     `h >> polyFreeMapAt DQ_A DQ_B P cofreeMap x'' t_A`
     by `polyFreeMapAt_transport` and proof irrelevance.

   Location: separate private lemma
   `gsosJoin_bind_natural` or similar. Or use
   `polyFreeMJoin_natural` (PolyAlg.lean:8366) if the
   bind-based join can be expressed via polyFreeMJoin.

Proof of `join_nat`: `Over.OverMorphism.ext; funext
(x', evalElem)`. Use lemma 1 to rewrite. Use lemma 2
to close.

Location: separate private lemma.

### Existing lemmas to use

| Lemma | File:Line | Purpose |
| ----- | --------- | ------- |
| `ccrEvalMap_comp` | Polynomial:347 | Combine ccrEvalMap compositions |
| `ccrEvalMap_id` | Polynomial:341 | Identity map |
| `polyBetweenMorphEval_natural` | Polynomial:1341 | Morphism eval naturality |
| `polyBetweenComp_eval_fiberEquiv_toFun` | Polynomial:1677 | toFun definition |
| `polyBetweenComp_eval_fiberEquiv_invFun` | Polynomial:1691 | invFun definition |
| `mor_to_pbe_fiber_index` | Polynomial:1250 | Index extraction |
| `mor_to_pbe_fiber_mor` | Polynomial:1259 | Morphism extraction |
| `overPullbackMap` | Utilities/Slice:740 | Pullback map |
| `polyGSOSFoldFst_natural` | PolyGSOS:1028 | Fst component naturality |
| `polyFreeMPolyEval_to_M_natural` | PolyAlg:8423 | Eval-to-tree naturality |
| `polyFreeMJoin_natural` | PolyAlg:8366 | Join naturality |
| `polyFreeMapAt_as_bind` | PolyAlg:5765 | Map as bind |
| `polyFreeM_bind_assoc` | PolyAlg:3494 | Bind associativity |
| `polyFreeM_pure_bind` | PolyAlg:3466 | Pure-bind law |
| `polyFreeMapAt_transport` | PolyAlg:5734 | Transport commutes with map |
| `polyFreeMBind_transport` | PolyAlg:5743 | Transport commutes with bind |
| `Over.OverMorphism.ext` | Utilities | Over morphism extensionality |
| `polyFreeMapAt_comp` | PolyAlg:5825 | Map composition |

## Pending: detailed step-by-step plan

### Phase N: Complete naturality

Architecture: coalgebra morphism approach using
`polyCofixUnfold_precomp` and `polyScaleReindex`.
`polyGSOSDistLaw_naturality` already compiles given the
coalgebra morphism lemma.

#### N1. Complete leaf case of polyGSOSScaleCoalg\_morphism\_h

The leaf tree is `PolyFix.mk y (Sum.inl ⟨⟨y, d⟩, rfl⟩) _`
where `d : PolyCofreeM A Q y`.  The fold produces
`polyGSOSFoldLeafAt`, giving `(eta(d), Q(eta)(str(d)))`.

After `dsimp`, the goal compares (using Sigma structure):

- Annotation: `f.left(polyCofreeExtract A Q d)` vs
  `polyCofreeExtract B Q (polyCofreeMapAt f d)`.
  Use `polyCofreeExtract_mapAt_val`.
- Q-index: `d.head.2` vs `(polyCofreeMapAt f d).head.2`.
  Use `polyCofreeMapAt_head_snd`.
- Q-children: A-side children composed with
  `polyFreeMap(polyCofreeMap f)` vs B-side children.
  Use `polyCofreeMapAt_children_heq` +
  `polyFix_leaf_heq_of_val_eq`.

The nested Sigma/Scale/Subtype structure requires
careful `congr`/`Sigma.ext` decomposition.

Build checkpoint.

#### N2. Complete node case of polyGSOSScaleCoalg\_morphism\_h

The node tree is `PolyFix.mk y (Sum.inr p) children`.
The IH gives the coalgebra morphism condition for each
P-child.  The fold computes Q-structure via the GSOS
pipeline: prodComp -> comp\_eval -> rho.rule ->
comp\_eval -> join.

After `dsimp`, the goal compares:

- Annotation: use `polyGSOSDistLaw_annot_natural`.
- Q-index: use `polyGSOSFoldQIndex_eq`.
- Q-children: the GSOS pipeline must commute with
  mapping.  This is the hardest part.

For Q-children pipeline naturality, the argument is:

1. The `prodComp` step commutes because per-P-child
   products commute (via IH projected to each component).
2. `polyBetweenComp_eval_fiberEquiv` is structural.
3. `rho.rule` commutes by polynomial morphism naturality.
4. `ccrEvalMap join` commutes because free monad bind
   commutes with mapping.

Factor sub-lemmas for each pipeline step if needed.

Build checkpoint.

#### N3. Verify full build

Both leaf and node cases complete => no underscores =>
`lake build GebLean.PolyGSOS` should succeed.

#### N4. Write NatTrans packaging

Three definitions:

- `polyGSOSDistLawNatApp A P Q rho` (type wrapper)
- `polyGSOSDistLawNat_naturality A B P Q rho f`
  (delegates to `polyGSOSDistLaw_naturality` after simp
  with `polyCofreeComonad_map_eq` and `polyFreeMonad_map_eq`)
- `polyGSOSDistLawNat P Q rho` (NatTrans definition)

Template: PolyDistributiveLaw.lean lines 2463-2500.

Build checkpoint: `lake build GebLean.PolyGSOS`.

#### N5. Commit

Message: "GSOS naturality proof and NatTrans packaging"

### Phase CM: Comultiplication coherence

#### CM1. Write abbreviations for nested types

Following the pattern from `polyDistLaw_comul_lhsCoalg` etc.
in PolyDistributiveLaw.lean (lines 992-1051):

- `polyGSOSDistLaw_comul_lhsCoalg A P Q rho`:
  `PolyCoalg (polyScale (polyCofreeCarrier
  (polyFreeMCarrier A P) Q) Q)` --- the
  `polyGSOSScaleCoalg` at `D_Q(A)` reindexed by `dist`
- `polyGSOSDistLaw_comul_rhsCoalg A P Q`:
  `PolyCoalg Q` --- `polyCofreeCoalg (polyFreeMCarrier A P) Q`
- `polyGSOSDistLaw_comul_lhsInput A P Q rho`:
  `T_P(delta_A)(t)` --- polyFreeMapAt by polyCoalgUnit
- `polyGSOSDistLaw_comul_rhsInput A P Q rho`:
  `dist_A(t)` --- polyCofixUnfoldAt of polyGSOSScaleCoalg

Build checkpoint: verify signatures compile.

#### CM2. Write polyGSOSDistLaw\_comul\_annot\_eq

Show: `T_P(eps_Q . D_Q(eps_Q) . delta_Q) = T_P(eps_Q)`.
Uses `polyCofree_left_triangle` (comonad law
`eps . delta = id`) composed with `polyFreeMapAt_comp`.

Template: `polyDistLaw_comul_annot_eq` (line 959, ~20 lines).

Build checkpoint.

#### CM3. Write RHS child equality helper

Like `polyDistLaw_comul_family_eq_node` (line 1117) and
`polyDistLaw_comul_head_snd_node` (line 1084).  These
show that at a node, the children of `dist(node(p,ch))`
(extracted from the cofree M-type) match the expected
recursive structure.

In the GSOS case, the Q-indices come from
`polyGSOSFoldQIndex` rather than from the P-coalgebra
structure directly.  May need GSOS-specific versions.

Build checkpoint.

#### CM4. Write polyGSOSDistLaw\_comul\_approx\_node

Depth-indexed proof for the node case at depth n+1.
Takes IH as parameter.

Strategy: unfold both sides, use
`polyCofixApprox_intro_polyScale_congr`, show annotation
equality via CM2, show Q-index equality, show children
equality via IH.

Template: `polyDistLaw_comul_approx_node`
(line 1149, ~110 lines).

Build checkpoint.

#### CM5. Write polyGSOSDistLaw\_comul\_approx\_leaf

Depth-indexed proof for the leaf case at depth n+1.
Takes IH as parameter.

Strategy: unfold leaf case for both sides, show annotations
match (via CM2 for the annotation component), show
Q-structure matches, apply IH on children.

Template: `polyDistLaw_comul_approx_leaf`
(line 1258, ~170 lines).

Build checkpoint.

#### CM6. Write polyGSOSDistLaw\_comul\_approx

Main induction on `n`, dispatching to node/leaf cases.

Template: `polyDistLaw_comul_approx` (line 1432, ~30 lines).

Build checkpoint.

#### CM7. Write polyGSOSDistLaw\_comul

Lift from approximation to full morphism equality.

Pattern: `Over.OverMorphism.ext`, `funext`, `Sigma.ext`,
`PolyCofix.ext`, `intro n`, apply approx.

Template: `polyDistLaw_comul` (line 1470, ~40 lines).

Build checkpoint.

#### CM8. Commit

Message: "GSOS comultiplication coherence proof"

### Phase MU: Multiplication coherence

The multiplication proof uses a different strategy from
the other coherence proofs: rather than direct depth-indexed
induction, express both sides as anamorphisms from the same
`polyScale`-coalgebra and use `polyCofixUnfold_precomp`.

Template: `polyDistLaw_mul` (lines 1850-2410, ~560 lines).

#### MU1. Write polyGSOSDistLaw\_mul\_srcCoalgStrAt

The `polyScale(T_P(A), Q)`-coalgebra structure on
`T_P(T_P(D_Q(A)))`.  Combines:

- Annotation: `T_P(eps_Q)(mu(t))` where
  mu = polyFreeMJoinMor and eps\_Q = polyCofreeCounit
- Q-index/children: from `polyGSOSFoldCata` applied to
  `polyFreeMJoinMor(t)` (the fold of the flattened tree)

In the P=Q case, the P-coalgebra on T(D(A)) uses
`polyFreeMCoalgStrAt`. In the GSOS case, we use the
GSOS fold instead.

Two sub-options:

- (a) Define via `polyFreeMCoalgStrAt` for the outer
  P-structure, then use the GSOS fold for Q-structure
- (b) Define directly combining join + GSOS fold

Following the P=Q template (line 1755), use approach (a):
the outer free monad structure gives the P-coalgebra,
and we pair it with `T_P(eps_Q)(mu(t))` for annotation
and the GSOS fold for Q-structure.

Template: `polyDistLaw_mul_srcCoalgStrAt`
(line 1755, ~20 lines).

Build checkpoint.

#### MU2. Write packaging definitions

Write `_srcCoalgStrLeft`, `_srcCoalgStr_comm`,
`_srcCoalgStr`, `_srcCoalg`.

Direct adaptation of lines 1783-1842.

Build checkpoint.

#### MU3. Write polyGSOSDistLaw\_mul\_rhsCoalg

The `polyScale(T_P(A), Q)`-coalgebra on `D_Q(T_P(A))`
obtained by reindexing the GSOS scale coalgebra at T\_P(A)
by `polyFreeCounitFold P (polyFreeAlg A P)` (monad mu).

Uses `polyScaleReindexCoalg`.

Template: `polyDistLaw_mul_rhsCoalg`
(line 1630, ~10 lines).

Build checkpoint.

#### MU4. Prove mu\_hom\_h (LHS coalgebra morphism condition)

Show: `srcCoalg.str >> Scale.map(mu) = mu >> scaleCoalg.str`

This is the most technically demanding sub-proof.  The
P=Q template (lines 1868-2047) does this by:

1. `Over.OverMorphism.ext`, `funext`, induction on tree
2. Node case: unfold everything, use
   `polyFreeMonad_mu_left_eq` to express `mu.left` via
   `polyFreeMJoinMor`
3. Leaf case: multiple sub-cases for inner tree structure

In the GSOS case, the proof structure is similar but
involves the GSOS fold rather than the P-coalgebra.  The
fold on `mu(t)` must equal `mu` composed with the fold on
each inner tree.

This requires showing:
`polyGSOSFoldCata(mu(t)) = mu_*(polyGSOSFoldCata(t))`
where `mu_*` is an appropriate lifting.

This may require `polyGSOSFoldCata_natural` or a new
lemma about fold and join.

Sub-steps:

1. MU4a. Write type signature with underscore body
2. MU4b. Reduce to pointwise via
   `Over.OverMorphism.ext`, `funext`
3. MU4c. Induct on tree structure
4. MU4d. Handle node case (P-node): unfold srcCoalg, use
   `polyFreeMonad_mu_left_eq` for mu, show fold commutes
5. MU4e. Handle leaf case: sub-case on inner tree
   structure (pure leaves vs nodes in the inner T\_P)

Factor helper lemmas as needed when sub-proofs exceed
~30 lines.

Build checkpoint after each sub-step.

#### MU5. Prove tdist\_hom\_h (RHS coalgebra morphism condition)

Show: `srcCoalg.str >> Scale.map(T(dist)) =
T(dist) >> rhsCoalg.str`

Template: lines 2048-2353.

This involves showing the source coalgebra structure
commutes with `polyFreeMap ... (polyGSOSDistLawMor ...)`.

Sub-steps:

1. MU5a. Write type signature with underscore body
2. MU5b. Reduce to pointwise via ext/funext
3. MU5c. Induct on tree structure
4. MU5d. Handle node case: annotation equality uses counit
   coherence (`polyGSOSDistLaw_counit`) and mu naturality
5. MU5e. Handle leaf case: show dist applied to pure leaf
   matches the expected structure

Build checkpoint after each sub-step.

#### MU6. Assemble polyGSOSDistLaw\_mul

With `mu_hom_h` and `tdist_hom_h`, apply
`polyCofixUnfold_precomp` twice:

1. `lhs_eq`: mu >> dist = polyCofixUnfold srcCoalg
   (via `polyCofixUnfold_precomp` with mu\_hom\_h)
2. `rhs_eq1`: dist\_{TA} >> D\_Q(mu) =
   polyCofixUnfold rhsCoalg
   (via `polyScaleReindex`)
3. `rhs_eq2`: T(dist) >> polyCofixUnfold rhsCoalg =
   polyCofixUnfold srcCoalg
   (via `polyCofixUnfold_precomp` with tdist\_hom\_h)
4. `rw [lhs_eq, rhs_eq1, rhs_eq2]`

Template: lines 2354-2410 (~60 lines).

Build checkpoint.

#### MU7. Commit

Message: "GSOS multiplication coherence proof"

### Phase PK: Final packaging

#### PK1. Write polyGSOSDistributiveLaw

Combine all four axioms + naturality into a
`DistributiveLaw` instance.  Each field delegates to its
corresponding lemma after `simp` unfolding of
`polyFreeMonad_eta_eq`, `polyCofreeComonad_eps_eq`, etc.

Template: PolyDistributiveLaw.lean lines 2510-2567.

Build checkpoint.

#### PK2. Write polyGSOSOperationalMonad

```lean
def polyGSOSOperationalMonad P Q rho :
    Monad (polyCofreeComonad X Q).Coalgebra :=
  liftedMonad (polyGSOSDistributiveLaw P Q rho)
```

Build checkpoint.

#### PK3. Full build and test

```bash
lake build && lake test
```

#### PK4. Commit

Message: "GSOS distributive law and operational monad"

#### PK5. Update session documents

Mark E1 and E2 as complete in
`polynomial-algebra-coalgebra-combinators.md`.
Update this file to reflect completion.

## Resumption guide

When resuming after compaction/restart:

1. Run `lake build GebLean.PolyGSOS 2>&1 | head -5` to see
   current state
2. Check which phase we're in by looking at the last commit
   message (`git log --oneline -5`)
3. Find the next uncompleted step in this document
4. For each step, use the underscore technique from CLAUDE.md:
   write the signature with underscore body, build, check
   goal type, fill in
5. After completing a phase, commit and update this document

## Design notes

The node handler pipeline in `polyGSOSFoldNodeAt`:

1. `prodComp`: convert overPullback to product polynomial
   evaluation
2. `polyBetweenComp_eval_fiberEquiv.invFun`: to composite
   evaluation
3. `polyBetweenMorphEvalAt rho.rule`: apply GSOS rule
4. `polyBetweenComp_eval_fiberEquiv.toFun`: from composite
   evaluation
5. `ccrEvalMap join`: flatten via free monad multiplication

The `join` morphism uses `polyFreeMPolyEval_to_polyFreeM`
followed by `polyFreeMBind` to flatten tree-of-trees.

The `prodComp` morphism constructs product polynomial
evaluation from a pullback pair by:

- Identity component: maps to the first projection element
- Q component: maps to the Q-evaluation child morphism

## Template references

All proofs follow patterns from `PolyDistributiveLaw.lean`:

| GSOS proof | Template              | Lines     | Est. lines |
| ---------- | --------------------- | --------- | ---------- |
| counit     | `polyDistLaw_counit`  | 280-294   | ~15 (done) |
| unit       | `polyDistLaw_unit`    | 334-480   | ~120 (done)|
| naturality | `polyDistLaw_nat`     | 474-940   | ~250       |
| comul      | `polyDistLaw_comul`   | 959-1500  | ~450       |
| mul        | `polyDistLaw_mul`     | 1630-2410 | ~650       |
| packaging  | final section         | 2463-2567 | ~60        |
