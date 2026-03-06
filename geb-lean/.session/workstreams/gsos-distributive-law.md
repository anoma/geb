# GSOS Distributive Law

## Status: Naturality proof in progress (3 errors + 2 holes)

## Current build state

File: `GebLean/PolyGSOS.lean` (1323 lines, staged but not
committed)

Three build errors and two holes (`_` placeholders):

### Error 1 (line 988): `mor_to_pbe_fiber_index_postcomp`

The `generalize` tactic fails because the expression
`(hMor.left c).fst` appears under dependent transport
(`eqRec`) in a way that entangles the proof with the
expression being generalized.

**Fix**: Replace the proof body. The goal after `simp` is:

```text
(p1 ▸ match (hMor.left c).snd with
  | ⟨i, h_1⟩ => ⟨i, h_1 ≫ h⟩).fst =
(p2 ▸ (hMor.left c).snd).fst
```

Both sides transport a Sigma whose `.fst` is the same
index `i`. Use `subst_sigma_fst_irrel` (defined at line
965 of the same file) which proves exactly this pattern:
two `eqRec`-transported Sigmas with the same `.fst`
component have equal `.fst` projections regardless of
different proofs and different `.snd` components.

Also swap the conclusion direction to match the usage
site (line 1016 currently needs `.symm`).

### Error 2 (line 1016): reversed equality

`mor_to_pbe_fiber_index_postcomp` proves `A = B` but the
goal is `B = A`. After fixing Error 1 by swapping the
conclusion, this resolves automatically.

### Error 3 (line 1018): `snd` case of Sigma.ext

In `polyBetweenComp_eval_invFun_natural`, the `snd` case
of `Sigma.ext` is an underscore. The goal is an HEq
between morphism parts:

```text
⟨..., Over.homMk (fun ⟨eg, ef⟩ =>
  (mor_to_pbe_fiber_mor hMor eg).left ef) ... ≫ h⟩.snd
≍
⟨..., Over.homMk (fun ⟨eg, ef⟩ =>
  (mor_to_pbe_fiber_mor (hMor ≫ post) eg).left ef)
  ...⟩.snd
```

**Fix**: The `.snd` on the LHS is `Over.homMk ... ≫ h`
and on the RHS is `Over.homMk ...`. Pointwise, the LHS
gives `h.left ((mor_to_pbe_fiber_mor hMor eg).left ef)`
and the RHS gives
`(mor_to_pbe_fiber_mor (hMor ≫ post) eg).left ef`.
These should be definitionally equal after unfolding
`mor_to_pbe_fiber_mor` and `polyToOverEvalMap`.

Approach: After the `fst` equality is established (giving
the index equality needed for the HEq), cast the HEq to
an Eq via `heq_of_eq` (if indices are definitionally
equal after rewriting) or use dependent rewriting. Then
apply `Over.OverMorphism.ext`, `funext ⟨eg, ef⟩`, and
unfold definitions to reach `rfl` or a `simp`.

### Hole 1 (line 1110): `polyGSOSFoldNodeAt_snd_natural`

The pipeline naturality for node cases. The goal
(from LSP) is a large match-expression equality comparing:

- LHS: the GSOS pipeline applied to A-side children, then
  post-composed with `freeMap`
- RHS: the GSOS pipeline applied to B-side children

The pipeline is five steps:

1. `prodComp`: overPullback to product polynomial eval
2. `invFun`: P-eval-at-(IQ.obj) to composite (P.IQ)-eval
3. `rhoEval`: apply GSOS rule
4. `toFun`: composite (Q.TP)-eval to Q-eval-at-(TP.obj)
5. `ccrEvalMap join`: flatten via free monad mu

**Strategy**: Commute `freeMap` from the outermost
position inward through each step, using a chain of
rewrites. Each step requires a naturality lemma.

See "Proof plan for polyGSOSFoldNodeAt_snd_natural" below.

### Hole 2 (line 1283): `polyGSOSScaleCoalg_morphism_h`

Node case Q-children in the coalgebra morphism proof.
The goal (from LSP):

```text
polyFreeMapLeft DQ_A DQ_B P (polyCofreeMap A B Q f)
    (fold_A_node.snd.snd.left e1) =
fold_B_node.snd.snd.left e2
```

where `e1 ≍ e2` (HEq due to equal Q-indices via `hqidx`).

**Fix**: Once `polyGSOSFoldNodeAt_snd_natural` (Hole 1)
compiles, `polyGSOSFoldQeval_natural` (line 1112) compiles
automatically. Apply `polyGSOSFoldQeval_natural` to the
full node tree `PolyFix.mk y (Sum.inr p) children` to get
the Sigma equality of Q-evaluations. Decompose into index
equality (already have `hqidx`) and morphism HEq. The
morphism HEq at `e1 ≍ e2` gives:

```text
freeMap.left (qMor_A.left e1) = qMor_B.left e2
```

which is exactly the goal (after unfolding
`polyFreeMapLeft`).

## Proof plan for polyGSOSFoldNodeAt_snd_natural

### Chain of rewrites

Starting from:

```text
ccrEvalMap freeMap (pipeline_A node_A)
```

Rewrite outside-in:

```text
ccrEvalMap freeMap
  (ccrEvalMap join_A
    (toFun_A (rhoEval_A (invFun_A
      (ccrEvalMap prodComp_A node_A)))))

-- Step 4 (join naturality):
= ccrEvalMap join_B
    (ccrEvalMap (TP.map freeMap)
      (toFun_A (rhoEval_A (invFun_A
        (ccrEvalMap prodComp_A node_A)))))

-- Step 3 (toFun naturality):
= ccrEvalMap join_B
    (toFun_B (ccrEvalMap freeMap
      (rhoEval_A (invFun_A
        (ccrEvalMap prodComp_A node_A)))))

-- Step 2 (rho naturality, already proved):
= ccrEvalMap join_B
    (toFun_B (rhoEval_B
      (ccrEvalMap freeMap (invFun_A
        (ccrEvalMap prodComp_A node_A)))))

-- Step 1 (invFun naturality):
= ccrEvalMap join_B
    (toFun_B (rhoEval_B
      (invFun_B (ccrEvalMap (IQ.map freeMap)
        (ccrEvalMap prodComp_A node_A)))))

-- Step 0 (children + prodComp naturality):
= ccrEvalMap join_B
    (toFun_B (rhoEval_B
      (invFun_B (ccrEvalMap prodComp_B node_B))))

= pipeline_B node_B
```

### Sub-lemmas needed

#### Step 4: join naturality (new lemma)

**Statement** (as Over X morphism equality):

```lean
join_A ≫ freeMap =
  (polyEndoFunctor X (polyFreeMPoly P)).map freeMap
  ≫ join_B
```

where `join` is the `Over.homMk` defined in
`polyGSOSFoldNodeAt` (lines 216-226) that converts a
`polyFreeMPoly P` evaluation element into a flattened
`PolyFreeM DQ P` tree via `polyFreeMPolyEval_to_polyFreeM`
followed by `polyFreeMBind`.

**Proof approach**: `Over.OverMorphism.ext`, `funext`, then
show pointwise equality. The LHS applies `freeMap.left`
after bind. The RHS maps the evaluation element by
`TP.map(freeMap)` and then binds.

Use:

- `polyFreeMPolyEval_to_polyFreeM` naturality: need to
  show or find that mapping the evaluation by
  `TP.map(freeMap)` and then converting to tree equals
  converting to tree and then mapping by `freeMap`.
  Check for existing lemma or prove inline.
- `polyFreeMapAt` as bind (`polyFreeMapAt_as_bind`) to
  express freeMap as a bind, then use bind associativity
  (`polyFreeM_bind_assoc`) and pure-bind
  (`polyFreeM_pure_bind`).

Alternatively, use `polyFreeMJoin_natural` (PolyAlg:8366)
if the join can be expressed as `polyFreeMJoin` composed
with some mapping.

**Difficulty**: Medium-High.

#### Step 3: toFun naturality (new lemma)

**Statement**:

```lean
private lemma polyBetweenComp_eval_toFun_natural
    (g f : PolyEndo X) (A B : Over X)
    (h : A ⟶ B) (z : X)
    (v : polyBetweenEvalFamily X X
      (polyBetweenComp g f) A z) :
    ccrEvalMap ((polyEndoFunctor X g).map h)
      ((polyBetweenComp_eval_fiberEquiv
        g f A z).toFun v) =
    (polyBetweenComp_eval_fiberEquiv
      g f B z).toFun (ccrEvalMap h v)
```

**Proof approach**: `obtain` the composite index and
morphism. Apply `Sigma.ext`:

- Index: `rfl` (outer g-index is preserved)
- Morphism: `Over.OverMorphism.ext`, `funext eg`. At each
  g-direction, the inner f-evaluation morphism is
  post-composed with `h`. After unfolding `toFun`
  (which uses `Over.homMk (fun ef => mor.left ⟨eg, ef⟩)`),
  the equality should be definitional.

**Difficulty**: Low-Medium.

#### Step 1: invFun naturality (fix existing lemma)

Already exists as `polyBetweenComp_eval_invFun_natural`
(line 993). Needs the three errors fixed (Steps A-C in
the fix plan).

#### Step 0: children + prodComp naturality (inline)

**Statement** (combined):

```text
ccrEvalMap (IQ.map freeMap)
  (ccrEvalMap prodComp_A node_A) =
ccrEvalMap prodComp_B node_B
```

**Proof approach**: After unfolding, this becomes a
Sigma equality of evaluation elements. At each P-direction
`e`, the components are:

- y-coordinate: both sides give the fold result's fiber,
  which matches by `polyGSOSFoldCataWithFiber.prop`
- IQ-index: `fun | inl _ => PUnit.unit | inr _ => qIdx`.
  The `inl` branch gives `PUnit.unit` on both sides. The
  `inr` branch gives Q-indices which are equal by `ih`
  (the inductive hypothesis gives Q-eval naturality per
  child, whose `.fst` gives Q-index equality).
- IQ-morphism at `inl`: LHS gives
  `freeMap.left (catA_e.val.val.1)`, RHS gives
  `catB_e.val.val.1`. Equal by
  `polyGSOSFoldFst_natural` (reversed).
- IQ-morphism at `inr, dir`: LHS gives
  `freeMap.left (qMor_A.left dir)`, RHS gives
  `qMor_B.left dir`. Equal by extracting from `ih`
  (the inductive hypothesis gives the full Q-eval Sigma
  equality, whose `.snd` gives morphism HEq).

**Difficulty**: Medium. Main work is decomposing the
`prodComp` output structure.

Should be factored out into a separate named lemma.

### Assembly

Use `calc` or sequential `conv`/`rw` to chain the five
steps. Each step rewrites one level of the pipeline.

The proof would look approximately like:

```lean
calc ccrEvalMap freeMap (pipeline_A)
    = ccrEvalMap join_B (ccrEvalMap (TP.map freeMap)
        (toFun_A ...)) := by
        rw [← ccrEvalMap_comp]; congr 1; exact join_nat
  _ = ccrEvalMap join_B (toFun_B
        (ccrEvalMap freeMap (rho_A ...))) := by
        congr 1; exact toFun_nat
  _ = ccrEvalMap join_B (toFun_B
        (rho_B (ccrEvalMap freeMap (invFun_A ...)))) := by
        congr 1; congr 1; exact rho_nat
  _ = ccrEvalMap join_B (toFun_B
        (rho_B (invFun_B (ccrEvalMap (IQ.map freeMap)
          ...)))) := by
        congr 1; congr 1; congr 1; exact invFun_nat
  _ = pipeline_B := by
        congr 1; congr 1; congr 1; congr 1
        exact prodComp_nat
```

### Implementation order

1. Fix `mor_to_pbe_fiber_index_postcomp` (Error 1)
2. Fix invFun_natural fst case (Error 2) --- auto-fixed
3. Fill invFun_natural snd case (Error 3)
4. Write `polyBetweenComp_eval_toFun_natural` (Step 3)
5. Write join naturality lemma (Step 4)
6. Assemble `polyGSOSFoldNodeAt_snd_natural` (Hole 1)
7. Fill `polyGSOSScaleCoalg_morphism_h` Q-children (Hole 2)
8. Build checkpoint

### Existing lemmas to use

| Lemma | File | Purpose |
| ----- | ---- | ------- |
| `ccrEvalMap_comp` | Poly | map composition |
| `ccrEvalMap_id` | Poly | map identity |
| `ccrEvalMap_index` | Poly | index preserved |
| `ccrEvalMap_mor` | Poly | morphism composed |
| `subst_sigma_fst_irrel` | GSOS:965 | eqRec fst |
| `mor_to_pbe_fiber_index` | Poly:1250 | idx extract |
| `mor_to_pbe_fiber_mor` | Poly:1259 | mor extract |
| `polyGSOSFoldFst_natural` | GSOS:913 | fold fst nat |
| `polyGSOSFoldQIndex_eq` | GSOS:736 | Q-idx nat |
| `polyFreeMJoin_natural` | Alg:8366 | join nat |
| `polyFreeMapAt_as_bind` | Alg:5765 | map as bind |
| `polyFreeM_bind_assoc` | Alg:3494 | bind assoc |
| `polyFreeM_pure_bind` | Alg:3466 | pure-bind |
| `polyFreeMapAt_comp` | Alg:5825 | map comp |
| `polyCofreeMapAt_head_snd` | Alg:6264 | cofree idx |
| `polyCofreeCounit_naturality` | Alg | eps nat |
| `Over.OverMorphism.ext` | Util | over ext |
| `polyBetweenFamily_mor_heq` | Poly | family heq |

## Completed

### PolyGSOSRule structure (PolyGSOS.lean)

- `PolyGSOSRule P Q`: GSOS rule as polynomial morphism
  `P . (Id x Q) --> Q . T_P`
- `polyIdBehaviorPoly Q`: identity-behavior product

### Fold algebra (PolyGSOS.lean)

- `polyGSOSFoldLeafAt`: leaf handler
- `polyGSOSFoldNodeAt`: node handler (pipeline)
- `polyGSOSFoldCataWithFiber`: catamorphism with fiber
- `polyGSOSFoldCata`: fold as Over X morphism

### Distributive law morphism (PolyGSOS.lean)

- `polyGSOSScaleCoalgStrAt`: scale coalgebra structure
- `polyGSOSDistLawMor`: dist law via polyCofixUnfold

### Counit coherence (done)

- `polyGSOSDistLawMor_head_fst`
- `polyGSOSDistLaw_counit`

### Unit coherence (done)

- `polyGSOSDistLaw_unit_approx`
- `polyGSOSDistLaw_unit`

### Naturality helpers (done, modulo holes)

- `polyGSOSDistLaw_annot_natural`
- `polyGSOSFoldCata_snd_fst_eq`
- `polyGSOSNodeQIdx`, `polyGSOSFoldQIndex`
- `polyGSOSFoldQIndex_leaf`, `_node_unfold`, `_eq_node`,
  `_eq`
- `polyGSOSFoldFst_natural`
- `polyGSOSFoldLeafAt_snd_natural`
- `polyGSOSScaleCoalg_morphism_h` (leaf case done)
- `polyGSOSDistLaw_naturality` (compiles given morphism_h)

## Remaining phases

### Phase N: Complete naturality (current)

Fix errors, fill holes as described above. Then:

#### N-pack: NatTrans packaging (~30 lines)

Three definitions following PolyDistributiveLaw.lean
lines 2463-2500:

```lean
def polyGSOSDistLawNatApp
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    ((polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).obj A ⟶
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor).obj A :=
  polyGSOSDistLawMor A P Q rho

lemma polyGSOSDistLawNat_naturality ... :=
  -- simp with polyCofreeComonad_map_eq,
  -- polyFreeMonad_map_eq, then exact
  -- polyGSOSDistLaw_naturality

def polyGSOSDistLawNat ... : NatTrans ... where
  app := polyGSOSDistLawNatApp
  naturality := polyGSOSDistLawNat_naturality
```

Commit: "GSOS naturality proof and NatTrans packaging"

### Phase CM: Comultiplication coherence (~450 lines)

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
