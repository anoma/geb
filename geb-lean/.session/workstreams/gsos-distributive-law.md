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

## Current state (2026-03-05, updated)

### What compiles

- `polyGSOSFoldNodeAt_snd_natural` (line 913): Type
  signature compiles. Inner `rho_nat` helper compiles.
  Main body has underscore at line 992.
- `polyGSOSFoldQeval_natural` (line 994): Uses
  `polyGSOSFoldNodeAt_snd_natural` in node case.
  Leaf case proved.
- `polyGSOSScaleCoalg_morphism_h` (line 1080): Leaf
  case proved. Node case has underscore at line 1217 for
  Q-children.
- `polyGSOSDistLaw_naturality` (line 1219): Compiles
  given `polyGSOSScaleCoalg_morphism_h`.

### Dependency chain

```
polyGSOSFoldNodeAt_snd_natural  (bottleneck)
    ↓
polyGSOSFoldQeval_natural  (induction on t, node case
    delegates to polyGSOSFoldNodeAt_snd_natural)
    ↓
polyGSOSScaleCoalg_morphism_h line 1217
    (use polyGSOSFoldQeval_natural + Sigma decomposition)
    ↓
polyGSOSDistLaw_naturality  (already compiles given above)
```

Once `polyGSOSFoldNodeAt_snd_natural` compiles,
everything else follows.

### The Q-children pipeline naturality problem

File `GebLean/PolyGSOS.lean`, lemma
`polyGSOSFoldNodeAt_snd_natural` at line 913.

#### Goal structure

After `simp only [polyGSOSFoldNodeAt, GSOSQMap,
polyEndoFunctor, polyBetweenEvalFunctor,
polyToOverFunctor, polyToOverEvalMap_left]` and
`congr 1`, the goal reduces to:

```
ccrEvalMap freeMap (pipeline_A node_A) = pipeline_B node_B
```

where `pipeline = ccrEvalMap join . toFun . rhoEval .
invFun . ccrEvalMap prodComp` and:

- `node_A = pbefMk p childMor_A` with
  `childMor_A.left e = catA_e.val`
- `node_B = pbefMk p childMor_B` with
  `childMor_B.left e = catB_e.val`
- `catA_e = polyGSOSFoldCataWithFiber A ...
  (children e)`
- `catB_e = polyGSOSFoldCataWithFiber B ...
  (polyFreeMapAt ... (children e))`

#### Available hypotheses

- `ih`: `GSOSQMap.left catA_e.val.val.2 =
  catB_e.val.val.2` (Q-eval naturality per child)
- `h_fst`: `catB_e.val.val.1 = freeMap.left
  catA_e.val.val.1` (fst naturality per child,
  via `polyGSOSFoldFst_natural`)
- `rho_nat`: `ccrEvalMap freeMap (rhoEval_A ev) =
  rhoEval_B (ccrEvalMap freeMap ev)` (rho naturality)

#### Pipeline operations

`polyGSOSFoldNodeAt` (lines 135-231) applies five
operations:

1. `ccrEvalMap prodComp`: overPullback -> IQ-eval.
   `prodComp` maps `(fst, snd)` to
   `⟨y, ⟨fun | inl _ => PUnit.unit | inr _ =>
   snd.2.1, morph⟩⟩` where `morph(inl) = fst`,
   `morph(inr, dir) = snd.2.2.left dir`.

2. `invFun` = `polyBetweenComp_eval_fiberEquiv_invFun
   P IQ TDQ y`: P-eval at IQ.obj -> composite P.IQ
   eval. Restructures using `mor_to_pbe_fiber_index`
   and `mor_to_pbe_fiber_mor`.

3. `polyBetweenMorphEvalAt rho.rule TDQ y`:
   composite P.IQ eval -> composite Q.TP eval.
   Index: `ccrReindex (rho.rule y)`.
   Morph: `ccrFiberMor (rho.rule y) ... ≫ input.mor`.

4. `toFun` = `polyBetweenComp_eval_fiberEquiv_toFun
   Q TP TDQ y`: composite Q.TP eval -> Q-eval at
   TP.obj. Index: outer Q-index. Morph: restructured.

5. `ccrEvalMap join`: Q-eval at TP.obj -> Q-eval at
   TDQ. `join` uses `polyFreeMPolyEval_to_polyFreeM`
   then `polyFreeMBind` to flatten tree-of-trees.

### Proof plan: push freeMap from outside to inside

Strategy: rewrite
`ccrEvalMap freeMap (pipeline_A node_A)`
into `pipeline_B node_B`
by commuting `freeMap` past each pipeline step,
working outside-in.

```
ccrEvalMap freeMap (ccrEvalMap join_A (toFun_A
  (rhoEval_A (invFun_A (ccrEvalMap prodComp_A
  node_A)))))

-- Step 4 (join_nat):
= ccrEvalMap join_B (ccrEvalMap (TP.map freeMap)
    (toFun_A (rhoEval_A (invFun_A
    (ccrEvalMap prodComp_A node_A)))))

-- Step 3 (toFun_nat):
= ccrEvalMap join_B (toFun_B (ccrEvalMap freeMap
    (rhoEval_A (invFun_A
    (ccrEvalMap prodComp_A node_A)))))

-- Step 2 (rho_nat, already proved):
= ccrEvalMap join_B (toFun_B (rhoEval_B
    (ccrEvalMap freeMap (invFun_A
    (ccrEvalMap prodComp_A node_A)))))

-- Step 1 (invFun_nat):
= ccrEvalMap join_B (toFun_B (rhoEval_B
    (invFun_B (ccrEvalMap (IQ.map freeMap)
    (ccrEvalMap prodComp_A node_A)))))

-- Step 0 (children_nat + prodComp_nat):
= ccrEvalMap join_B (toFun_B (rhoEval_B
    (invFun_B (ccrEvalMap prodComp_B node_B))))
```

### Sub-lemmas for each step

#### Step 0: children + prodComp naturality

**Statement (combined)**:
`ccrEvalMap (IQ.map freeMap) (ccrEvalMap prodComp_A
node_A) = ccrEvalMap prodComp_B node_B`

Equivalently: `childMor_A ≫ prodComp_A ≫ IQ.map
freeMap = childMor_B ≫ prodComp_B`.

**Proof sketch**: `Over.OverMorphism.ext; funext e`.
At each P-direction `e`:

- y-coordinate: `catA_e.val.prop` gives
  `catA_e.val.val.1.1 = catA_e.val.val.2.1`;
  similarly for B side. The y-coordinates match
  because both sides produce the y-coordinate from
  the fold result.

- IQ-index: `fun | inl _ => PUnit.unit |
  inr _ => qIdx`. From `ih`, `ccrEvalMap freeMap`
  preserves Q-indices: `catA_e.val.val.2.2.1 =
  catB_e.val.val.2.2.1`. The `inl` branch gives
  `PUnit.unit` on both sides. So IQ-indices match.

- IQ-morphism at `inl`: LHS gives
  `freeMap.left (catA_e.val.val.1)`.
  RHS gives `catB_e.val.val.1`.
  These are equal by `h_fst` (reversed).

- IQ-morphism at `inr, dir`: LHS gives
  `freeMap.left (catA_e.val.val.2.2.2.left dir)`.
  RHS gives `catB_e.val.val.2.2.2.left dir`.
  These are equal because from `ih`,
  `ccrEvalMap freeMap ⟨qIdx_A, qMor_A⟩ =
  ⟨qIdx_B, qMor_B⟩`, so `qMor_A ≫ freeMap =
  qMor_B` (after index transport), giving
  `freeMap.left (qMor_A.left dir) =
  qMor_B.left dir`.

**Difficulty**: Medium. Main work is decomposing
the `prodComp` output and matching components.
Needs careful handling of the `Over X` morphism
`w` conditions and the Sigma structure.

**Implementation**: Inline `have` in proof.
Alternatively, define `prodComp_natural` as a
private lemma stating the morphism equation
`prodComp_A ≫ IQ.map freeMap =
overPullbackMap freeMap GSOSQMap ≫ prodComp_B`,
then combine with children naturality
`childMor_A ≫ overPullbackMap freeMap GSOSQMap =
childMor_B`.

#### Step 1: invFun naturality

**Statement**: For any
`v : polyBetweenEvalFamily Y Z g (polyBetweenEval
  X Y f A) z`,
`ccrEvalMap h (invFun g f A z v) =
  invFun g f B z (ccrEvalMap (f_eval.map h) v)`

where `h : A ⟶ B` and `f_eval.map h =
(polyEndoFunctor X f).map h`.

**Why it holds**: `invFun` restructures a
P-eval-at-(f.obj A) into a composite (P.f)-eval-at-A
using `mor_to_pbe_fiber_index` and
`mor_to_pbe_fiber_mor`. These extract index and
morphism from the inner f-evaluation at each
P-direction. Post-composing with `h` distributes:

- Index: `mor_to_pbe_fiber_index (childMor ≫
  f.map h) eg = mor_to_pbe_fiber_index childMor eg`
  because `f.map h` preserves evaluation indices
  (it only post-composes the morphism part via
  `ccrEvalMap`). This should be DEFINITIONAL because
  `ptoefIndex` extracts the first field of the eval
  pair, which is the same before and after
  `ccrEvalMap h`.

- Morphism: `(mor_to_pbe_fiber_mor (childMor ≫
  f.map h) eg).left ef = h.left
  ((mor_to_pbe_fiber_mor childMor eg).left ef)`
  because `f.map h` post-composes with `h`, and
  `mor_to_pbe_fiber_mor` extracts the morphism whose
  `.left` gives `h.left (...)` after composition.

**Proof sketch**: By the Sigma equality of
`polyBetweenEvalFamily` values:
- Index part: `rfl` (definitional, if `ptoefIndex`
  reduction works through `ccrEvalMap`)
- Morphism part: `Over.OverMorphism.ext; funext
  ⟨eg, ef⟩; rfl` (if definitional), or
  `simp [ccrEvalMap, mor_to_pbe_fiber_mor, ...]`.

**Difficulty**: Low-Medium. Should reduce to simple
unfolding if the definitions are transparent enough.

**Implementation**: Prove as a general private lemma
`polyBetweenComp_eval_invFun_natural` in
`Polynomial.lean` or inline in `PolyGSOS.lean`.

#### Step 2: rho naturality (already proved)

Existing `have rho_nat` in the proof context.

Uses: `polyBetweenMorphEvalAt` definition and
`ccrEvalMap` / `ccrReindex` / `ccrFiberMor`
distributivity, with `Category.assoc`.

#### Step 3: toFun naturality

**Statement**: For any composite eval `v`,
`ccrEvalMap (g_eval.map h) (toFun g f A z v) =
  toFun g f B z (ccrEvalMap h v)`

where `g_eval.map h = (polyEndoFunctor X g).map h`.

**Why it holds**: `toFun` restructures a composite
(g.f)-eval-at-A into a g-eval-at-(f.obj A). The
outer g-index is preserved. For each g-direction,
the inner f-evaluation is constructed by
`Over.homMk (fun ef => mor.left ⟨eg, ef⟩) ...`.

Post-composing with `h` distributes:

- Index: `ig` (the outer g-index from the composite
  index `⟨ig, pf⟩`). Same on both sides
  (definitional).

- Morphism: The g-evaluation morphism maps each
  g-direction `eg` to a `(f.obj A).left` element
  `⟨y_eg, ⟨pf eg, Over.homMk (fun ef =>
  mor.left ⟨eg, ef⟩) ...⟩⟩`. After `g_eval.map h`,
  the inner f-eval morphism is post-composed with
  `h`: `Over.homMk (fun ef => h.left
  (mor.left ⟨eg, ef⟩)) ...`. On the other hand,
  `ccrEvalMap h v` replaces `mor` with `mor ≫ h`,
  and `toFun` applied to this gives
  `Over.homMk (fun ef => (mor ≫ h).left ⟨eg, ef⟩)
  ... = Over.homMk (fun ef => h.left
  (mor.left ⟨eg, ef⟩)) ...`. Same result.

**Proof sketch**: Similar structure to Step 1.
`Sigma.ext` with `rfl` for index, then
`Over.OverMorphism.ext; funext eg`. At each `eg`,
show the eval elements match by
`Sigma.ext rfl (Sigma.ext rfl
(Over.OverMorphism.ext (funext ef)))`.

**Difficulty**: Low-Medium. Parallel to Step 1.

**Implementation**: Prove as general private lemma
`polyBetweenComp_eval_toFun_natural` or inline.

#### Step 4: join naturality

**Statement**: `join_A ≫ freeMap =
(polyEndoFunctor X (polyFreeMPoly P)).map freeMap
≫ join_B`

where `join = Over.homMk (fun ⟨x', evalElem⟩ =>
⟨x', polyFreeMBind TDQ DQ P
(polyFreeMPolyEval_to_polyFreeM TDQ P evalElem)
(fun _ a => a.prop ▸ a.val.2)⟩) rfl`.

**Why it holds**: The join morphism:
1. Converts a `polyFreeMPoly P` evaluation into a
   `PolyFreeM TDQ P` tree (via
   `polyFreeMPolyEval_to_polyFreeM`)
2. Binds this tree, substituting each leaf
   `a : TDQ.left` with `a.prop ▸ a.val.2 :
   PolyFreeM DQ P ...` (the sub-tree stored in
   the leaf)

Naturality says: mapping then joining = joining
then mapping.

At each `⟨x', evalElem⟩`:

LHS: `freeMap.left (x', polyFreeMBind TDQ_A DQ_A P
(polyFreeMPolyEval_to_polyFreeM TDQ_A P evalElem)
sub_A)` where `sub_A _ a = a.prop ▸ a.val.2`.

This is `(x', polyFreeMapAt DQ_A DQ_B P cofreeMap x'
(polyFreeMBind TDQ_A DQ_A P tree_A sub_A))`.

RHS: `(x', polyFreeMBind TDQ_B DQ_B P
(polyFreeMPolyEval_to_polyFreeM TDQ_B P
(ccrEvalMap (TP.map freeMap) evalElem))
sub_B)`.

Using `polyFreeMPolyEval_to_M_natural` (PolyAlg:8423):
`polyFreeMapAt TDQ_A TDQ_B P freeMap x' tree_A =
polyFreeMPolyEval_to_polyFreeM TDQ_B P
(ccrEvalMap (TP.map freeMap) evalElem)`

So RHS tree = `polyFreeMapAt ... freeMap ... tree_A`.

Then the equality reduces to:
`polyFreeMapAt DQ_A DQ_B P cofreeMap x'
(polyFreeMBind TDQ_A DQ_A P tree_A sub_A) =
polyFreeMBind TDQ_B DQ_B P
(polyFreeMapAt TDQ_A TDQ_B P freeMap x' tree_A)
sub_B`

This is bind-map interchange. Proof via:
- `polyFreeMapAt_as_bind` (PolyAlg:5765)
- `polyFreeM_bind_assoc` (PolyAlg:3494)
- `polyFreeM_pure_bind` (PolyAlg:3466)
- `polyFreeMapAt_transport` (PolyAlg:5734)

Alternatively, check if `polyFreeMJoin_natural`
(PolyAlg:8366) applies directly, which would
avoid the bind-level argument.

**Difficulty**: Medium-High. The bind-map
interchange requires several monad law applications
and proof irrelevance arguments. May be the
hardest individual step.

**Implementation**: Separate private lemma
`gsosJoin_natural` or similar.

### Assembling the proof of polyGSOSFoldNodeAt\_snd\_natural

```lean
:= by
  let DQ_A := polyCofreeCarrier A Q
  let DQ_B := polyCofreeCarrier B Q
  let TDQ_A := polyFreeMCarrier DQ_A P
  let TDQ_B := polyFreeMCarrier DQ_B P
  let freeMap := GSOSFreeMap A B P Q f
  have rho_nat : ... := by ...  -- already proved
  have h_fst : ... := by ...  -- from polyGSOSFoldFst_natural
  -- Unfold polyGSOSFoldNodeAt and GSOSQMap
  simp only [polyGSOSFoldNodeAt, GSOSQMap,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap_left]
  congr 1
  -- Now goal is the ccrEval equality.
  -- Apply the chain of rewrites using
  -- steps 0-4 established above.
  -- Method: use `conv` or `calc` or sequential
  -- `rw` with the sub-lemmas.
```

### Resolving line 1217 after polyGSOSFoldNodeAt\_snd\_natural

Once `polyGSOSFoldNodeAt_snd_natural` compiles,
`polyGSOSFoldQeval_natural` compiles (line 994).

At line 1217, the goal is:
```
polyFreeMapLeft DQ_A DQ_B P cofreeMap
  (catA.val.val.2.snd.snd.left e₁) =
catB.val.val.2.snd.snd.left e₂
```
i.e., `freeMap.left (qMor_A.left e₁) =
qMor_B.left e₂` where `e₁ ≍ e₂`.

This follows from `polyGSOSFoldQeval_natural`
applied to `PolyFix.mk y (Sum.inr p) children`:
1. `polyGSOSFoldQeval_natural` gives
   `GSOSQMap.left catA.val.val.2 = catB.val.val.2`
2. Unfolding: `⟨y, ⟨qIdx_A, qMor_A ≫ freeMap⟩⟩ =
   ⟨y, ⟨qIdx_B, qMor_B⟩⟩`
3. Sigma decomposition: `qIdx_A = qIdx_B` (which is
   `hqidx`) and `qMor_A ≫ freeMap ≍ qMor_B` (HEq
   from index change)
4. At `e₁ ≍ e₂`, the HEq on morphisms gives
   `(qMor_A ≫ freeMap).left e₁ = qMor_B.left e₂`
5. `(qMor_A ≫ freeMap).left e₁ =
   freeMap.left (qMor_A.left e₁)` = the goal.

Note: `polyGSOSFoldQeval_natural` for the full
tree is NOT circular with `polyGSOSScaleCoalg_morphism_h`
because:
- `polyGSOSFoldQeval_natural` is proved by its OWN
  induction on `t`, separate from the induction in
  `polyGSOSScaleCoalg_morphism_h`
- The `ih` in `polyGSOSScaleCoalg_morphism_h` at
  line 1217 gives the coalgebra morphism condition
  per child, but `polyGSOSFoldQeval_natural` doesn't
  use this — it has its own induction hypothesis

The `ih` from `polyGSOSScaleCoalg_morphism_h` is
only needed for the outer structure (annotation,
Q-index), not for Q-children — those come from
`polyGSOSFoldQeval_natural`.

### Implementation order

1. Prove Step 1 (invFun_nat) as a general lemma
2. Prove Step 3 (toFun_nat) as a general lemma
3. Prove Step 4 (join_nat) as a private lemma
4. Prove Step 0 (children + prodComp) inline
5. Assemble `polyGSOSFoldNodeAt_snd_natural`
6. Verify `polyGSOSFoldQeval_natural` compiles
7. Fill line 1217 using `polyGSOSFoldQeval_natural`
8. Build checkpoint

### Existing lemmas to use

| Lemma | File:Line | Purpose |
| ----- | --------- | ------- |
| `ccrEvalMap_comp` | Polynomial:347 | `ccrEvalMap (f ≫ g) = ccrEvalMap g ∘ ccrEvalMap f` |
| `ccrEvalMap_id` | Polynomial:341 | Identity map |
| `ccrEvalMap_index` | Polynomial:333 | `ccrEvalIndex (ccrEvalMap f x) = ccrEvalIndex x` (simp, rfl) |
| `ccrEvalMap_mor` | Polynomial:337 | `ccrEvalMor (ccrEvalMap f x) = ccrEvalMor x ≫ f` (simp, rfl) |
| `polyBetweenComp_eval_fiberEquiv_toFun` | Polynomial:1677 | toFun definition |
| `polyBetweenComp_eval_fiberEquiv_invFun` | Polynomial:1691 | invFun definition |
| `mor_to_pbe_fiber_index` | Polynomial:1250 | Index extraction |
| `mor_to_pbe_fiber_mor` | Polynomial:1259 | Morphism extraction |
| `mor_to_pbe_fiber_index_homMk_rfl` | Polynomial:1279 | Index with `Over.homMk` reduces |
| `mor_to_pbe_fiber_mor_homMk_rfl` | Polynomial:1292 | Morphism with `Over.homMk` reduces |
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
