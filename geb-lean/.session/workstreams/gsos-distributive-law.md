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

### Phase N: NatTrans packaging (~30 lines)

Wrap `polyGSOSDistLawMor` as a natural transformation
between functor compositions.

#### N-1: `polyGSOSDistLawNatApp` (~5 lines)

Type alias wrapping `polyGSOSDistLawMor A P Q rho` with
the functor composition types:

```lean
def polyGSOSDistLawNatApp
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    ((polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).obj A ⟶
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor).obj A :=
  polyGSOSDistLawMor A P Q rho
```

#### N-2: `polyGSOSDistLawNat_naturality` (~15 lines)

Naturality proof delegating to `polyGSOSDistLaw_naturality`
after `simp only` unfolding of monad/comonad `map` and
`NatApp`:

```lean
lemma polyGSOSDistLawNat_naturality
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) :
    ((polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).map f ≫
    polyGSOSDistLawNatApp B P Q rho =
    polyGSOSDistLawNatApp A P Q rho ≫
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor).map f := by
  simp only [Functor.comp_map,
    polyFreeMonad_map_eq,
    polyCofreeComonad_map_eq,
    polyGSOSDistLawNatApp]
  exact polyGSOSDistLaw_naturality A B P Q rho f
```

#### N-3: `polyGSOSDistLawNat` (~10 lines)

NatTrans definition using N-1 and N-2.

**Dependencies**: `polyGSOSDistLaw_naturality` (done).

Commit: "GSOS NatTrans packaging"

---

### Phase CM: Comultiplication coherence (~350 lines)

Statement:

```text
T_P(delta_A) ≫ dist_{D_Q(A)} ≫ D_Q(dist_A) =
  dist_A ≫ delta_{T_P(A)}
```

Both sides map `T_P(D_Q(A)) → D_Q(D_Q(T_P(A)))`.

Architecture: Direct depth-indexed approximation via
`PolyCofix.ext`. Induct on depth n, case-split on tree
structure (node/leaf). This does NOT use the
`polyCofixUnfold_precomp` trick (unlike naturality and
multiplication); it works directly at the approximation
level.

Template: `polyDistLaw_comul` in PolyDistributiveLaw.lean
(lines 959-1500).

#### CM-0: Abbreviations (~30 lines)

Define four abbreviations for readability:

- `polyGSOSDistLaw_comul_lhsCoalg`:
  `polyScale(D_Q(T_P(A)), Q)`-coalgebra.
  = `polyScaleReindexCoalg ... (polyGSOSDistLawMor A P Q
  rho) (polyGSOSScaleCoalg (polyCofreeCarrier A Q) P Q
  rho)`. This is the GSOS scale coalgebra at `D_Q(A)`,
  reindexed by `dist_A`.

- `polyGSOSDistLaw_comul_rhsCoalg`:
  = `polyCofreeCoalg (polyFreeMCarrier A P) Q`.
  The Q-coalgebra on `T_P(A)`.

- `polyGSOSDistLaw_comul_lhsInput(t)`:
  = `T_P(delta_A)(t)` fed into lhsCoalg's anamorphism.
  Constructs a `{ v // ... }` element from
  `polyFreeMapAt ... (polyCoalgUnit Q ...) x t`.

- `polyGSOSDistLaw_comul_rhsInput(t)`:
  = `dist_A(t)` fed into `delta_{T_P(A)}`.
  Constructs a `{ v // ... }` element from
  `polyCofixUnfoldAt ... (polyGSOSScaleCoalg A P Q rho)
  x ⟨⟨x, t⟩, rfl⟩`.

Template: lines 992-1051.

#### CM-1: `polyGSOSDistLaw_comul_annot_eq` (~15 lines)

**Statement**:

```lean
polyFreeMapAt DA DDQ P (polyCofreeCounit DQ Q) x
  (polyFreeMapAt DA DDQ P
    (polyCoalgUnit Q (polyCofreeCoalg A Q)) x t)
= t
```

where `DA = polyCofreeCarrier A Q`,
`DQ = polyCofreeCarrier A Q`,
`DDQ = polyCofreeCarrier (polyCofreeCarrier A Q) Q`.

This says `T_P(eps ≫ delta)(t) = t`.

**Proof**: Rewrite via `polyFreeMapAt_comp` to get
`T_P(eps ≫ delta)(t)`, then apply
`polyCofree_left_triangle Q` (which gives `eps ≫ delta =
id`), then apply `polyFreeMapAt_id`.

**Dependencies**: None (uses existing comonad law).

#### CM-2: `polyGSOSDistLaw_comul_approx_leaf` (~150 lines)

**Statement**: At depth n+1, the leaf case holds.

**Input**: A leaf `t = PolyFix.mk x (Sum.inl c) ch`
where `c` wraps a cofree element `d : PolyCofreeM A Q x`.

**Mathematical argument**:

LHS reduces as follows:

1. `T_P(delta)(leaf(d))` = `leaf(delta(d))` since
   `T_P` maps leaves pointwise.
2. `dist_{DQ(A)}(leaf(delta(d)))` by unit coherence
   (`polyGSOSDistLaw_unit_approx` at `DQ(A)`)
   approximates `DQ(eta)(delta(d))` at depth n+1.
3. `DQ(dist)(DQ(eta)(delta(d)))` =
   `DQ(dist ∘ eta)(delta(d))` by functoriality.
4. By unit coherence (`polyGSOSDistLaw_unit`),
   `dist ∘ eta = DQ(eta)`, so this becomes
   `DQ(DQ(eta))(delta(d))`.

RHS reduces as follows:

1. `dist_A(leaf(d))` by unit coherence approximates
   `DQ(eta)(d)` at depth n+1.
2. `delta_{TA}(DQ(eta)(d))` by comonad comultiplication
   naturality equals `DQ(DQ(eta))(delta(d))`.

Both sides equal `DQ(DQ(eta))(delta(d))` at depth n+1.

**Proof structure**: Uses the Eq.trans chain pattern from
the P=Q template:

```lean
refine Eq.trans ?lhs_eq (Eq.trans ?ih_eq ?rhs_eq)
```

where:

- `lhs_eq`: transforms LHS using
  `polyScaleReindex_approx` and
  `polyGSOSDistLaw_unit_approx` at `DQ(A)` to get
  `DQ(DQ(eta))(delta(d))` form
- `ih_eq`: applies IH at depth n to bridge children
- `rhs_eq`: transforms RHS using `polyCoalgUnitApprox`
  properties and comonad delta naturality

**Helper lemmas available**:

- `polyScaleReindex_approx` (PolyDistributiveLaw:851)
- `polyGSOSDistLaw_unit_approx` (PolyGSOS.lean)
- `polyCofreeMapApprox` (PolyAlg:6175)
- `polyCoalgUnitApprox` (PolyAlg:6695)
- `polyCoalgUnit_family_eq` (PolyAlg:6888)
- `polyCoalgUnitAt_children_heq` (PolyAlg:7170)
- `polyCofixUnfoldAt_children_heq` (PolyAlg:1824)
- `polyCofixUnfold_coalg_comm_child_fst_eq`
  (PolyAlg:1646)

**May need to create**:

- `polyFreeMPure_cofree_sigma_eq` analog for Q (the
  existing one in PolyDistributiveLaw is for P; may need
  a version for Q, or the existing one may be parametric
  enough)

**Dependencies**: CM-1, unit coherence (done).

#### CM-3: `polyGSOSDistLaw_comul_approx_node` (~100 lines)

**Statement**: At depth n+1, the node case holds.

**Input**: A node `t = PolyFix.mk x (Sum.inr p) children`.

**Proof structure**:

1. Apply `polyScaleReindex_approx` to rewrite LHS
2. Simplify annotation via CM-1:
   `T_P(eps)(T_P(delta)(node(p, ch)))` = `node(p, ch)`
   since `T_P(eps ≫ delta)` = `T_P(id)` = `id`.
   At a node, this means the annotation component (which
   is the `T_P(A)` element inside the Scale structure)
   is `polyFreeMapAt ... eps x (T_P(delta)(node)) =
   node(p, ...)` which equals the original tree's
   annotation.
3. Q-index equality via `polyGSOSFoldQIndex_eq`:
   The Q-index of the fold at `DQ(A)` applied to
   `T_P(delta)(node)` equals the Q-index at `A` applied
   to `node` because `polyGSOSFoldQIndex_eq` shows
   Q-index is invariant under `polyFreeMapAt`. Since
   `T_P(delta) = polyFreeMapAt ... delta`, applying
   `polyGSOSFoldQIndex_eq` with `f = delta` gives the
   result.
4. Q-children equality via IH: Apply
   `polyCofixApprox_intro_polyScale_congr` with:
   - `hp = polyGSOSFoldQIndex_eq` result
   - `ha = CM-1` result (annotation)
   - `hch`: Q-children HEq from IH application at each
     Q-direction

**Helper lemmas available**:

- `polyGSOSFoldQIndex_eq` (PolyGSOS.lean)
- `polyCofixApprox_intro_polyScale_congr` (PolyAlg:514)
- `polyScaleReindex_approx` (PolyDistributiveLaw:851)

**Dependencies**: CM-1.

#### CM-4: `polyGSOSDistLaw_comul_approx` (~25 lines)

**Statement**: Depth-indexed equality for all n and all
trees t.

**Proof**: Induction on n.

- Base case (n = 0): Both sides reduce to
  `.continue x`. Trivial (`simp` or `rfl`).
- Inductive case (n + 1): Match on tree structure:
  - `PolyFix.mk _ (Sum.inr p) ch` → dispatch to CM-3
  - `PolyFix.mk _ (Sum.inl c) ch` → dispatch to CM-2

**Dependencies**: CM-2, CM-3.

#### CM-5: `polyGSOSDistLaw_comul` (~35 lines)

**Statement**: Full morphism equality.

**Proof**:

```lean
apply Over.OverMorphism.ext
funext ⟨x, t⟩
apply Sigma.ext
· rfl  -- fiber equality
· apply PolyCofix.ext
  intro n
  exact polyGSOSDistLaw_comul_approx A P Q rho t n
```

**Dependencies**: CM-4.

Commit: "GSOS comultiplication coherence proof"

---

### Phase MU: Multiplication coherence (~550 lines)

Statement:

```text
mu_{D_Q(A)} ≫ dist_A =
  T_P(dist_A) ≫ dist_{T_P(A)} ≫ D_Q(mu_A)
```

Both sides map `T_P(T_P(D_Q(A))) → D_Q(T_P(A))`.

Architecture: Express both sides as anamorphisms from
`polyScale(T_P(A), Q)`-coalgebras on
`T_P(T_P(D_Q(A)))`, then show they are the unique
coalgebra morphism using `polyCofixUnfold_precomp`.

The source coalgebra embeds fold Q-children via
`polyFreeUnit` (eta) so that `Scale.map(mu)` recovers
them via `mu ∘ eta = id` (monad left unit law). This is
the design choice from the P=Q template.

Template: `polyDistLaw_mul` in PolyDistributiveLaw.lean
(lines 1630-2410).

#### MU-1: Source coalgebra definition (~80 lines)

##### MU-1a: `polyGSOSDistLaw_mul_srcCoalgStrAt` (~25 lines)

Given `t : PolyFreeM (polyFreeMCarrier DQ P) P x`
(a tree in `T_P(T_P(D_Q(A)))`), produce a
`polyBetweenEvalFamily X X (polyScale TA Q) TTDQ x`:

```text
let mu_t := polyFreeMJoinMor DQ P t
  -- monad multiplication: T(T(DQ)) → T(DQ)
let foldResult := polyGSOSFoldCataWithFiber A P Q rho mu_t
  -- fold: T(DQ) → overPullback(T(DQ), Q(T(DQ)))
let annot := polyFreeMapAt DQ A P eps_Q x mu_t
  -- T_P(eps_Q)(mu(t)) : T_P(A)
let qIdx := foldResult.val.val.2.1
  -- Q-index from fold
let qChildren := fun e =>
    polyFreeMPure ... (foldResult.val.val.2.2.left e)
  -- wrap fold Q-children in eta (free monad unit)
  -- into T(T(DQ(A)))
return ⟨⟨⟨x, annot⟩, rfl⟩, qIdx, qChildren_mor⟩
```

The eta embedding ensures `Scale.map(mu)` recovers the
original Q-children: `mu(eta(child)) = child` by monad
left unit.

##### MU-1b: `polyGSOSDistLaw_mul_srcCoalgStrLeft` (~10 lines)

Package as a function on carrier elements.

##### MU-1c: `polyGSOSDistLaw_mul_srcCoalgStr_comm` (~15 lines)

Prove fiber compatibility: the Over X hom commutes.
The annotation is `polyFreeMapAt DQ A P eps_Q x mu_t`,
which lives in `TA.left`, and its fiber
`TA.hom annot = x` follows from `polyFreeMapAt` fiber
preservation.

##### MU-1d: `polyGSOSDistLaw_mul_srcCoalgStr` (~10 lines)

Package as Over X morphism via `Over.homMk`.

##### MU-1e: `polyGSOSDistLaw_mul_srcCoalg` (~10 lines)

Package as `PolyCoalg (polyScale TA Q)`.

Template: lines 1755-1842.

**Dependencies**: `polyGSOSFoldCataWithFiber`,
`polyFreeMJoinMor`, `polyFreeMapAt`.

#### MU-2: RHS coalgebra definition (~10 lines)

```lean
abbrev polyGSOSDistLaw_mul_rhsCoalg
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    PolyCoalg (polyScale TA Q) :=
  polyScaleReindexCoalg TTA TA Q mu_A
    (polyGSOSScaleCoalg TA P Q rho)
```

where `TTA = polyFreeMCarrier (polyFreeMCarrier A P) P`,
`TA = polyFreeMCarrier A P`,
`mu_A = polyFreeCounitFold P (polyFreeAlg A P)`.

This is the GSOS scale coalgebra at `T_P(A)`,
reindexed by `mu_A`.

**Dependencies**: `polyGSOSScaleCoalg`,
`polyScaleReindexCoalg`.

#### MU-H: Helper — mu naturality at eps_Q (~25 lines)

**Statement**: For each tree
`t : PolyFreeM (polyFreeMCarrier DQ P) P x`:

```lean
polyFreeMapAt DQ A P eps_Q x (polyFreeMJoinMor DQ P t) =
  polyFreeMJoinMor A P
    (polyFreeMapAt TDQ TA P
      (polyFreeMap DQ A P eps_Q) x t)
```

This says `T_P(eps_Q) ∘ mu_{DQ} = mu_A ∘ T_P(T_P(eps_Q))`
pointwise, which is naturality of monad mu at `eps_Q`.

**Proof**: By induction on the free monad tree `t`:

- **Node** `(Sum.inr p, ch)`:
  `mu(node(p, ch)) = node(p, mu ∘ ch)`.
  `T(eps)(node(p, mu∘ch)) = node(p, T(eps)∘mu∘ch)`.
  RHS: `T(T(eps))(node) = node(p, T(T(eps))∘ch)`,
  then `mu(node) = node(p, mu∘T(T(eps))∘ch)`.
  Equal by IH on children.

- **Leaf** `(Sum.inl a, ch)`:
  `mu(leaf(a)) = a.val.2`.
  `T(eps)(a.val.2)`.
  RHS: `T(T(eps))(leaf(a)) = leaf(T(eps)(a.val.2))`,
  then `mu(leaf(...)) = T(eps)(a.val.2)`.
  Equal directly.

**Dependencies**: None (pure free monad properties).

**Note**: `polyFreeMJoinMor_nat` in
PolyDistributiveLaw.lean (line 1708) may already provide
this. Check before writing.

#### MU-3: LHS coalgebra morphism (`mu_hom_h`) (~150 lines)

**Statement**: mu is a coalgebra morphism from srcCoalg
to the GSOS scale coalgebra at A:

```lean
(polyGSOSDistLaw_mul_srcCoalg A P Q rho).str ≫
  (polyEndoFunctor X (polyScale TA Q)).map mu_DQ =
  mu_DQ ≫ (polyGSOSScaleCoalg A P Q rho).str
```

where `mu_DQ = polyFreeCounitFold P
  (polyFreeAlg (polyCofreeCarrier A Q) P)`.

**Proof approach**: `Over.OverMorphism.ext`, `funext`,
induction on tree `t`.

##### MU-3-node (~60 lines)

For `t = node(p, children)`:

- **Annotation**: Both sides compute
  `T_P(eps_Q)(mu(node(p, ch)))`. The srcCoalg annotation
  is `T_P(eps_Q)(mu(t))` by definition. After
  `Scale.map(mu)`, the annotation is unchanged (Scale.map
  only acts on Q-children). The RHS computes
  `T_P(eps_Q)(mu(node(p, ch)))` directly. Equal by `rfl`.

- **Q-index**: Both sides compute
  `polyGSOSFoldQIndex A P Q rho (mu(t))`. The srcCoalg
  Q-index is from `polyGSOSFoldCata` of `mu(t)`. The RHS
  also folds `mu(t)`. Equal by `rfl`.

- **Q-children**: After `Scale.map(mu)`, srcCoalg's
  Q-children become `mu(eta(fold-child)) = fold-child`
  by monad left unit. RHS Q-children are fold-children
  directly. Need monad left unit lemma:
  `polyFreeCounitFoldAt P (polyFreeAlg DQ P)
    x (polyFreeMPure DQ P child) = child`.
  This should follow from the fold's leaf case or from
  `polyFreeCounitFold_left_unit` (if it exists).

  Factor out as sub-lemma if needed:
  `polyGSOSDistLaw_mul_mu_eta_cancel`:
  `mu(eta(child)) = child` at the pointwise level.

##### MU-3-leaf (~80 lines)

For `t = leaf(a)` where `a = ⟨⟨x_a, t_a⟩, ha⟩`
and `t_a : PolyFreeM DQ P x_a`:

- `mu(leaf(a)) = t_a` (after transport via `ha`)
- srcCoalg computes `polyGSOSFoldCata` of `t_a` (with
  eta-embedded Q-children)
- After `Scale.map(mu)`: Q-children become
  `mu(eta(fold-child)) = fold-child`
- RHS: `(polyGSOSScaleCoalg A P Q rho).str` applied to
  `t_a` computes the same fold

Match on `t_a` structure (inner node vs inner leaf):

- **Inner node** `t_a = node(p_inner, ch_inner)`:
  Both sides compute `polyGSOSScaleCoalgStrAt` of
  `node(p_inner, ch_inner)`. Direct equality.

- **Inner leaf** `t_a = leaf(c)`:
  Both sides compute `polyGSOSScaleCoalgStrAt` of
  `leaf(c)`. Direct equality.

The transport from `ha` requires `subst` or `obtain` +
destructuring.

**Dependencies**: MU-1, `polyGSOSScaleCoalg`.

#### MU-4: RHS coalgebra morphism (`tdist_hom_h`) (~250 lines)

**Statement**: `T_P(dist)` is a coalgebra morphism from
srcCoalg to rhsCoalg:

```lean
(polyGSOSDistLaw_mul_srcCoalg A P Q rho).str ≫
  (polyEndoFunctor X (polyScale TA Q)).map
    (polyFreeMap DQ (polyCofreeCarrier TA Q) P
      (polyGSOSDistLawMor A P Q rho)) =
  polyFreeMap DQ (polyCofreeCarrier TA Q) P
    (polyGSOSDistLawMor A P Q rho) ≫
  (polyGSOSDistLaw_mul_rhsCoalg A P Q rho).str
```

**Proof approach**: `Over.OverMorphism.ext`, `funext`,
induction on tree `t`.

##### MU-4-node-annot (~40 lines)

At a node `t = node(p, ch)`:

`T(dist)(node(p,ch)) = node(p, T(dist)∘ch)`.

LHS annotation: `T_P(eps_Q at A)(mu_{DQ}(node(p,ch)))`.
After `Scale.map(T(dist))`: annotation unchanged.

RHS annotation from rhsCoalg: the reindexed coalgebra
applies `mu_A` to the Scale annotation at `T_P(A)`:
`mu_A(T_P(eps_Q at TA)(node(p, T(dist)∘ch)))`.

Need:

```text
T_P(eps_Q at A)(mu_{DQ}(t)) =
  mu_A(T_P(eps_Q at TA)(T_P(dist)(t)))
```

Proof chain:

1. `T_P(eps_Q at TA) ∘ T_P(dist) = T_P(eps_Q at TA ∘ dist)
   = T_P(T_P(eps_Q at A))` by counit coherence
   (`polyGSOSDistLaw_counit`) and `polyFreeMapAt_comp`.

2. `mu_A ∘ T_P(T_P(eps_Q)) = T_P(eps_Q) ∘ mu_{DQ}`
   by monad mu naturality (MU-H) with `f = eps_Q`.

Combined: `mu_A(T_P(eps_Q at TA)(T_P(dist)(t)))
= mu_A(T_P(T_P(eps_Q))(t)) = T_P(eps_Q)(mu_{DQ}(t))`.

##### MU-4-node-qstructure (~60 lines)

Q-index and Q-children at nodes.

Uses `polyCofixUnfold_coalg_comm` (PolyAlg:2085) which
relates `dist`'s structure map to the scale coalgebra:

```lean
(polyGSOSScaleCoalg A P Q rho).str ≫
  (polyEndoFunctor X (polyScale TA Q)).map dist =
  dist ≫ polyCofixDest (polyScale TA Q)
```

From this, extract Q-index and Q-children equality via
`Sigma.mk.inj` + `eq_of_heq` (the same pattern as in
the naturality proof's `polyBetweenEvalMap_mor_apply`).

For Q-children: need to show that `T(dist)` applied to
eta-embedded Q-children produces the expected children
of the rhsCoalg. Since `T(dist)(eta(child)) =
eta(dist(child))` (by T preserving leaves), and the
rhsCoalg Q-children are reindexed by `mu_A`, the
composition should cancel via `mu(eta(x)) = x`.

##### MU-4-leaf (~120 lines)

For `t = leaf(a)` where `a = ⟨⟨x_a, t_a⟩, ha⟩`:

`T(dist)(leaf(a)) = leaf(dist(t_a))` (after transport).

Uses `polyCofixUnfold_coalg_comm` at the point `t_a`
to relate `dist(t_a)`'s structure to the scale coalgebra.

Sigma extraction chain:

1. Apply `polyCofixUnfold_coalg_comm` at `t_a`
2. Extract via `Sigma.mk.inj` (outer z-component)
3. Extract via `Sigma.mk.inj` (inner idx-component)
4. Extract morphism equality via
   `congrFun (congrArg CommaMorphism.left ...)`

The leaf case handles transport from `ha` via `subst`
or `obtain` destructuring, then matches on inner tree
structure if needed.

**Dependencies**: MU-1, MU-2, counit coherence (done),
`polyCofixUnfold_coalg_comm`.

#### MU-5: Assembly (`polyGSOSDistLaw_mul`) (~50 lines)

With `mu_hom_h` and `tdist_hom_h`, apply
`polyCofixUnfold_precomp` twice:

```lean
have lhs_eq :
    mu_DQ ≫ polyGSOSDistLawMor A P Q rho =
    polyCofixUnfold (polyScale TA Q)
      (polyGSOSDistLaw_mul_srcCoalg A P Q rho) :=
  polyCofixUnfold_precomp (polyScale TA Q)
    (polyGSOSDistLaw_mul_srcCoalg A P Q rho)
    (polyGSOSScaleCoalg A P Q rho)
    ⟨mu_DQ, mu_hom_h⟩

have rhs_eq1 :
    polyGSOSDistLawMor TA P Q rho ≫
    polyCofreeMap TTA TA Q mu_A =
    polyCofixUnfold (polyScale TA Q)
      (polyGSOSDistLaw_mul_rhsCoalg A P Q rho) :=
  polyScaleReindex TTA TA Q mu_A
    (polyGSOSScaleCoalg TA P Q rho)

have rhs_eq2 :
    polyFreeMap DQ (polyCofreeCarrier TA Q) P
      (polyGSOSDistLawMor A P Q rho) ≫
    polyCofixUnfold (polyScale TA Q)
      (polyGSOSDistLaw_mul_rhsCoalg A P Q rho) =
    polyCofixUnfold (polyScale TA Q)
      (polyGSOSDistLaw_mul_srcCoalg A P Q rho) :=
  polyCofixUnfold_precomp (polyScale TA Q)
    (polyGSOSDistLaw_mul_srcCoalg A P Q rho)
    (polyGSOSDistLaw_mul_rhsCoalg A P Q rho)
    ⟨T_P_dist, tdist_hom_h⟩

dsimp only []
rw [lhs_eq, rhs_eq1, rhs_eq2]
```

Template: lines 2354-2410.

**Dependencies**: MU-3, MU-4.

Commit: "GSOS multiplication coherence proof"

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

Mark E2 as completed in
`polynomial-algebra-coalgebra-combinators.md`.
Update this file to reflect completion.

---

## Implementation order summary

| Phase | Lemma | Lines | Deps |
| ----- | ----- | ----- | ---- |
| N | NatTrans packaging | ~30 | naturality |
| CM-0 | Abbreviations | ~30 | -- |
| CM-1 | Annotation eq | ~15 | comonad law |
| CM-2 | Leaf approx | ~150 | CM-1, unit |
| CM-3 | Node approx | ~100 | CM-1, QIndex |
| CM-4 | Main induction | ~25 | CM-2, CM-3 |
| CM-5 | Assembly | ~35 | CM-4 |
| MU-1 | Src coalgebra | ~80 | fold |
| MU-2 | RHS coalgebra | ~10 | scaleCoalg |
| MU-H | mu nat at eps | ~25 | free monad |
| MU-3 | mu_hom_h | ~150 | MU-1 |
| MU-4 | tdist_hom_h | ~250 | MU-1,2,counit |
| MU-5 | Assembly | ~50 | MU-3, MU-4 |
| PK-1 | DistributiveLaw | ~40 | all above |
| PK-2 | Operational monad | ~5 | PK-1 |
| | **Total** | **~995** | |

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

### Eq.trans chain pattern (for leaf cases)

```lean
refine Eq.trans ?lhs_eq (Eq.trans ?ih_eq ?rhs_eq)
```

Split proof into three phases: transform LHS, apply IH,
transform RHS.

### Sigma extraction pattern (for coalgebra morphisms)

```lean
obtain ⟨rfl, h₂⟩ := Sigma.mk.inj h
obtain ⟨rfl, h₃⟩ := Sigma.mk.inj (eq_of_heq h₂)
```

Extract components from nested sigma equalities.

### polyCofixUnfold_precomp assembly pattern

```lean
have lhs := polyCofixUnfold_precomp _ src dst ⟨f, hom_h⟩
have rhs1 := polyScaleReindex ...
have rhs2 := polyCofixUnfold_precomp _ src rhs ⟨g, hom_h'⟩
rw [lhs, rhs1, rhs2]
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
| `polyCofixApprox_intro_polyScale_congr` | 514 | CM-3 |
| `polyCofixUnfoldApprox_input_heq` | 498 | CM-2 |
| `polyCofixUnfold_coalg_comm` | 2085 | MU-4 |
| `polyCofixUnfold_coalg_comm_child_fst_eq` | 1646 | CM-2 |
| `polyCofixUnfoldAt_children_heq` | 1824 | CM-2 |
| `polyCofreeMapApprox` | 6175 | CM-2 |
| `polyCoalgUnitApprox` | 6695 | CM-2 |
| `polyCoalgUnit_family_eq` | 6888 | CM-2 |
| `polyCoalgUnitAt_children_heq` | 7170 | CM-2 |
| `polyCofreeCounit_naturality` | 6658 | MU-4a |

### From PolyDistributiveLaw.lean

| Lemma | Line | Use |
| ----- | ---- | --- |
| `polyScaleReindex_approx` | 851 | CM-2,3 |
| `polyScaleReindex` | 880 | MU-5 |
| `polyCofixUnfold_precomp` | 1688 | MU-5 |
| `polyFreeMJoinMor` | 1542 | MU-1 |
| `polyFreeMPure_cofree_sigma_eq` | 1229 | CM-2 |

### From PolyGSOS.lean (existing)

| Lemma | Use |
| ----- | --- |
| `polyGSOSDistLaw_counit` | MU-4a |
| `polyGSOSDistLaw_unit_approx` | CM-2 |
| `polyGSOSFoldQIndex_eq` | CM-3, MU-3 |
| `polyGSOSFoldQeval_natural` | MU-4 |
| `polyBetweenEvalMap_mor_apply` | MU-4 |
| `polyGSOSFoldCata_snd_fst_eq` | MU-3 |
