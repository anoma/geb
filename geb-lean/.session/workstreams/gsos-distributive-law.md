# GSOS Distributive Law

## Status: Naturality in progress, coherence proofs pending

## Current build state

File: `GebLean/PolyGSOS.lean` (1226 lines)

Single compilation error at line 1021: unsolved HEq goal in
`polyGSOSFoldCata_natural`, node case, `Prod.snd` branch.
This blocks compilation of everything after line 1021,
including `polyGSOSDistLaw_naturality_approx` (which is
written but cannot be verified).

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

## Pending: detailed step-by-step plan

### Phase N: Complete naturality (unblock compilation)

#### N1. Fix polyGSOSFoldCata\_natural line 1021

The goal is showing the Q-evaluation (second component) of
`polyGSOSFoldNodeAt` commutes with `polyFreeMap`/
`polyCofreeMap`.  The first component (Prod.fst) is already
proved.

Strategy options:

- (a) Prove the HEq directly by unfolding `polyGSOSFoldNodeAt`
  and showing the GSOS rule application commutes with mapping
  (uses naturality of `rho.rule`).
- (b) Factor out `polyGSOSFoldNodeAt_snd_natural` as a helper
  lemma.

The HEq involves:

- `prodComp` naturality (the overPullback-to-polyIdBehavior
  conversion commutes with mapping)
- `polyBetweenComp_eval_fiberEquiv` commutes with mapping
- `rho.rule.app` naturality (automatic from NatTrans)
- `ccrEvalMap join` commutes with mapping

If the proof grows beyond ~30 lines, factor sub-lemmas.

Build checkpoint: `lake build GebLean.PolyGSOS` should
succeed with no errors after this step.

#### N2. Verify polyGSOSDistLaw\_naturality\_approx compiles

After N1, the file should compile.  Run `lake build` and
check for any errors in the naturality\_approx proof
(lines 1023-1224).  Fix any issues.

Build checkpoint: clean compilation.

#### N3. Write polyGSOSDistLaw\_naturality

Type signature:

```text
polyFreeMap (polyCofreeCarrier A Q) (polyCofreeCarrier B Q) P
    (polyCofreeMap A B Q f) >>
  polyGSOSDistLawMor B P Q rho =
  polyGSOSDistLawMor A P Q rho >>
  polyCofreeMap (polyFreeMCarrier A P)
    (polyFreeMCarrier B P) Q (polyFreeMap A B P f)
```

Pattern: `Over.OverMorphism.ext`, `funext`, `Sigma.ext`
(fiber `rfl`), `PolyCofix.ext`, `intro n`, apply
`polyGSOSDistLaw_naturality_approx`.

Template: `polyDistLaw_naturality`
(PolyDistributiveLaw.lean line 906, ~20 lines).

Build checkpoint: `lake build GebLean.PolyGSOS`.

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
