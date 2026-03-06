# GSOS Coherence Proofs Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.  Use lean4:prove or
> lean4:autoprove for theorem proving steps.

**Goal:** Prove coherence axioms for the GSOS distributive law
and package it as a `DistributiveLaw` instance, completing the
GSOS work in `GebLean/PolyGSOS.lean`.

**Architecture:** Each coherence proof follows the pattern from
the P=Q case in `PolyDistributiveLaw.lean`: reduce to
depth-indexed approximation equality via `PolyCofix.ext`, then
induct on depth with leaf/node case analysis.  The GSOS case
differs in using separate polynomials P (signature) and Q
(behavior) connected by a GSOS rule `rho`.

**Tech Stack:** Lean 4, mathlib category theory, existing
`GebLean` polynomial infrastructure.

---

## Pre-task: Fix current build errors

Before proceeding with coherence proofs, the staged code in
`GebLean/PolyGSOS.lean` has three errors and two holes that
must be resolved.  See
`.session/workstreams/gsos-distributive-law.md` for detailed
fix instructions.

Summary:

1. Fix `mor_to_pbe_fiber_index_postcomp` (generalize failure)
2. Fix reversed equality in invFun_natural fst case
3. Fill invFun_natural snd case (HEq of morphisms)
4. Write `polyBetweenComp_eval_toFun_natural` (new lemma)
5. Write join naturality lemma (new lemma)
6. Assemble `polyGSOSFoldNodeAt_snd_natural` (pipeline chain)
7. Fill `polyGSOSScaleCoalg_morphism_h` Q-children
8. Build checkpoint

---

## Reference: Existing Infrastructure

### File: `GebLean/PolyGSOS.lean` (current state, 1323 lines)

Definitions already present and compiling:

- `PolyGSOSRule P Q` --- GSOS rule structure
- `polyGSOSFoldLeafAt` --- leaf handler for fold
- `polyGSOSFoldNodeAt` --- node handler for fold
- `polyGSOSFoldCataWithFiber` --- catamorphism with fiber
- `polyGSOSFoldCata` --- fold as Over X morphism
- `polyGSOSScaleCoalgStrAt` --- scale coalgebra structure
- `polyGSOSScaleCoalgStr` --- scale coalgebra structure map
- `polyGSOSScaleCoalg` --- the PolyCoalg instance
- `polyGSOSDistLawMor` --- distributive law morphism
- `polyGSOSDistLawMor_head_fst` --- head annotation lemma
- `polyGSOSDistLaw_counit` --- counit coherence (done)
- `polyGSOSDistLaw_unit_approx` --- depth-indexed unit
- `polyGSOSDistLaw_unit` --- unit coherence (done)
- `polyGSOSDistLaw_annot_natural` --- annotation naturality
- `polyGSOSFoldQIndex_eq` --- Q-index naturality
- `polyGSOSFoldFst_natural` --- fold fst naturality
- `polyGSOSFoldLeafAt_snd_natural` --- leaf Q-eval nat
- `polyGSOSScaleCoalg_morphism_h` --- leaf case done
- `polyGSOSDistLaw_naturality` --- compiles given morphism_h

### Reusable helper lemmas (parametric)

From `PolyDistributiveLaw.lean`:

- `polyFreeMonad_eta_eq` (line 2415)
- `polyFreeMonad_mu_eq` (line 1596)
- `polyFreeMonad_map_eq` (line 1608)
- `polyCofreeComonad_eps_eq` (line 2427)
- `polyCofreeComonad_delta_eq` (line 2439)
- `polyCofreeComonad_map_eq` (line 2451)

Instantiate monad lemmas with P, comonad lemmas with Q.

From `PolyDistributiveLaw.lean` (structural):

- `polyCofixUnfold_precomp` (line 1688)
- `polyScaleReindex` (line 880)
- `polyCofixUnfoldApprox_input_heq` (line 498)
- `polyCofixApprox_intro_polyScale_congr` (line 514)

### Target structure: `DistributiveLaw`

```text
structure DistributiveLaw (T : Monad C) (D : Comonad C)
  dist : D.toFunctor ⋙ T.toFunctor ⟶
    T.toFunctor ⋙ D.toFunctor
  unit : forall X,
    T.eta.app (D.obj X) ≫ dist.app X =
    D.map (T.eta.app X)
  mul : forall X,
    T.mu.app (D.obj X) ≫ dist.app X =
    T.map (dist.app X) ≫ dist.app (T.obj X) ≫
    D.map (T.mu.app X)
  counit : forall X,
    dist.app X ≫ D.eps.app (T.obj X) =
    T.map (D.eps.app X)
  comul : forall X,
    T.map (D.delta.app X) ≫
    dist.app (D.obj X) ≫
    D.map (dist.app X) =
    dist.app X ≫ D.delta.app (T.obj X)
```

---

## Task 1: Complete naturality (pre-task + NatTrans)

**Files:** Modify `GebLean/PolyGSOS.lean`

See `.session/workstreams/gsos-distributive-law.md` for the
detailed fix plan with intermediate lemma signatures.

After fixes, write NatTrans packaging:

```lean
def polyGSOSDistLawNatApp
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    ((polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).obj A ⟶
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor).obj A :=
  polyGSOSDistLawMor A P Q rho

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

def polyGSOSDistLawNat
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    (polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor ⟶
    (polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor where
  app := fun A =>
    polyGSOSDistLawNatApp A P Q rho
  naturality := fun {A B} f =>
    polyGSOSDistLawNat_naturality A B P Q rho f
```

Build, then commit:
"GSOS naturality proof and NatTrans packaging"

---

## Task 2: Comultiplication proof

**Files:** Modify `GebLean/PolyGSOS.lean`

### Intermediate lemmas (factored out)

#### Lemma CM-1: Annotation equality

```lean
lemma polyGSOSDistLaw_comul_annot_eq
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    polyFreeMapAt ... (polyCofreeCounit A Q ≫ ...)
      x (polyFreeMapAt ...
        (polyCoalgUnit Q ...) x t) =
    polyFreeMapAt ... (polyCofreeCounit A Q) x t
```

Uses: `polyCofree_left_triangle` (eps . delta = id),
`polyFreeMapAt_comp`.

~20 lines. Template: `polyDistLaw_comul_annot_eq`.

#### Lemma CM-2: Leaf approximation

```lean
lemma polyGSOSDistLaw_comul_approx_leaf
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (c : { v : (polyCofreeCarrier A Q).left //
      (polyCofreeCarrier A Q).hom v = x })
    (n : Nat)
    (ih : <depth-n IH for all trees>) :
    <LHS approx at leaf, depth n+1> =
    <RHS approx at leaf, depth n+1>
```

Uses: `polyGSOSDistLaw_unit_approx`, comonad laws,
`polyCofreeMapApprox` properties.

~170 lines. Template: `polyDistLaw_comul_approx_leaf`.

#### Lemma CM-3: Node approximation

```lean
lemma polyGSOSDistLaw_comul_approx_node
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (pIdx : polyBetweenIndex X X P x)
    (children : ...) (n : Nat)
    (ih : <depth-n IH for all trees>) :
    <LHS approx at node, depth n+1> =
    <RHS approx at node, depth n+1>
```

Uses: CM-1 for annotation,
`polyGSOSFoldQIndex` properties for Q-index,
`polyCofixApprox_intro_polyScale_congr`, IH for children.

~110 lines. Template: `polyDistLaw_comul_approx_node`.

#### Lemma CM-4: Main induction

```lean
lemma polyGSOSDistLaw_comul_approx
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x)
    (n : Nat) :
    <LHS approx at t, depth n> =
    <RHS approx at t, depth n>
```

Induction on n, dispatching to CM-2/CM-3.

~30 lines. Template: `polyDistLaw_comul_approx`.

### Main theorem

```lean
lemma polyGSOSDistLaw_comul
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeMap (polyCofreeCarrier A Q)
      (polyCofreeCarrier
        (polyCofreeCarrier A Q) Q) P
      (polyCoalgUnit Q
        (polyCofreeCoalg A Q)) ≫
    polyGSOSDistLawMor
      (polyCofreeCarrier A Q) P Q rho ≫
    polyCofreeMap
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) Q) Q
      (polyGSOSDistLawMor A P Q rho) =
    polyGSOSDistLawMor A P Q rho ≫
    polyCoalgUnit Q
      (polyCofreeCoalg
        (polyFreeMCarrier A P) Q)
```

Proof: `Over.OverMorphism.ext`, `funext`, `Sigma.ext`,
`PolyCofix.ext`, `intro n`, apply CM-4.

~40 lines. Template: `polyDistLaw_comul`.

Build, then commit:
"GSOS comultiplication coherence proof"

---

## Task 3: Multiplication proof

**Files:** Modify `GebLean/PolyGSOS.lean`

### Source coalgebra definition

#### Sub-lemma MU-1: Source coalgebra structure

```lean
def polyGSOSDistLaw_mul_srcCoalgStrAt
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P) P x) :
    polyBetweenEvalFamily X X
      (polyScale (polyFreeMCarrier A P) Q)
      (polyFreeMCarrier
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P) P) x
```

Combines:

- Annotation: `T_P(eps_Q)(mu(t))`
- Q-structure: fold(mu(t)), with Q-children embedded
  into `T_P(T_P(D_Q(A)))` via `polyFreeUnit` (eta)

The eta embedding is the technique that makes
`Scale.map(mu)` recover the original Q-children via
`mu . eta = id` (monad left unit law).

~20 lines. Template: `polyDistLaw_mul_srcCoalgStrAt`.

#### Sub-lemma MU-1b: Packaging (~60 lines)

- `polyGSOSDistLaw_mul_srcCoalgStrLeft`
- `polyGSOSDistLaw_mul_srcCoalgStr_comm`
- `polyGSOSDistLaw_mul_srcCoalgStr`
- `polyGSOSDistLaw_mul_srcCoalg`

Template: lines 1783-1842.

### RHS coalgebra definition

```lean
def polyGSOSDistLaw_mul_rhsCoalg
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    PolyCoalg
      (polyScale (polyFreeMCarrier A P) Q) :=
  polyScaleReindexCoalg
    (polyFreeMCarrier
      (polyFreeMCarrier A P) P)
    (polyFreeMCarrier A P) Q
    (polyFreeCounitFold P (polyFreeAlg A P))
    (polyGSOSScaleCoalg
      (polyFreeMCarrier A P) P Q rho)
```

~10 lines. Template: line 1630.

### Coalgebra morphism conditions

#### Sub-lemma MU-3: mu_hom_h (~180 lines)

```lean
lemma polyGSOSDistLaw_mu_hom_h
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    (polyGSOSDistLaw_mul_srcCoalg
      A P Q rho).str ≫
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) Q)).map
      (polyFreeCounitFold P
        (polyFreeAlg
          (polyCofreeCarrier A Q) P)) =
    polyFreeCounitFold P
      (polyFreeAlg
        (polyCofreeCarrier A Q) P) ≫
    (polyGSOSScaleCoalg A P Q rho).str
```

This says mu is a coalgebra morphism. The proof
by induction on tree t has:

**Node case**: `mu(node(p, ch)) = node(p, mu . ch)`.
Both sides compute `fold(node(p, mu(ch_e)))` which
is `nodeHandler(p, fold(mu(ch_e)))`. The srcCoalg
embeds Q-children via eta; after `Scale.map(mu)`,
`mu(eta(child)) = child` by left unit. Annotation
matches by `polyFreeMapAt_comp` and mu's node behavior.

**Leaf case**: `mu(leaf(a)) = a.val.2` (inner tree).
Both sides compute `fold(a.val.2)`. Q-children:
srcCoalg embeds via eta; `mu(eta(child)) = child`.
Annotation matches since `T_P(eps_Q)(mu(leaf(a)))` =
`T_P(eps_Q)(a.val.2)`.

**Sub-lemmas to factor out**:

- mu_hom_h_node_annot: annotation equality at nodes
- mu_hom_h_node_qidx: Q-index equality at nodes
- mu_hom_h_leaf: full leaf case
- mu_hom_h_node_qchildren: Q-children after mu.eta=id

Template: lines 1868-2047.

#### Sub-lemma MU-4: tdist_hom_h (~300 lines)

```lean
lemma polyGSOSDistLaw_tdist_hom_h
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    (polyGSOSDistLaw_mul_srcCoalg
      A P Q rho).str ≫
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) Q)).map
      (polyFreeMap
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier
          (polyFreeMCarrier A P) Q) P
        (polyGSOSDistLawMor A P Q rho)) =
    polyFreeMap
      (polyCofreeCarrier A Q)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) Q) P
      (polyGSOSDistLawMor A P Q rho) ≫
    (polyGSOSDistLaw_mul_rhsCoalg
      A P Q rho).str
```

This says `T_P(dist)` is a coalgebra morphism. The proof
uses:

- Counit coherence for annotation:
  `T_P(eps_Q)(T_P(dist)(t))` =
  `T_P(eps_Q . dist)(t)` = `T_P(T_P(eps_Q))(t)`
  by `polyGSOSDistLaw_counit` and `polyFreeMapAt_comp`.
- `polyCofixUnfold_coalg_comm` for Q-structure.
- Induction on tree for pointwise equality.

**Sub-lemmas to factor out**:

- tdist_hom_h_node_annot: annotation at nodes
- tdist_hom_h_node_qstructure: Q-structure at nodes
- tdist_hom_h_leaf: full leaf case

Template: lines 2048-2353.

### Task's Main theorem

```lean
lemma polyGSOSDistLaw_mul
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeCounitFold P
      (polyFreeAlg
        (polyCofreeCarrier A Q) P) ≫
    polyGSOSDistLawMor A P Q rho =
    polyFreeMap
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) Q) P
      (polyGSOSDistLawMor A P Q rho) ≫
    polyGSOSDistLawMor
      (polyFreeMCarrier A P) P Q rho ≫
    polyCofreeMap
      (polyFreeMCarrier
        (polyFreeMCarrier A P) P)
      (polyFreeMCarrier A P) Q
      (polyFreeCounitFold P
        (polyFreeAlg A P))
```

Assembly via `polyCofixUnfold_precomp`:

1. `lhs_eq`: `mu ≫ dist = polyCofixUnfold srcCoalg`
   (by mu_hom_h)
2. `rhs_eq1`: `dist_{TA} ≫ D_Q(mu) =
   polyCofixUnfold rhsCoalg` (by `polyScaleReindex`)
3. `rhs_eq2`: `T(dist) ≫ polyCofixUnfold rhsCoalg =
   polyCofixUnfold srcCoalg` (by tdist_hom_h)
4. Conclude: `lhs = polyCofixUnfold srcCoalg = rhs`

~60 lines. Template: lines 2354-2410.

Build, then commit:
"GSOS multiplication coherence proof"

---

## Task 4: Final packaging

**Files:** Modify `GebLean/PolyGSOS.lean`

### Step 4-1: DistributiveLaw instance

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

### Step 4-2: Operational monad

```lean
def polyGSOSOperationalMonad
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    Monad
      (polyCofreeComonad X Q).Coalgebra :=
  liftedMonad
    (polyGSOSDistributiveLaw P Q rho)
```

### Step 4-3: Full build and test

```bash
lake build && lake test
```

### Step 4-4: Commit

"GSOS distributive law and operational monad"

### Step 4-5: Update session documents

Mark E1 and E2 as completed in
`polynomial-algebra-coalgebra-combinators.md`.

---

## Estimated effort

| Task | Estimated lines | Difficulty |
| ---- | -------------- | ---------- |
| 1. Naturality (fix + NatTrans) | ~280 | Medium |
| 2. Comultiplication | ~450 | High |
| 3. Multiplication | ~650 | Very high |
| 4. Packaging | ~60 | Low |
| **Total** | **~1440** | |

## Notes for implementer

- All proofs follow the same outer shell: `Over` ext,
  `Sigma` ext, `PolyCofix` ext, depth induction.
- Use underscores (`_`) liberally to check intermediate
  goal types.
- When `simp` does not close a goal, try `unfold`/`show`
  to make the goal explicit, then proceed manually.
- The P=Q template proofs in `PolyDistributiveLaw.lean`
  are the primary reference for every step.
- The GSOS-specific differences are in the fold handlers
  (`polyGSOSFoldLeafAt`, `polyGSOSFoldNodeAt`) which use
  the GSOS rule `rho` --- trace through these when
  adapting from the P=Q template.
- Helper lemmas from `PolyDistributiveLaw.lean` like
  `polyCofixUnfoldApprox_input_heq` and
  `polyCofixApprox_intro_polyScale_congr` are parametric
  and can be applied directly.
- The multiplication proof's source coalgebra embeds
  fold Q-children via `polyFreeUnit` (eta) so that
  `Scale.map(mu)` recovers them via `mu . eta = id`.
  This is the central design choice for MU-1.
- When a proof exceeds ~30 lines, factor out helper
  lemmas using the factoring-out-lemmas technique from
  CLAUDE.md.
- For HEq goals from dependent types, use the pattern:
  establish index equality first, then cast HEq to Eq
  using `heq_of_eq` or `heq_iff_eq`.
