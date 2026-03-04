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

## Reference: Existing Infrastructure

### File: `GebLean/PolyGSOS.lean` (current state, 389 lines)

Definitions already present:

- `PolyGSOSRule P Q` — GSOS rule structure
- `polyGSOSFoldLeafAt` — leaf handler for fold
- `polyGSOSFoldNodeAt` — node handler for fold
- `polyGSOSFoldCataWithFiber` — catamorphism with fiber
  proof
- `polyGSOSFoldCata` — fold as Over X morphism
- `polyGSOSScaleCoalgStrAt` — scale coalgebra structure
  at a point
- `polyGSOSScaleCoalgStr` — scale coalgebra structure map
- `polyGSOSScaleCoalg` — the PolyCoalg instance
- `polyGSOSDistLawMor` — distributive law morphism via
  `polyCofixUnfold`

### File: `GebLean/PolyDistributiveLaw.lean` (template)

Reusable helper lemmas (parametric in polynomial argument):

- `polyFreeMonad_eta_eq` (line 2415):
  `(polyFreeMonad X P).eta.app A = polyFreeUnit A P`
- `polyFreeMonad_mu_eq` (line 1596):
  `(polyFreeMonad X P).mu.app A = polyFreeCounitFold P
  (polyFreeAlg A P)`
- `polyFreeMonad_map_eq` (line 1608):
  `(polyFreeMonad X P).toFunctor.map f =
  polyFreeMap A B P f`
- `polyCofreeComonad_eps_eq` (line 2427):
  `(polyCofreeComonad X P).eps.app A =
  polyCofreeCounit A P`
- `polyCofreeComonad_delta_eq` (line 2439):
  `(polyCofreeComonad X P).delta.app A =
  polyCoalgUnit P (polyCofreeCoalg A P)`
- `polyCofreeComonad_map_eq` (line 2451):
  `(polyCofreeComonad X P).toFunctor.map f =
  polyCofreeMap A B P f`

For GSOS: instantiate monad lemmas with P, comonad lemmas
with Q.

### File: `GebLean/PolyAlg.lean`

- `polyCofixUnfold` (line 1378): anamorphism from coalgebra
  to terminal coalgebra
- `polyCofixUnfoldAt` (line 1355): pointwise anamorphism
- `polyCofixUnfoldApprox` (line 1281): depth-indexed
  approximation
- `PolyCofix.ext` (line 1026): extensionality via
  approximations
- `polyCofreeMapApprox` (line 6175): depth-indexed cofree
  map
- `polyCofreeMapAt_head_snd` (line 6264): cofree map
  preserves Q-index
- `polyCofixUnfold_coalg_comm` (line 2085): coalgebra
  morphism condition for anamorphism
- `polyCofreeCounit_naturality` (in PolyAlg.lean):
  naturality of epsilon_Q

### File: `GebLean/PolyDistributiveLaw.lean`

- `polyCofixUnfold_precomp` (line 1688):
  `g.f >> polyCofixUnfold P beta =
  polyCofixUnfold P alpha`
  (when g is a coalgebra morphism alpha -> beta)
- `polyScaleReindex` (line 880):
  `polyCofixUnfold >> polyCofreeMap f =
  polyCofixUnfold (reindexed coalgebra)`
- `polyCofixUnfoldApprox_input_heq` (line 498): HEq
  for approx with equal inputs
- `polyCofixApprox_intro_polyScale_congr` (line 514):
  equality of .intro when components match

### File: `GebLean/Utilities/DistributiveLaw.lean`

Target structure:

```
structure DistributiveLaw (T : Monad C) (D : Comonad C)
  dist : D.toFunctor >> T.toFunctor --> T.toFunctor >> D.toFunctor
  unit : forall X,
    T.eta.app (D.obj X) >> dist.app X =
    D.map (T.eta.app X)
  mul : forall X,
    T.mu.app (D.obj X) >> dist.app X =
    T.map (dist.app X) >> dist.app (T.obj X) >>
    D.map (T.mu.app X)
  counit : forall X,
    dist.app X >> D.eps.app (T.obj X) =
    T.map (D.eps.app X)
  comul : forall X,
    T.map (D.delta.app X) >>
    dist.app (D.obj X) >>
    D.map (dist.app X) =
    dist.app X >> D.delta.app (T.obj X)
```

---

## Task 1: Counit proof

**Files:**

- Modify: `GebLean/PolyGSOS.lean` (append after
  `polyGSOSDistLawMor`, before `end GebLean`)

**Step 1: Write `polyGSOSDistLawMor_head_fst`**

This lemma states that the head annotation of the
anamorphism output equals `T_P(eps_Q)` applied to
the input.

Type signature:

```lean
lemma polyGSOSDistLawMor_head_fst
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    let m := polyCofixUnfoldAt
      (polyScale (polyFreeMCarrier A P) Q)
      (polyGSOSScaleCoalg A P Q rho)
      x ⟨⟨x, t⟩, rfl⟩
    (polyCofreeExtract
      (polyFreeMCarrier A P) Q m).val =
    ⟨x, polyFreeMapAt
      (polyCofreeCarrier A Q) A P
      (polyCofreeCounit A Q) x t⟩
```

Strategy: Unfold `polyCofixUnfoldAt` and
`polyGSOSScaleCoalgStrAt`.  The annotation field is
constructed as `polyFreeMapAt ... (polyCofreeCounit A Q)
x t` by definition.  Should be `rfl` or near-`rfl`.

Build and fix errors.

**Step 2: Write `polyGSOSDistLaw_counit`**

Type signature:

```lean
lemma polyGSOSDistLaw_counit
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyGSOSDistLawMor A P Q rho ≫
    polyCofreeCounit (polyFreeMCarrier A P) Q =
    polyFreeMap
      (polyCofreeCarrier A Q) A P
      (polyCofreeCounit A Q)
```

Strategy: `Over.OverMorphism.ext`, `funext`,
`simp only` with unfolding lemmas for
`polyCofixUnfold`, `polyCofreeCounit`, `polyFreeMap`,
then apply `polyGSOSDistLawMor_head_fst`.

Template: `polyDistLaw_counit` (PolyDistributiveLaw.lean
line 280, ~15 lines).

Build and fix errors.

**Step 3: Commit**

```
git add GebLean/PolyGSOS.lean
git commit -m "GSOS counit coherence proof"
```

---

## Task 2: Unit proof

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

**Step 1: Write `polyGSOSDistLaw_unit_approx`**

Type signature:

```lean
lemma polyGSOSDistLaw_unit_approx
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (m : PolyCofreeM A Q x) (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier A P) Q)
      (polyGSOSScaleCoalg A P Q rho) n x
      ⟨⟨x, polyFreeMPure
        (polyCofreeCarrier A Q) P
        ⟨⟨x, m⟩, rfl⟩⟩, rfl⟩ =
    polyCofreeMapApprox A
      (polyFreeMCarrier A P) Q
      (polyFreeUnit A P) (m.approx n)
```

Strategy: Induction on `n`.

- Base (n=0): both sides are `.continue`/`.trunc`, `rfl`
  or simple simp.
- Succ (n+1): The input is `polyFreeMPure(cofree elem)`.
  The fold of a pure leaf is `polyGSOSFoldLeafAt`.
  The scale coalgebra structure at this leaf gives:
  - annotation:
    `T_P(eps_Q)(eta(m)) = eta(eps_Q(m)) = eta(head(m))`
  - Q-index: `m.head.2` (preserved by fold leaf handler)
  - children: recursive call on `m.children e`

  The RHS unfolds `polyCofreeMapApprox` on `m.approx
  (n+1)`, which maps each annotation via `polyFreeUnit`
  and recurses on children.

  Show annotation equality and children equality (IH).

Template: `polyDistLaw_unit_approx`
(PolyDistributiveLaw.lean line 334, ~100 lines).

Build and fix errors.

**Step 2: Write `polyGSOSDistLaw_unit`**

Type signature:

```lean
lemma polyGSOSDistLaw_unit
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeUnit (polyCofreeCarrier A Q) P ≫
    polyGSOSDistLawMor A P Q rho =
    polyCofreeMap A
      (polyFreeMCarrier A P) Q
      (polyFreeUnit A P)
```

Strategy: `Over.OverMorphism.ext`, `funext`,
`Sigma.ext` (fiber is `rfl`), `PolyCofix.ext`,
`intro n`, apply `polyGSOSDistLaw_unit_approx`.

Template: `polyDistLaw_unit` (line 431, ~20 lines).

Build and fix errors.

**Step 3: Commit**

```
git add GebLean/PolyGSOS.lean
git commit -m "GSOS unit coherence proof"
```

---

## Task 3: Naturality proof

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

**Step 1: Write `polyGSOSDistLaw_annot_natural`**

Type signature:

```lean
lemma polyGSOSDistLaw_annot_natural
    (A B : Over X) (P Q : PolyEndo X)
    (f : A ⟶ B) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    polyFreeMapAt
      (polyCofreeCarrier B Q) B P
      (polyCofreeCounit B Q) x
      (polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x t) =
    polyFreeMapAt A B P f x
      (polyFreeMapAt
        (polyCofreeCarrier A Q) A P
        (polyCofreeCounit A Q) x t)
```

Strategy: `rw [polyFreeMapAt_comp (both sides)]`,
`congr 1`, `exact polyCofreeCounit_naturality A B Q f`.

Template: `polyDistLaw_annot_natural`
(PolyDistributiveLaw.lean line 474, ~10 lines).

Build and fix errors.

**Step 2: Write `polyGSOSDistLaw_naturality_approx_leaf`**

This handles the leaf case of the depth-indexed
naturality proof.

Type signature (analogous to
`polyDistLaw_naturality_approx_leaf` at line 544):

```lean
lemma polyGSOSDistLaw_naturality_approx_leaf
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) {x : X}
    (c : { a //
      (polyCofreeCarrier A Q).hom a = x })
    (n : Nat)
    (ih : forall {x : X}
      (t : PolyFreeM
        (polyCofreeCarrier A Q) P x),
      polyCofixUnfoldApprox
        (polyScale (polyFreeMCarrier B P) Q)
        (polyGSOSScaleCoalg B P Q rho) n x
        ⟨⟨x, polyFreeMapAt
          (polyCofreeCarrier A Q)
          (polyCofreeCarrier B Q) P
          (polyCofreeMap A B Q f) x t⟩, rfl⟩ =
      polyCofreeMapApprox
        (polyFreeMCarrier A P)
        (polyFreeMCarrier B P) Q
        (polyFreeMap A B P f)
        (polyCofixUnfoldApprox
          (polyScale (polyFreeMCarrier A P) Q)
          (polyGSOSScaleCoalg A P Q rho) n x
          ⟨⟨x, t⟩, rfl⟩)) :
    <goal for leaf at depth n+1>
```

Strategy: Unfold definitions for the leaf case.  The
fold of a leaf produces `polyGSOSFoldLeafAt`, whose
annotation and Q-structure commute with `f` via
`polyGSOSDistLaw_annot_natural` and the leaf handler's
construction.  Use `polyCofixApprox_intro_polyScale_congr`
and IH on children.

Build and fix errors.

**Step 3: Write `polyGSOSDistLaw_naturality_approx`**

Type signature:

```lean
lemma polyGSOSDistLaw_naturality_approx
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x)
    (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier B P) Q)
      (polyGSOSScaleCoalg B P Q rho) n x
      ⟨⟨x, polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x t⟩, rfl⟩ =
    polyCofreeMapApprox
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) Q
      (polyFreeMap A B P f)
      (polyCofixUnfoldApprox
        (polyScale (polyFreeMCarrier A P) Q)
        (polyGSOSScaleCoalg A P Q rho) n x
        ⟨⟨x, t⟩, rfl⟩)
```

Strategy: Induction on `n`.

- Base: trivial.
- Succ: match on `t`.
  - Node `(Sum.inr pIdx) children`:
    Show annotation equality via
    `polyGSOSDistLaw_annot_natural`.
    Show Q-index equality (preserved by fold node
    handler).
    Show children equality via IH.
  - Leaf `(Sum.inl c) _`:
    Apply `polyGSOSDistLaw_naturality_approx_leaf`.

Template: `polyDistLaw_naturality_approx`
(PolyDistributiveLaw.lean line 718, ~100 lines).

Build and fix errors.

**Step 4: Write `polyGSOSDistLaw_naturality`**

Type signature:

```lean
lemma polyGSOSDistLaw_naturality
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) :
    polyFreeMap
      (polyCofreeCarrier A Q)
      (polyCofreeCarrier B Q) P
      (polyCofreeMap A B Q f) ≫
    polyGSOSDistLawMor B P Q rho =
    polyGSOSDistLawMor A P Q rho ≫
    polyCofreeMap
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) Q
      (polyFreeMap A B P f)
```

Strategy: `Over.OverMorphism.ext`, `funext`,
`Sigma.ext` (fiber `rfl`), `PolyCofix.ext`, `intro n`,
apply `polyGSOSDistLaw_naturality_approx`.

Build and fix errors.

**Step 5: Write NatTrans packaging**

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
      (polyCofreeComonad X Q).toFunctor).map f

def polyGSOSDistLawNat
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    (polyCofreeComonad X Q).toFunctor ⋙
      (polyFreeMonad X P).toFunctor ⟶
    (polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X Q).toFunctor where
  app := fun A => polyGSOSDistLawNatApp A P Q rho
  naturality := fun {A B} f =>
    polyGSOSDistLawNat_naturality A B P Q rho f
```

Build and fix errors.

**Step 6: Commit**

```
git add GebLean/PolyGSOS.lean
git commit -m "GSOS naturality proof and NatTrans"
```

---

## Task 4: Comultiplication proof

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

**Step 1: Write annotation equality lemma**

```lean
lemma polyGSOSDistLaw_comul_annot_eq
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    <annotation of LHS at t = annotation of RHS at t>
```

The LHS applies `T_P(delta)` then `dist_{D_Q(A)}` then
`D_Q(dist)`.  The RHS applies `dist` then
`delta_{T_P(A)}`.

For the annotation component, show that
`T_P(eps_Q . D_Q(eps_Q) . delta) =
T_P(eps_Q)` (since `eps . delta = id` by comonad law).

Build and fix errors.

**Step 2: Write leaf approximation lemma**

```lean
lemma polyGSOSDistLaw_comul_approx_leaf
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (c : { a //
      (polyCofreeCarrier A Q).hom a = x })
    (n : Nat)
    (ih : <inductive hypothesis>) :
    <leaf case at depth n+1>
```

Build and fix errors.

**Step 3: Write node approximation lemma**

```lean
lemma polyGSOSDistLaw_comul_approx_node
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (pIdx : polyBetweenIndex X X P x)
    (children : ...) (n : Nat)
    (ih : <inductive hypothesis>) :
    <node case at depth n+1>
```

Build and fix errors.

**Step 4: Write `polyGSOSDistLaw_comul_approx`**

Depth-indexed induction combining leaf and node cases.

Build and fix errors.

**Step 5: Write `polyGSOSDistLaw_comul`**

Type signature:

```lean
lemma polyGSOSDistLaw_comul
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeMap (polyCofreeCarrier A Q)
      (polyCofreeCarrier
        (polyCofreeCarrier A Q) Q) P
      (polyCoalgUnit Q (polyCofreeCoalg A Q)) ≫
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

Strategy: `Over.OverMorphism.ext`, `funext`,
`Sigma.ext`, `PolyCofix.ext`, `intro n`, apply
`polyGSOSDistLaw_comul_approx`.

Build and fix errors.

**Step 6: Commit**

```
git add GebLean/PolyGSOS.lean
git commit -m "GSOS comultiplication coherence proof"
```

---

## Task 5: Multiplication proof

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

**Step 1: Define LHS coalgebra structure**

The LHS `mu_{D_Q(A)} >> dist` composes monad
multiplication with the distributive law.  Express this as
an anamorphism by showing `T_P(T_P(D_Q(A)))` carries a
`polyScale(T_P(A), Q)`-coalgebra structure via the fold
applied to the flattened tree.

```lean
def polyGSOSDistLaw_mu_coalg
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    PolyCoalg (polyScale (polyFreeMCarrier A P) Q)
```

where the carrier is
`polyFreeMCarrier (polyFreeMCarrier
  (polyCofreeCarrier A Q) P) P`
(i.e., `T_P(T_P(D_Q(A)))`) and the structure map
combines `mu` with the scale coalgebra.

Build and fix errors.

**Step 2: Prove LHS coalgebra homomorphism**

Show that `polyFreeCounitFold` (monad multiplication)
is a coalgebra morphism from `polyGSOSDistLaw_mu_coalg`
to `polyGSOSScaleCoalg`.

```lean
lemma polyGSOSDistLaw_mu_hom
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    <mu is a coalgebra morphism>
```

This requires showing the fold commutes with the scale
coalgebra structure.

Build and fix errors.

**Step 3: Define RHS coalgebra structure**

The RHS `T_P(dist) >> dist_{T_P(A)} >> D_Q(mu_A)`.
Express as an anamorphism via `polyScaleReindex`.

Build and fix errors.

**Step 4: Prove RHS coalgebra condition**

Show the composition `T_P(dist) >> dist_{T_P(A)}`
followed by `D_Q(mu)` satisfies the required coalgebra
condition.

Build and fix errors.

**Step 5: Write `polyGSOSDistLaw_mul`**

Type signature:

```lean
lemma polyGSOSDistLaw_mul
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    let DQ := polyCofreeCarrier A Q
    let TA := polyFreeMCarrier A P
    let TDQ := polyFreeMCarrier DQ P
    polyFreeCounitFold P (polyFreeAlg DQ P) ≫
    polyGSOSDistLawMor A P Q rho =
    polyFreeMap TDQ
      (polyCofreeCarrier TA Q) P
      (polyGSOSDistLawMor A P Q rho) ≫
    polyGSOSDistLawMor TA P Q rho ≫
    polyCofreeMap
      (polyFreeMCarrier TA P)
      TA Q
      (polyFreeCounitFold P
        (polyFreeAlg A P))
```

Strategy: Express both sides as anamorphisms using
`polyCofixUnfold_precomp` and `polyScaleReindex`.
Show they agree because they are anamorphisms from
the same coalgebra.

Template: `polyDistLaw_mul`
(PolyDistributiveLaw.lean line 1850, ~560 lines).

Build and fix errors.

**Step 6: Commit**

```
git add GebLean/PolyGSOS.lean
git commit -m "GSOS multiplication coherence proof"
```

---

## Task 6: Final packaging

**Files:**

- Modify: `GebLean/PolyGSOS.lean`

**Step 1: Write `polyGSOSDistributiveLaw`**

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

Build and fix errors.

**Step 2: Commit and verify**

```
lake build
lake test
git add GebLean/PolyGSOS.lean
git commit -m "GSOS distributive law instance"
```

**Step 3: Update session workstream**

Update `.session/workstreams/gsos-distributive-law.md`
to reflect completion.

---

## Estimated effort

| Task | Estimated lines | Difficulty |
|------|----------------|------------|
| 1. Counit | ~30 | Low |
| 2. Unit | ~140 | Medium |
| 3. Naturality | ~250 | Medium |
| 4. Comul | ~450 | High |
| 5. Mul | ~650 | Very high |
| 6. Packaging | ~60 | Low |
| **Total** | **~1580** | |

## Notes for implementer

- All proofs follow the same outer shell: `Over` ext,
  `Sigma` ext, `PolyCofix` ext, depth induction.
- Use underscores (`_`) liberally to check intermediate
  goal types.
- When `simp` doesn't close a goal, try `unfold`/`show`
  to make the goal explicit, then proceed manually.
- The P=Q template proofs in `PolyDistributiveLaw.lean`
  are the primary reference for every step.
- The GSOS-specific differences are in the fold handlers
  (`polyGSOSFoldLeafAt`, `polyGSOSFoldNodeAt`) which use
  the GSOS rule `rho` — trace through these carefully
  when adapting from the P=Q template.
- Helper lemmas from `PolyDistributiveLaw.lean` like
  `polyCofixUnfoldApprox_input_heq` and
  `polyCofixApprox_intro_polyScale_congr` are parametric
  and can be applied directly (they take a generic
  `PolyEndo X` argument, not specifically P).
