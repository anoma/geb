# Cotriple Bar Resolution Implementation Plan

## Current Status

Tasks 1-3 complete.  Task 4 nearly complete:
barSimplexMap defined (computable via Fin.find),
map_id proved, barResolution structure laid out.
Remaining: barSimplexMap_comp (functoriality of
barSimplexMap w.r.t. composition).  This is equivalent
to the presentation theorem for SimplexCategory by
generators and relations — a substantial standalone
result.  Tasks 5-9 not started but do not depend on
barSimplexMap_comp.

### What exists in `GebLean/BarResolution.lean`

- `Comonad.iterateObj G X n` — `G^n(X)`, with
  `iterateObj G X 0 = X`
- `Comonad.iterateMap G f n` — functoriality in `X`
- `Comonad.barFace G X n i` — face map applying `ε`
  at depth `i` in `G^{n+2}(X) ⟶ G^{n+1}(X)`
- `Comonad.barDegen G X n i` — degeneracy map
  applying `δ` at depth `i`
- Equation lemmas: `barFace_zero`, `barFace_succ`,
  `barDegen_zero`, `barDegen_succ` (all `rfl`)
- All five simplicial identity families proved:
  `barFace_comp_barFace`, `barDegen_comp_barDegen`,
  `barDegen_comp_barFace_self`,
  `barDegen_comp_barFace_succ`,
  `barFace_comp_barDegen_lt`,
  `barFace_comp_barDegen_gt`
- SimplexCategory helpers:
  `exists_not_mem_range_of_lt`,
  `exists_flatSpot_of_gt`, `skipValue`, `mergeFlat`
- `barSimplexMap` — maps arbitrary SimplexCategory
  morphisms to bar resolution morphisms (well-founded
  recursion on `a.len + b.len`)

### Proof technique for simplicial identities

The `Fin` proof term issue requires care:

1. Use `erw` (not `rw`) with `barFace_succ` /
   `barFace_zero` to unfold `barFace` — `erw`
   handles the `Fin` proof irrelevance that `rw`
   does not.
2. For the `i = 0` base case: use
   `@Comonad.counit_naturality C _ G X Y f`
   with **all arguments explicit** — implicit
   resolution fails otherwise.
3. For the `i > 0, j > 0` inductive case: use
   `G.toFunctor.map_comp` to factor out `G.map`,
   then `congr 1` + the induction hypothesis.
4. The `n = 0` case needs both `i = 0` (ε-naturality)
   and specific small cases (e.g., `i = 1, j = 1`)
   handled by `subst_vars` + the same technique.

### Remaining simplicial identities (Task 3)

The four remaining families, following the same
proof pattern as `barFace_comp_barFace`:

1. `barDegen_comp_barDegen` — uses
   `Comonad.delta_naturality` (δ-naturality)
2. `barFace_comp_barDegen_lt` — for `i < j`, uses
   `Comonad.counit_naturality` and
   `Comonad.delta_naturality`
3. `barFace_comp_barDegen_eq` — for `i = j` or
   `i = j + 1`, uses the left/right counit laws
   (`Comonad.left_counit`, `Comonad.right_counit`)
4. `barFace_comp_barDegen_gt` — for `i > j + 1`,
   similar to case 2

### After Task 3

Task 4 assembles `Comonad.barResolution` as a
`SimplicialObject C` = `SimplexCategoryᵒᵖ ⥤ C`.
This requires defining `map` for arbitrary
`SimplexCategory` morphisms.  The Čech nerve in
mathlib (`Arrow.cechNerve`) provides a model: it
defines `map g` directly using `g.unop.toOrderHom`
to reindex, without decomposing into generators.
For the bar resolution, a similar direct definition
using the order-preserving map structure should be
possible, or alternatively, the identities proved in
Task 3 can be used to verify the functor laws after
defining `map` via generator factorization.

Tasks 5-9 build the copresheaf cover comonad and
apply the generic bar resolution.

> **For agentic workers:** Use
> superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Build a generic comonad bar resolution as a
simplicial object, then instantiate it for the
copresheaf cover comonad to obtain a simplicial
resolution of any copresheaf by coproducts of
representables.

**Architecture:** Define a generic
`Comonad.barResolution` that constructs a
`SimplicialObject C` from any `Comonad C` and object
`X : C`.  Then package the copresheaf cover as a
`Comonad` on `C ⥤ Type (max u w v)` and apply the
generic construction.  The copresheaf side is done
first; the presheaf side follows by the same pattern.

**Tech Stack:** Lean 4, mathlib (`Comonad`,
`SimplicialObject`, `SimplexCategory`)

---

## File Structure

- **Create:** `GebLean/BarResolution.lean` — generic
  `Comonad.barResolution` (independent of presheaves)
- **Create:** `GebLean/CopresheafCoverComonad.lean` —
  the copresheaf cover comonad and its bar resolution
- **Modify:** `GebLean.lean` — add imports for new files

The generic bar resolution is separated from the
copresheaf-specific code so it can be reused (and
potentially contributed to mathlib).

## Background

### Comonad bar resolution

For a comonad `G : Comonad C` and object `X : C`,
the bar resolution `B_•(G, X)` is a simplicial object:

- `B_n = G^{n+1}(X)` — the `(n+1)`-fold application
  of the underlying endofunctor
- Face maps `d_i : B_n → B_{n-1}` apply the counit
  `ε` at position `i`:
  `d_i = G^i(ε_{G^{n-i}(X)})`
- Degeneracy maps `s_i : B_n → B_{n+1}` apply the
  comultiplication `δ` at position `i`:
  `s_i = G^i(δ_{G^{n-i}(X)})`

The simplicial identities follow from the comonad
laws (coassociativity, left/right counit).

### The copresheaf cover comonad

The endofunctor `G` on `C ⥤ Type (max u w v)` sends
a copresheaf `F` to `copresheafCover F` (defined in
`PolyCover.lean` as `ccrToFunctor (copresheafCoverObj F)`).

- **Counit** `ε_F : G(F) → F`: sends `(j, f)` to
  `F.map f j.2` — the existing `copresheafCoverMap`
  composed with the ULift isomorphism.
- **Comultiplication** `δ_F : G(F) → G(G(F))`: sends
  `(j, f) ∈ G(F)(Y)` to
  `(elementsMk G(F) Y (j, f), 𝟙 Y) ∈ G(G(F))(Y)` —
  the tautological embedding using the identity
  morphism.

## Tasks

### Task 1: Generic iterated comonad application

**Files:**

- Create: `GebLean/BarResolution.lean`

Define `G^{n+1}(X)` for a comonad `G` and object `X`.

- [ ] **Step 1:** Create `GebLean/BarResolution.lean`
  with imports for `Mathlib.CategoryTheory.Monad.Basic`
  and `Mathlib.AlgebraicTopology.SimplicialObject.Basic`.
  Define `Comonad.iterateObj (G : Comonad C) (X : C) (n : ℕ) : C`
  by recursion: `iterateObj G X 0 = G.toFunctor.obj X`,
  `iterateObj G X (n+1) = G.toFunctor.obj (iterateObj G X n)`.
  This gives `G^{n+1}(X)`.

- [ ] **Step 2:** Run `lake build GebLean.BarResolution`.
  Fix any issues.

- [ ] **Step 3:** Define `Comonad.iterateMap`
  sending `(f : X ⟶ Y)` and `(n : ℕ)` to a morphism
  `iterateObj G X n ⟶ iterateObj G Y n`,
  by recursion: apply `G.map` to the previous level.
  This gives functoriality of `G^{n+1}` in `X`.

- [ ] **Step 4:** Build and fix.

### Task 2: Face and degeneracy maps

**Files:**

- Modify: `GebLean/BarResolution.lean`

Define the face map `d_i` (applying `ε` at position
`i`) and degeneracy map `s_i` (applying `δ` at
position `i`).

- [ ] **Step 1:** Define `Comonad.barFace` taking
  `(n : ℕ)` and `(i : Fin (n + 2))` and returning
  `iterateObj G X (n+1) ⟶ iterateObj G X n`.
  This applies `ε` at depth `i`: for `i = 0`, use
  `ε` at the outermost level; for `i > 0`, apply
  `G.map` to the face map at depth `i - 1`.

  Recursive definition:
  - `barFace G X n 0 = ε.app (iterateObj G X n)`
  - `barFace G X (n+1) (i+1) = G.map (barFace G X n i)`

  (The second case uses `Fin.succ` / `Fin.castSucc`
  to handle the index arithmetic.)

- [ ] **Step 2:** Build and fix.

- [ ] **Step 3:** Define `Comonad.barDegen` taking
  `(n : ℕ)` and `(i : Fin (n + 1))` and returning
  `iterateObj G X n ⟶ iterateObj G X (n+1)`.
  This applies `δ` at depth `i`, with the same
  recursive structure as `barFace` but using `δ`
  instead of `ε`.

- [ ] **Step 4:** Build and fix.

### Task 3: Simplicial identities from comonad laws

**Files:**

- Modify: `GebLean/BarResolution.lean`

Prove the five families of simplicial identities:
`d_i ∘ d_j = d_{j-1} ∘ d_i` (for `i < j`),
`s_i ∘ s_j = s_{j+1} ∘ s_i` (for `i ≤ j`),
and the three mixed `d_i ∘ s_j` identities.

These follow from:

- `d_i ∘ d_j`: counit naturality
- `s_i ∘ s_j`: comultiplication naturality
- `d_i ∘ s_j` (mixed): counit-comultiplication
  interaction (left counit, right counit, or
  naturality depending on the case)

Strategy: use the factoring-out-lemmas technique.
Prove each identity by induction on the depth,
reducing to the comonad laws at the base case.
The inductive step uses `G.map` to push inside.

- [ ] **Step 1:** Prove `barFace_comp_barFace`:
  the composition `barFace (n+1) i.castSucc` then
  `barFace n j` equals `barFace (n+1) j.succ` then
  `barFace n i`, for `i ≤ j`.
  Start with an underscore
  implementation, identify the goal, factor into
  helper lemmas if needed.

- [ ] **Step 2:** Build and fix.

- [ ] **Step 3:** Prove the remaining four families
  of simplicial identities, one at a time, building
  after each.

- [ ] **Step 4:** Build and verify no warnings.

### Task 4: Assemble the simplicial object

**Files:**

- Modify: `GebLean/BarResolution.lean`

Define `Comonad.barResolution (G : Comonad C) (X : C) : SimplicialObject C`.

A `SimplicialObject C` is `SimplexCategoryᵒᵖ ⥤ C`.
Construct it by defining the functor:

- On objects: `[n] ↦ iterateObj G X n`
- On morphisms: decompose into compositions of
  `δ_i` and `σ_i` (the generators of
  `SimplexCategory`) and apply the corresponding
  `barFace`/`barDegen` maps.

Alternative approach (possibly cleaner): use
`SimplicialObject.mk'` or construct via the
`δ`/`σ` interface if mathlib provides a constructor
that takes face and degeneracy maps plus simplicial
identities.  Check whether
`CategoryTheory.SimplicialObject.mk` or similar
exists.

If no such constructor exists, define the functor
directly by induction on morphisms in
`SimplexCategory`, using that every morphism factors
as a composition of face and degeneracy maps.

- [ ] **Step 1:** Check mathlib for a `SimplicialObject`
  constructor that takes face/degeneracy maps and
  identities.  If none exists, plan the direct
  functor construction.

- [ ] **Step 2:** Define
  `Comonad.barResolution (G : Comonad C) (X : C) : SimplicialObject C`
  using the face and degeneracy maps from Task 2 and
  the identities from Task 3.

- [ ] **Step 3:** Build and fix.

- [ ] **Step 4:** Add `GebLean.BarResolution` to
  `GebLean.lean` imports.  Run `lake build` and
  `lake test`.

### Task 5: Copresheaf cover endofunctor

**Files:**

- Create: `GebLean/CopresheafCoverComonad.lean`

Define the copresheaf cover as a `Functor` on
`C ⥤ Type (max u w v)`.

- [ ] **Step 1:** Create the file with imports for
  `GebLean.PolyCover` and
  `Mathlib.CategoryTheory.Monad.Basic`.

- [ ] **Step 2:** Define
  `copresheafCoverFunctor : (C ⥤ Type (max u w v)) ⥤ (C ⥤ Type (max u w v))`
  with:
  - `obj F = copresheafCover F` (where `copresheafCover`
    uses `w := max u w` so the input and output are in
    the same universe)
  - `map α = ...` (given `α : F ⟶ G`, define the
    induced map `copresheafCover F ⟶ copresheafCover G`
    by transporting elements along `α`)

  The action on morphisms sends `(j, f) ∈ G_F(Y)` to
  `(α_*(j), f) ∈ G_G(Y)` where `α_*` maps elements of
  `F` to elements of `G` via the category-of-elements
  functoriality.

- [ ] **Step 3:** Build and fix.

- [ ] **Step 4:** Prove `map_id` and `map_comp` for
  the functor.  Build and fix.

### Task 6: Counit natural transformation

**Files:**

- Modify: `GebLean/CopresheafCoverComonad.lean`

Define `copresheafCoverCounit : copresheafCoverFunctor ⟶ 𝟭 _`.

- [ ] **Step 1:** Define the natural transformation.
  At each `F`, the component is
  `copresheafCoverMap F ≫ (uliftCopresheafIso F).hom`
  (composing the cover map with the ULift removal).

  Naturality: for `α : F ⟶ G`, show
  `copresheafCoverFunctor.map α ≫ ε_G = ε_F ≫ α`.

- [ ] **Step 2:** Build and fix.

### Task 7: Comultiplication natural transformation

**Files:**

- Modify: `GebLean/CopresheafCoverComonad.lean`

Define `copresheafCoverComult`, a natural
transformation from `copresheafCoverFunctor` to
`copresheafCoverFunctor ⋙ copresheafCoverFunctor`.

- [ ] **Step 1:** Define the comultiplication.
  At each `F` and each `Y : C`, the component sends
  `(j, f) ∈ copresheafCover F |>.obj Y` to
  `(k, 𝟙 Y) ∈ copresheafCover (copresheafCover F) |>.obj Y`
  where `k = Functor.elementsMk (copresheafCover F) Y (j, f)`.

  This is the tautological embedding: each element of
  `G(F)` at `Y` becomes an element of `G(G(F))` at `Y`
  via the identity morphism.

- [ ] **Step 2:** Prove naturality in `Y` (the inner
  naturality for the natural transformation at each `F`).

- [ ] **Step 3:** Prove naturality in `F` (the outer
  naturality of the natural transformation).

- [ ] **Step 4:** Build and fix.

### Task 8: Comonad laws

**Files:**

- Modify: `GebLean/CopresheafCoverComonad.lean`

Prove the three comonad laws and assemble the
`Comonad` instance.

- [ ] **Step 1:** Prove `left_counit`:
  `δ_F ≫ ε_{G(F)} = 𝟙`.
  At `Y`, this says: `(j, f)` maps via `δ` to
  `(k, 𝟙)`, then via `ε` the identity morphism
  sends `k` back to `(j, f)`.

- [ ] **Step 2:** Prove `right_counit`:
  `δ_F ≫ G(ε_F) = 𝟙`.
  At `Y`, this says: `(j, f)` maps via `δ` to
  `(k, 𝟙)`, then `G(ε)` applies `ε` inside,
  recovering `(j, f)`.

- [ ] **Step 3:** Prove `coassoc`:
  `δ_F ≫ G(δ_F) = δ_F ≫ δ_{G(F)}`.
  Both sides send `(j, f)` to the same doubly-
  tautological embedding in `G(G(G(F)))`.

- [ ] **Step 4:** Assemble
  `copresheafCoverComonad : Comonad (C ⥤ Type (max u w v))`.

- [ ] **Step 5:** Build and fix.  Run `lake test`.

### Task 9: Instantiate the bar resolution

**Files:**

- Modify: `GebLean/CopresheafCoverComonad.lean`

Apply `Comonad.barResolution` to the copresheaf
cover comonad.

- [ ] **Step 1:** Define `copresheafBarResolution`
  taking `F : C ⥤ Type (max u w v)` and returning a
  `SimplicialObject (C ⥤ Type (max u w v))`, defined
  as `Comonad.barResolution copresheafCoverComonad F`.

- [ ] **Step 2:** Add
  `GebLean.CopresheafCoverComonad` to `GebLean.lean`.
  Run `lake build` and `lake test`.

- [ ] **Step 3:** Verify that level 0 of the bar
  resolution is `copresheafCover F` (the projective
  cover) and that the augmentation map (face map
  `d_0` at level 0) recovers the cover map.

## Notes

- The simplicial identities (Task 3) are the most
  proof-intensive part.  Use the factoring-out-lemmas
  technique from CLAUDE.md if proofs grow long.
- Universe management: work in
  `C ⥤ Type (max u w v)` throughout the comonad
  construction.  The `presheafCover`/`copresheafCover`
  functions from `PolyCover.lean` cross universe
  boundaries, but within `Type (max u w v)` the
  iteration stabilizes.
- The generic `Comonad.barResolution` (Tasks 1-4)
  has no universe complications — it works for any
  `Comonad C`.
- Write one definition at a time, building after each,
  per CLAUDE.md guidelines.
